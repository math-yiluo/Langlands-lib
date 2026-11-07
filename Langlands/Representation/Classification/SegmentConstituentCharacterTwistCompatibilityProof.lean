import Langlands.Representation.Classification.SegmentConstituentCompatibilityStatement
import Langlands.Representation.Classification.ConstituentCompatibilityAlgebraicProof
import Langlands.Representation.Induction.NormalizedProductCharacterTwist
import Langlands.Representation.Induction.BlockEquivalence
import Langlands.Group.GL.UpperBruhatCells

/-! # Character twists of the four segment constituent relations -/

noncomputable section

namespace Langlands

open CategoryTheory GeneralLinear

universe uF uV

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- `det (diag(a, 1, …, 1)) = a`. -/
theorem determinant_diagonalUnits_mulSingle {r : ℕ} (j : Fin r) (a : F.Carrierˣ) :
    determinant (Iwasawa.diagonalUnits (Pi.mulSingle j a) :
      GeneralLinear r F.Carrier) = a := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Iwasawa.diagonalUnits_val,
    Matrix.det_diagonal]
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.mulSingle_eq_of_ne hij]
  · simp

/-- If `χ ∘ det` has open kernel on `GL_r(F)` with `0 < r`, then `χ` has open kernel
on `F^×`: the continuous section `a ↦ diag(a, 1, …, 1)` of the determinant pulls
the kernel of `χ ∘ det` back to the kernel of `χ`. -/
theorem isOpen_ker_of_isOpen_ker_comp_determinant {r : ℕ} (hr : 0 < r)
    (χ : F.Carrierˣ →* ℂˣ)
    (h : letI := T.topology
      IsOpen ((χ.comp (determinant : GeneralLinear r F.Carrier →* F.Carrierˣ)).ker :
        Set (GeneralLinear r F.Carrier))) :
    letI := T.topology
    IsOpen (χ.ker : Set F.Carrierˣ) := by
  let := T.topology
  let s : F.Carrierˣ → GeneralLinear r F.Carrier :=
    fun a => Iwasawa.diagonalUnits (Pi.mulSingle (⟨0, hr⟩ : Fin r) a)
  have hs : Continuous s :=
    (continuous_diagonalUnits r).comp
      (continuous_mulSingle (A := fun _ : Fin r => F.Carrierˣ) (⟨0, hr⟩ : Fin r))
  have hker : (χ.ker : Set F.Carrierˣ) =
      s ⁻¹' ((χ.comp (determinant : GeneralLinear r F.Carrier →* F.Carrierˣ)).ker :
        Set (GeneralLinear r F.Carrier)) := by
    ext a
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, MonoidHom.comp_apply,
      s, determinant_diagonalUnits_mulSingle]
  rw [hker]
  exact h.preimage hs

/-- Common character twist of the actual increasing segment product. -/
def segmentInducedCharacterTwistEquiv {r : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (m : ℕ) (hr : 0 < r)
    (χ : letI := T.topology; Induction.SmoothCharacter ℂ F.Carrierˣ)
    (hχ : letI := T.topology
      IsOpen ((χ.toMonoidHom.comp
        (determinant : GeneralLinear r F.Carrier →* F.Carrierˣ)).ker :
          Set (GeneralLinear r F.Carrier))) :
    letI := T.topology
    (twist (χ.toMonoidHom.comp determinant)
      (T.segmentInduced A m hr).representation).Equiv
      (T.segmentInduced (A.twist (χ.toMonoidHom.comp determinant) hχ) m hr).representation := by
  letI := T.topology
  have e :
      (twist (χ.toMonoidHom.comp determinant)
        (T.segmentInduced A m hr).representation).Equiv
        (T.normalizedProductInduced (BlockShape.uniform m r hr)
          (fun i => twist (χ.toMonoidHom.comp determinant)
            (T.segmentFactors A m hr i).representation)) :=
    T.normalizedProductDeterminantTwistEquiv (BlockShape.uniform m r hr) χ
      (fun i => (T.segmentFactors A m hr i).representation)
  have hblocks :
      (fun i : Fin (BlockShape.uniform m r hr).length =>
        twist (χ.toMonoidHom.comp determinant)
          (T.segmentFactors A m hr i).representation) =
      (fun i => (T.segmentFactors (A.twist (χ.toMonoidHom.comp determinant) hχ) m hr
        i).representation) := by
    funext i
    change twist (χ.toMonoidHom.comp determinant)
        (twist (T.determinantPowerCharacter r (i : ℝ)) A.representation) =
      twist (T.determinantPowerCharacter r (i : ℝ))
        (twist (χ.toMonoidHom.comp determinant) A.representation)
    rw [twist_twist, twist_twist,
      mul_comm (χ.toMonoidHom.comp determinant) (T.determinantPowerCharacter r (i : ℝ))]
  have eblocks (i : Fin (BlockShape.uniform m r hr).length) :
      (twist (χ.toMonoidHom.comp determinant)
        (T.segmentFactors A m hr i).representation).Equiv
        (T.segmentFactors (A.twist (χ.toMonoidHom.comp determinant) hχ) m hr
          i).representation :=
    equivOfRepresentationEq (congrFun hblocks i)
  exact e.trans
    (T.normalizedProductInducedEquiv (BlockShape.uniform m r hr) eblocks)

end PadicField.TopologicalData

namespace Classification

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Twisting by a character of the determinant preserves and reflects all four
segment relations. -/
theorem segmentConstituentCharacterTwistCompatibility :
    SegmentConstituentCharacterTwistCompatibility.{uF, uV} F T := by
  let := T.topology
  intro Δ χ hr hd π Δχ πχ
  obtain ⟨A, hA⟩ := Quotient.exists_rep Δ.base.cls
  let χs : Induction.SmoothCharacter ℂ F.Carrierˣ :=
    ⟨χ, T.isOpen_ker_of_isOpen_ker_comp_determinant Δ.rank_pos χ hr⟩
  let Aχ := SupercuspidalRep.twist
    (χ.comp (determinant : GeneralLinear Δ.rank F.Carrier →* F.Carrierˣ)) hr
    (ker_determinant_le_ker_comp χ) A
  have hAχ : Δχ.base.IsRepresentedBy Aχ := by
    change SupercuspidalClass.twist _ _ _ A.isoClass =
      SupercuspidalClass.twist _ _ _ Δ.base.cls
    rw [show A.isoClass = Δ.base.cls from hA]
  have e := T.segmentInducedCharacterTwistEquiv A.obj Δ.length Δ.rank_pos χs hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [T.isSegmentSocle_iff Δ π A hA, T.isSegmentSocle_iff Δχ πχ Aχ hAχ]
    exact (isIrreducibleSocle_twist_iff _ _ _).symm.trans
      (isIrreducibleSocle_iff_of_equiv e)
  · rw [T.isSegmentHead_iff Δ π A hA, T.isSegmentHead_iff Δχ πχ Aχ hAχ]
    exact (isIrreducibleHead_twist_iff _ _ _).symm.trans
      (isIrreducibleHead_iff_of_equiv e)
  · rw [T.isSegmentSubrepresentation_iff Δ π A hA,
      T.isSegmentSubrepresentation_iff Δχ πχ Aχ hAχ]
    exact (isIrreducibleSubrepresentation_twist_iff _ _ _).symm.trans
      (isIrreducibleSubrepresentation_iff_of_equiv e)
  · rw [T.isSegmentQuotient_iff Δ π A hA,
      T.isSegmentQuotient_iff Δχ πχ Aχ hAχ]
    exact (isIrreducibleQuotient_twist_iff _ _ _).symm.trans
      (isIrreducibleQuotient_iff_of_equiv e)

end Classification

end Langlands
