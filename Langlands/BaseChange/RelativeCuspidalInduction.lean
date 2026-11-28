import Langlands.BaseChange.TwistedLeviParabolic
import Langlands.Group.GL.RefinementCoordinates
import Langlands.Representation.Geometric.ParabolicOrbitInductionTransport
import Langlands.Group.GL.ReindexCongr
import Langlands.Representation.Classification.FineTwistRegularityProof

/-! # Normalization of relative induction from cuspidal data -/

noncomputable section

namespace Langlands.BaseChange.TwistedLeviPaleyWiener

open GeneralLinear Geometric Parabolic

universe v z

section Coordinates

variable (E : Type v) [Field E] {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

private theorem composedParabolic_flatten :
    composedParabolic E B S = (B.flatten S).parabolic E :=
  (B.flatten S).composedParabolic_eq_of_coordinates B S (B.flattenBlockEquiv S)
    (fun a => (B.flatten_size_flattenBlockEquiv S a).symm) E
    (fun i j x => B.index_index_eq_flatten S ⟨i, j⟩ x)

private theorem leviRefinementEquiv_flatten (m : (B.flatten S).Levi E) :
    (B.flatten S).leviRefinementEquiv B S (B.flattenBlockEquiv S)
      (fun a => (B.flatten_size_flattenBlockEquiv S a).symm) E m =
      flattenedLeviEquiv E B S m := by
  apply Subtype.ext
  apply B.leviEmbedding_injective E
  rw [(B.flatten S).leviEmbedding_leviRefinementEquiv B S (B.flattenBlockEquiv S)
    (fun a => (B.flatten_size_flattenBlockEquiv S a).symm) E
    (fun i j x => B.index_index_eq_flatten S ⟨i, j⟩ x), flattenedLeviEquiv_embedding]

/-- The relative parabolic attached to the flattened refinement is the product
of the parabolics in the individual blocks of the coarse Levi. -/
theorem relParabolic_eq_refinedParabolic :
    relParabolic E B (B.flatten S) = refinedParabolic E B S := by
  ext g
  rw [mem_relParabolic, ← composedParabolic_flatten, composedParabolic, mem_leviPreimage_iff]
  constructor
  · rintro ⟨_, hg⟩
    exact (B.leviProjection_section E g) ▸ hg
  · intro hg
    exact ⟨(B.leviInParabolic E g).property, (B.leviProjection_section E g).symm ▸ hg⟩

/-- The two projections extract the same fine diagonal blocks. -/
theorem relProjection_flattenedLeviEquiv (q : relParabolic E B (B.flatten S)) :
    flattenedLeviEquiv E B S (relProjection E B (B.flatten S) q) =
      refinedLeviProjection E B S
        (MulEquiv.subgroupCongr (relParabolic_eq_refinedParabolic E B S) q) := by
  let C := B.flatten S
  let qC := relEmbedding E B C q
  let eP := C.parabolicRefinementEquiv B S (B.flattenBlockEquiv S)
    (fun a => (B.flatten_size_flattenBlockEquiv S a).symm) E
    (fun i j x => B.index_index_eq_flatten S ⟨i, j⟩ x)
  have he := C.composedLeviProjection_parabolicRefinementEquiv B S (B.flattenBlockEquiv S)
    (fun a => (B.flatten_size_flattenBlockEquiv S a).symm) E
    (fun i j x => B.index_index_eq_flatten S ⟨i, j⟩ x) qC
  rw [leviRefinementEquiv_flatten] at he
  have hq : preimageProjection E B (refinedParabolic E B S) (eP qC) =
      MulEquiv.subgroupCongr (relParabolic_eq_refinedParabolic E B S) q := by
    apply Subtype.ext
    exact B.leviProjection_section E q.val
  change refinedLeviProjection E B S (preimageProjection E B (refinedParabolic E B S)
    (eP qC)) = flattenedLeviEquiv E B S (relProjection E B C q) at he
  exact he.symm.trans (congrArg (refinedLeviProjection E B S) hq)

end Coordinates

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{v} p} (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The positive half of the relative modulus in the flattened Levi coordinates. -/
def relativeLeviHalfModulus : (B.flatten S).Levi F.Carrier →* ℂˣ :=
  (T.refinedLeviHalfModulus B S).comp (flattenedLeviEquiv F.Carrier B S).toMonoidHom

theorem isOpen_ker_relativeLeviHalfModulus :
    let := T.topology
    IsOpen ((relativeLeviHalfModulus T B S).ker : Set ((B.flatten S).Levi F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (T.isOpen_ker_refinedLeviHalfModulus B S).preimage
    (flattenedLeviEquivContinuous F.Carrier B S).continuous

private theorem determinant_reindex_finCongr {a b : ℕ} (h : a = b)
    (g : GeneralLinear a F.Carrier) :
    determinant (reindex (finCongr h) g) = determinant g := by
  subst b
  rw [RankinSelberg.reindex_finCongr_self]

/-- The half modulus is trivial on every refined unipotent radical of the
flattened Levi. -/
theorem refinedUnipotent_le_ker_relativeLeviHalfModulus
    (R : BlockRefinement (B.flatten S)) :
    refinedUnipotent F.Carrier (B.flatten S) R ≤ (relativeLeviHalfModulus T B S).ker := by
  intro m hm
  change flattenedLeviEquiv F.Carrier B S m ∈ (T.refinedLeviHalfModulus B S).ker
  rw [T.refinedLeviHalfModulus_ker]
  change T.refinedLeviModulus B S (flattenedLeviEquiv F.Carrier B S m) = 1
  rw [T.refinedLeviModulus_apply]
  apply Finset.prod_eq_one
  intro i _
  have hd (j : Fin (S i).length) :
      T.determinantNorm ((S i).size j)
        (PadicField.TopologicalData.refinedLeviBlock B S i
          (flattenedLeviEquiv F.Carrier B S m) j) = 1 := by
    change T.determinantNorm ((S i).size j)
      ((refinedLeviEquiv F.Carrier B S).symm (flattenedLeviEquiv F.Carrier B S m) i j) = 1
    rw [flattenedLeviEquiv_component]
    unfold PadicField.TopologicalData.determinantNorm
    rw [MonoidHom.comp_apply, determinant_reindex_finCongr, ← map_one T.normalizedAbsUnits]
    rw [(R (B.flattenBlockEquiv S ⟨i, j⟩)).determinant_eq_one_of_mem_unipotentSubgroup
      ((mem_refinedUnipotent F.Carrier (B.flatten S) R m).mp hm _)]
  simp [T.leviModulus_apply, hd]

variable {V : Type z} [AddCommGroup V] [Module ℂ V]

/-- A positive or inverse relative half-modulus twist preserves cuspidality. -/
theorem isLeviCuspidal_relativeHalfTwist_iff
    (ρ : Representation ℂ ((B.flatten S).Levi F.Carrier) V)
    (χ : (B.flatten S).Levi F.Carrier →* ℂˣ)
    (hχ : χ.ker = (relativeLeviHalfModulus T B S).ker) :
    let := T.topology
    CuspidalSupport.IsLeviCuspidal (B.flatten S) (twist χ ρ) ↔
      CuspidalSupport.IsLeviCuspidal (B.flatten S) ρ := by
  let := T.topology
  refine and_congr (isAdmissible_twist_iff χ ρ
    (hχ.symm ▸ isOpen_ker_relativeLeviHalfModulus T B S)) ?_
  unfold CuspidalSupport.IsLeviQuasicuspidal
  exact forall_congr' fun R => forall_congr' fun _ =>
    Jacquet.subsingleton_coinvariants_twist_iff χ ρ
      (hχ.symm ▸ refinedUnipotent_le_ker_relativeLeviHalfModulus T B S R)

/-- The relative unnormalized induction of the half-modulus twist is
equivalent to normalized refined induction of the original coefficient. -/
def relativeInductionHalfTwistEquiv
    (ρ : Representation ℂ ((B.flatten S).Levi F.Carrier) V) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    (Induction.smoothInduced (relParabolic F.Carrier B (B.flatten S))
      ((twist (relativeLeviHalfModulus T B S) ρ).comp
        (relProjection F.Carrier B (B.flatten S)))).Equiv
      (T.normalizedRefinedInduced B S
        (ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom)) := by
  letI := T.topology
  letI := T.leviTopologicalGroup B
  let e := MulEquiv.subgroupCongr (relParabolic_eq_refinedParabolic F.Carrier B S)
  let σ := refinedInducingRepresentation B S (T.refinedLeviHalfModulus B S)
    (ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom)
  have he : (twist (relativeLeviHalfModulus T B S) ρ).comp
      (relProjection F.Carrier B (B.flatten S)) = σ.comp e.toMonoidHom := by
    ext q x
    have hq := relProjection_flattenedLeviEquiv F.Carrier B S q
    change (T.refinedLeviHalfModulus B S
      (flattenedLeviEquiv F.Carrier B S (relProjection F.Carrier B (B.flatten S) q)) : ℂ) •
        ρ (relProjection F.Carrier B (B.flatten S) q) x =
      (T.refinedLeviHalfModulus B S (refinedLeviProjection F.Carrier B S (e q)) : ℂ) •
        ρ ((flattenedLeviEquiv F.Carrier B S).symm
          (refinedLeviProjection F.Carrier B S (e q))) x
    rw [← hq, MulEquiv.symm_apply_apply]
  exact (Induction.smoothInducedEquiv _ (Representation.Equiv.mk
    (LinearEquiv.refl ℂ V) fun q => by rw [he]; rfl)).trans
    (Geometric.smoothInducedSubgroupCongr _ _ (relParabolic_eq_refinedParabolic F.Carrier B S) σ)

/-- To read an unnormalized relative induction as a normalized refined one,
twist the flattened coefficient by the inverse half modulus. -/
def relativeInductionEquiv
    (ρ : Representation ℂ ((B.flatten S).Levi F.Carrier) V) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    (Induction.smoothInduced (relParabolic F.Carrier B (B.flatten S))
      (ρ.comp (relProjection F.Carrier B (B.flatten S)))).Equiv
      (T.normalizedRefinedInduced B S
        ((twist (relativeLeviHalfModulus T B S)⁻¹ ρ).comp
          (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom)) := by
  letI := T.topology
  letI := T.leviTopologicalGroup B
  let χ := relativeLeviHalfModulus T B S
  have h : twist χ (twist χ⁻¹ ρ) = ρ := by
    ext m x
    simp [twist, smul_smul]
  let e : Representation.Equiv (ρ.comp (relProjection F.Carrier B (B.flatten S)))
      ((twist χ (twist χ⁻¹ ρ)).comp (relProjection F.Carrier B (B.flatten S))) :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ V) fun q => by rw [h]; rfl
  exact (Induction.smoothInducedEquiv _ e).trans
    (relativeInductionHalfTwistEquiv T B S (twist χ⁻¹ ρ))

/-- Normalization of relative induction and preservation of cuspidality by
the change in inducing action. -/
def RelativeCuspidalInductionNormalizationStatement : Prop :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  ∀ (W : Type z) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ ((B.flatten S).Levi F.Carrier) W),
    let χ := relativeLeviHalfModulus T B S
    (CuspidalSupport.IsLeviCuspidal (B.flatten S) (twist χ⁻¹ ρ) ↔
      CuspidalSupport.IsLeviCuspidal (B.flatten S) ρ) ∧
    Nonempty ((Induction.smoothInduced (relParabolic F.Carrier B (B.flatten S))
        (ρ.comp (relProjection F.Carrier B (B.flatten S)))).Equiv
      (T.normalizedRefinedInduced B S
        ((twist χ⁻¹ ρ).comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom)))

theorem relativeCuspidalInductionNormalization :
    RelativeCuspidalInductionNormalizationStatement.{v,z} T B S := by
  let _ := T.topology
  let _ := T.leviTopologicalGroup B
  intro W _ _ ρ
  refine ⟨isLeviCuspidal_relativeHalfTwist_iff T B S ρ _ ?_,
    ⟨relativeInductionEquiv T B S ρ⟩⟩
  ext m
  simp

end Langlands.BaseChange.TwistedLeviPaleyWiener
