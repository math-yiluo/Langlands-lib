import Langlands.Representation.Exponents.CoarseFineTwistScalarCharacterStatement
import Langlands.Representation.Exponents.UnitaryFineTwistScalarCharacterProof
import Langlands.Representation.Exponents.PositiveRootBlockSumsProof
import Langlands.Representation.Classification.MaximalConeLifting

/-! Proof of the coarse scalar character of a nested fine determinant twist. -/

noncomputable section

namespace Langlands.Exponents

open GeneralLinear Geometric RelativeJacquetMultiplicity RelativeRegularComparison
open scoped BigOperators

universe uF uV

private theorem transport_properties
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    {n : ℕ} {C C' : BlockShape n} (h : C = C')
    (ω : Rep.{uV} ℂ (C.Levi F.Carrier))
    (P : ∀ C : BlockShape n, Rep.{uV} ℂ (C.Levi F.Carrier) → Prop)
    (hP : P C ω) :
    P C' (h ▸ ω) := by
  subst C'
  exact hP

/-- The actual nested fine twist has the size-weighted coarse scalar character. -/
theorem coarseFineTwistScalarCharacter :
    CoarseFineTwistScalarCharacterStatement.{uF,uV} := by
  classical
  dsimp only [CoarseFineTwistScalarCharacterStatement]
  intro p _ F T
  let := T.topology
  intro n B Q R S h ω hi ha hu v₀ hv
  let ωB : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier) := h ▸ ω
  let vB : Fin (B.flatten S).length → ℝ := h ▸ v₀
  obtain ⟨hiB, haB, huB⟩ := transport_properties h ω
    (fun _ A => Representation.IsIrreducible A.ρ ∧
      IsAdmissible A.ρ ∧ IsUnitarizable A.ρ) ⟨hi, ha, hu⟩
  intro t
  let v' : Fin (B.flatten S).length → ℝ :=
    fun k => vB k - t (B.flattenOuter S k)
  obtain ⟨χf, hχf, hscalar, hreal⟩ :=
    unitaryFineTwistScalarCharacter p F T n B S ωB hiB haB huB v'
  have heff :
      (fun k => -v' k + (0 : Fin B.length → ℝ) ((B.flattenBlockEquiv S).symm k).1) =
        (fun k => -vB k + t ((B.flattenBlockEquiv S).symm k).1) := by
    funext k
    dsimp only [v', BlockShape.flattenOuter, Pi.zero_apply]
    ring
  have htwist : fineTwist T B S ωB v' 0 = fineTwist T B S ωB vB t := by
    unfold fineTwist
    rw [heff]
  rw [htwist] at hscalar
  let repeatCoords : (Fin B.length → F.Carrierˣ) →*
      (Fin (B.flatten S).length → F.Carrierˣ) :=
    { toFun := fun a => a ∘ B.flattenOuter S
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let χ : (Fin B.length → F.Carrierˣ) →* ℂˣ := χf.comp repeatCoords
  have hopen : IsOpen (χ.ker : Set (Fin B.length → F.Carrierˣ)) := by
    change IsOpen ((fun a : Fin B.length → F.Carrierˣ => a ∘ B.flattenOuter S) ⁻¹'
      (χf.ker : Set (Fin (B.flatten S).length → F.Carrierˣ)))
    exact hχf.preimage (continuous_pi fun k => continuous_apply (B.flattenOuter S k))
  have hsum (i : Fin B.length) :
      ∑ k : Fin (S i).length,
        ((S i).size k : ℝ) * vB (B.flattenBlockEquiv S ⟨i, k⟩) = 0 := by
    have hs := positiveRootBlockSums.2.2 n B Q R S h v₀ hv i
    rw [← (S i).indexEquiv.sum_comp, Fintype.sum_sigma] at hs
    change (∑ k : Fin (S i).length, ∑ b : Fin ((S i).size k),
      vB (blockIndex (B.flatten S) (B.index i ((S i).index k b)))) = 0 at hs
    have hblock (k : Fin (S i).length) (b : Fin ((S i).size k)) :
        blockIndex (B.flatten S) (B.index i ((S i).index k b)) =
          B.flattenBlockEquiv S ⟨i, k⟩ := by
      rw [B.index_index_eq_flatten S ⟨i, k⟩ b, blockIndex_index]
    simp_rw [hblock] at hs
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using hs
  refine ⟨χ, hopen, ?_, ?_⟩
  · intro a w
    exact hscalar (repeatCoords a) w
  · refine T.isRealPartOf_coarsen (q := B.flattenOuter S) hreal
      (χC := χ) (fun _ => rfl) _ ?_
    intro i
    rw [B.sum_filter_flattenOuter S]
    simp only [BlockShape.flatten_size_flattenBlockEquiv]
    dsimp only [v']
    simp only [BlockShape.flattenOuter_flattenBlockEquiv, mul_sub, neg_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, sub_zero]
    have hsize : (∑ k : Fin (S i).length, ((S i).size k : ℝ)) = (B.size i : ℝ) := by
      exact_mod_cast (S i).sum_eq
    rw [hsize]

end Langlands.Exponents
