import Langlands.Representation.Exponents.RefinedOppositeConeReversal
import Langlands.Representation.Parabolic.RefinementReversal
import Langlands.Representation.Parabolic.OppositeRefinementFunctors
import Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof

/-! Full normalized refined-Levi reversal, with an actual quotient-class map. -/

noncomputable section

namespace Langlands.RefinedOppositeReversal

open GeneralLinear Geometric Parabolic
open ProductLeviDualOpposite OppositeCuspidalJacquetFiltration
open scoped BigOperators NNReal

universe uF uV uW

section Groups

variable {R : Type uF} [CommRing R] {n : ℕ}
  (B : BlockShape n) (S : BlockRefinement B)

/-- Relabel every inner Levi by reversing its inner blocks. -/
def refinedLeviReverseEquiv :
    refinedLevi R B S ≃* refinedLevi R B (reverseRefinement B S) :=
  (refinedLeviEquiv R B S).symm.trans
    ((MulEquiv.piCongrRight fun i => leviReverseEquiv (S i)).trans
      (refinedLeviEquiv R B (reverseRefinement B S)))

/-- Conjugation by the actual blockwise reversal recovers the original
refined-Levi element from its reversed-label image. -/
theorem reverseWeyl_mul_refinedLeviReverseEquiv
    (m : refinedLevi R B S) :
    reverseWeyl B S R * (refinedLeviReverseEquiv B S m).val *
        (reverseWeyl B S R)⁻¹ = m.val := by
  funext i
  change (S i).reverseMatrix R *
      (S i).reverse.leviEmbedding R
        (leviReverseEquiv (S i) ((refinedLeviEquiv R B S).symm m i)) *
      ((S i).reverseMatrix R)⁻¹ = m.val i
  rw [reverseMatrix_mul_leviEmbedding]
  exact congrArg (fun z : refinedLevi R B S => z.val i)
    ((refinedLeviEquiv R B S).apply_symm_apply m)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (B.Levi R) V)

set_option maxHeartbeats 1200000 in
/-- On actual coinvariant classes, translation by the blockwise reversal
identifies the reversed upper quotient with the original lower quotient. -/
def refinedReverseCoinvariantsEquiv :
    RefinedJacquetModule B (reverseRefinement B S) ρ ≃ₗ[ℂ]
      RefinedOppositeJacquetModule B S ρ := by
  let q := reverseWeyl B S R
  let U := refinedUnipotent R B (reverseRefinement B S)
  let N := refinedOppositeUnipotent R B S
  let f : Jacquet.Coinvariants ρ U →ₗ[ℂ] Jacquet.Coinvariants ρ N :=
    Jacquet.lift ρ U ((Jacquet.mk ρ N).comp (ρ q)) (by
      intro u
      apply LinearMap.ext
      intro v
      have hu : q * (u : B.Levi R) * q⁻¹ ∈ N :=
        (Exponents.RefinedOppositeConeReversal.conj_mem_refinedOppositeUnipotent_iff B S R
          (u : B.Levi R)).mpr u.property
      have h := Jacquet.mk_apply_subgroup ρ N ⟨_, hu⟩ (ρ q v)
      change Jacquet.mk ρ N (ρ q (ρ u v)) = Jacquet.mk ρ N (ρ q v)
      rw [← h]
      change _ = Jacquet.mk ρ N (ρ (q * (u : B.Levi R) * q⁻¹) (ρ q v))
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        Representation.inv_self_apply])
  let b : Jacquet.Coinvariants ρ N →ₗ[ℂ] Jacquet.Coinvariants ρ U :=
    Jacquet.lift ρ N ((Jacquet.mk ρ U).comp (ρ q⁻¹)) (by
      intro u
      apply LinearMap.ext
      intro v
      have hu : q⁻¹ * (u : B.Levi R) * q ∈ U := by
        apply (Exponents.RefinedOppositeConeReversal.conj_mem_refinedOppositeUnipotent_iff B S R
          (q⁻¹ * (u : B.Levi R) * q)).mp
        change q * (q⁻¹ * (u : B.Levi R) * q) * q⁻¹ ∈ N
        simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using u.property
      have h := Jacquet.mk_apply_subgroup ρ U ⟨_, hu⟩ (ρ q⁻¹ v)
      change Jacquet.mk ρ U (ρ q⁻¹ (ρ u v)) = Jacquet.mk ρ U (ρ q⁻¹ v)
      rw [← h]
      change _ = Jacquet.mk ρ U (ρ (q⁻¹ * (u : B.Levi R) * q) (ρ q⁻¹ v))
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        Representation.self_inv_apply])
  exact
    { f with
      invFun := b
      left_inv := by
        intro x
        obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ U x
        change Jacquet.mk ρ U (ρ q⁻¹ (ρ q v)) = Jacquet.mk ρ U v
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      right_inv := by
        intro x
        obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N x
        change Jacquet.mk ρ N (ρ q (ρ q⁻¹ v)) = Jacquet.mk ρ N v
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] }

@[simp]
theorem refinedReverseCoinvariantsEquiv_mk (v : V) :
    refinedReverseCoinvariantsEquiv B S ρ
      (refinedJacquetMk B (reverseRefinement B S) ρ v) =
        refinedOppositeJacquetMk B S ρ (ρ (reverseWeyl B S R) v) := rfl

end Groups

section Normalized

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The actual inner coordinate maps agree with the reversed product labels. -/
theorem refinedLeviBlock_reverse (m : refinedLevi F.Carrier B S)
    (i : Fin B.length) :
    PadicField.TopologicalData.refinedLeviBlock B (reverseRefinement B S) i
        (refinedLeviReverseEquiv B S m) =
      leviReverseEquiv (S i)
        (PadicField.TopologicalData.refinedLeviBlock B S i m) := by
  change ((refinedLeviEquiv F.Carrier B (fun j => (S j).reverse)).symm
    ((refinedLeviEquiv F.Carrier B (fun j => (S j).reverse))
      (fun j => leviReverseEquiv (S j)
        ((refinedLeviEquiv F.Carrier B S).symm m j)))) i = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The full refined modulus inverts under the complete inner-Levi relabelling. -/
theorem refinedLeviModulus_reverse (m : refinedLevi F.Carrier B S) :
    T.refinedLeviModulus B (reverseRefinement B S) (refinedLeviReverseEquiv B S m) =
      (T.refinedLeviModulus B S m)⁻¹ := by
  rw [T.refinedLeviModulus_apply, T.refinedLeviModulus_apply, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [refinedLeviBlock_reverse]
  change T.leviModulus (S i).reverse
      (fun j => PadicField.TopologicalData.refinedLeviBlock B S i m j.rev) = _
  exact T.leviModulus_reverse (S i) _

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (B.Levi F.Carrier) V)

/-- An actual equivalence for the entire refined-Levi action, including the
normalization: the reversed upper quotient pulled back by inner block
relabelling is the original opposite quotient. -/
def normalizedRefinedOppositeReverseEquiv :
    Representation.Equiv
      ((T.normalizedRefinedJacquet B (reverseRefinement B S) ρ).comp
        (refinedLeviReverseEquiv B S).toMonoidHom)
      (T.normalizedRefinedOppositeJacquet B S ρ) :=
  Representation.Equiv.mk (refinedReverseCoinvariantsEquiv B S ρ) (fun m => by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ
      (refinedUnipotent F.Carrier B (reverseRefinement B S)) x
    change refinedReverseCoinvariantsEquiv B S ρ
        (T.normalizedRefinedJacquet B (reverseRefinement B S) ρ
          (refinedLeviReverseEquiv B S m)
          (refinedJacquetMk B (reverseRefinement B S) ρ v)) =
      T.normalizedRefinedOppositeJacquet B S ρ m
        (refinedReverseCoinvariantsEquiv B S ρ
          (refinedJacquetMk B (reverseRefinement B S) ρ v))
    rw [T.normalizedRefinedJacquet_mk, map_smul, refinedReverseCoinvariantsEquiv_mk,
      refinedReverseCoinvariantsEquiv_mk, T.normalizedRefinedOppositeJacquet_mk,
      T.refinedLeviInverseHalfModulus_apply, refinedLeviModulus_reverse]
    have hscalar :
        (((NNReal.sqrt ((T.refinedLeviModulus B S m)⁻¹ : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ)⁻¹ =
          (T.refinedLeviHalfModulus B S m : ℂ) := by
      rw [T.refinedLeviHalfModulus_apply]
      simp only [Units.val_inv_eq_inv_val, NNReal.sqrt_inv, NNReal.coe_inv,
        Complex.ofReal_inv, inv_inv]
    rw [hscalar]
    congr 1
    change Jacquet.mk ρ _ (ρ (reverseWeyl B S F.Carrier)
        (ρ (refinedLeviReverseEquiv B S m).val v)) =
      Jacquet.mk ρ _ (ρ m.val (ρ (reverseWeyl B S F.Carrier) v))
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    have hm := reverseWeyl_mul_refinedLeviReverseEquiv B S m
    exact congrArg ρ (mul_inv_eq_iff_eq_mul.mp hm))

@[simp]
theorem normalizedRefinedOppositeReverseEquiv_mk (v : V) :
    normalizedRefinedOppositeReverseEquiv T B S ρ
      (refinedJacquetMk B (reverseRefinement B S) ρ v) =
        refinedOppositeJacquetMk B S ρ (ρ (reverseWeyl B S F.Carrier) v) := rfl

end Normalized

end Langlands.RefinedOppositeReversal
