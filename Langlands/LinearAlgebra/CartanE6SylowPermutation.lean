import Langlands.LinearAlgebra.CartanE6AutomorphismOrder
import Langlands.LinearAlgebra.CartanE6FiveCycle
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Dual.Basis

/-! # A prime-to-five permutation subgroup for an E6 datum -/

noncomputable section

universe u

open scoped Pointwise

namespace Langlands.CartanE6Root

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) (b : P.Base) (e : b.support ≃ Fin 6)

/-- For a finite group acting on a simply connected E6 root datum, the weight
basis can be chosen to be permuted by a subgroup of index dividing `2^13 * 3^8`. -/
def TypeE6PermutationSubgroupStatement [Finite J] : Prop :=
  (∀ i j : b.support, P.pairing i.val j.val = CartanMatrix.E 6 (e i) (e j)) →
  P.corootSpan ℤ = ⊤ →
  ∀ (Γ : Type u) [Group Γ] [Finite Γ] (ρ : Γ →* P.Aut),
    ∃ H : Subgroup Γ, H.index ∣ 2 ^ 13 * 3 ^ 8 ∧
      ∃ C : Module.Basis (Fin 6) ℤ X, ∀ g ∈ H, ∀ i,
        ∃ j, (ρ g).weightEquiv (C i) = C j

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1200 in
theorem typeE6PermutationSubgroup [Finite J] : TypeE6PermutationSubgroupStatement P b e := by
  classical
  intro hCartan hSpan Γ _ _ ρ
  let : Finite P.Aut := finite_aut_of_coroot_span P b hSpan
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hcard := typeE6AutomorphismOrder P b e hCartan hSpan
  let w := fiveCycleWeyl P b e
  obtain ⟨hw, B, hB⟩ := typeE6FiveCycle P b e hCartan hSpan
  let C := B.dualBasis.map P.toPerfPair.symm
  have hC (i : Fin 6) : w.weightEquiv (C i) = C (fiveCycle.symm i) := by
    apply P.toPerfPair.injective
    apply B.ext
    intro j
    change P.toLinearMap (w.weightEquiv (C i)) (B j) = P.toLinearMap (C (fiveCycle.symm i)) (B j)
    rw [w.toLinearMap_weightEquiv, hB]
    have hDual (i j : Fin 6) : P.toLinearMap (C i) (B j) = B.dualBasis i (B j) := by
      change P.toPerfPair (P.toPerfPair.symm (B.dualBasis i)) (B j) = _
      rw [LinearEquiv.apply_symm_apply]
    rw [hDual, hDual, B.dualBasis_apply_self, B.dualBasis_apply_self]
    simp only [fiveCycle.eq_symm_apply]
  have hPow (n : ℕ) (i : Fin 6) :
      (w ^ n).weightEquiv (C i) = C ((fiveCycle.symm^[n]) i) := by
    change RootPairing.Equiv.weightHom P (w ^ n) (C i) = _
    rw [map_pow]
    induction n generalizing i with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, LinearEquiv.mul_apply, Function.iterate_succ_apply]
      change ((RootPairing.Equiv.weightHom P w) ^ n) (w.weightEquiv (C i)) = _
      rw [hC, ih]
  let W := Subgroup.zpowers w
  have hW : Nat.card W = 5 := (Nat.card_zpowers w).trans hw
  have hp : IsPGroup 5 W := IsPGroup.of_card (n := 1) (by simpa using hW)
  have hWidx : ¬ 5 ∣ W.index := by
    intro h
    have hd : 25 ∣ Nat.card P.Aut := by
      rw [← W.card_mul_index, hW]
      exact Nat.mul_dvd_mul_left 5 h
    exact (by decide : ¬ 25 ∣ 2 ^ 13 * 3 ^ 8 * 5) (hd.trans hcard)
  let P₀ : Sylow 5 P.Aut := hp.toSylow hWidx
  let Q : Sylow 5 ρ.range := Classical.choice inferInstance
  obtain ⟨R, hR⟩ := Q.exists_comap_subtype_eq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P.Aut P₀ R
  let H := (Q : Subgroup ρ.range).comap ρ.rangeRestrict
  have hidx : H.index = (Q : Subgroup ρ.range).index :=
    Subgroup.index_comap_of_surjective _ ρ.rangeRestrict_surjective
  have hdiv : H.index ∣ 2 ^ 13 * 3 ^ 8 * 5 := by
    rw [hidx]
    exact Q.toSubgroup.index_dvd_card.trans (ρ.range.card_subgroup_dvd_card.trans hcard)
  have h5 : ¬ 5 ∣ H.index := hidx ▸ Q.not_dvd_index
  have hdiv' : H.index ∣ 2 ^ 13 * 3 ^ 8 :=
    ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr h5).symm.dvd_of_dvd_mul_right hdiv
  refine ⟨H, hdiv', C.map g.weightEquiv, fun σ hσ i => ?_⟩
  have hσ' : ρ σ ∈ (R : Subgroup P.Aut) := by
    change (ρ.rangeRestrict σ : P.Aut) ∈ (R : Subgroup P.Aut)
    change ρ.rangeRestrict σ ∈ (R : Subgroup P.Aut).comap ρ.range.subtype
    rw [hR]
    exact hσ
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hσ'
  change (MulAut.conj g)⁻¹ (ρ σ) ∈ W at hσ'
  obtain ⟨n, _, hn⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hσ')
  have hσeq : ρ σ = g * w ^ n * g⁻¹ := by
    have h := congrArg (MulAut.conj g) hn
    rw [MulAut.apply_inv_self] at h
    exact h.symm
  refine ⟨(fiveCycle.symm^[n]) i, ?_⟩
  simp only [Module.Basis.map_apply, hσeq]
  change (RootPairing.Equiv.weightHom P (g * w ^ n * g⁻¹))
    ((RootPairing.Equiv.weightHom P g) (C i)) = _
  rw [map_mul, LinearEquiv.mul_apply, map_inv]
  change (RootPairing.Equiv.weightHom P (g * w ^ n))
    ((g.weightEquiv).symm (g.weightEquiv (C i))) = _
  rw [LinearEquiv.symm_apply_apply, map_mul, LinearEquiv.mul_apply]
  exact congrArg g.weightEquiv (hPow n i)

end Langlands.CartanE6Root
