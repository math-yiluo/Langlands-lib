import Langlands.LinearAlgebra.FiniteIntegralRankSixGroupOrder
import Langlands.LinearAlgebra.TypeE6NegationWeyl

/-! # The prime support and five-part bound for E6 root-datum automorphisms -/

noncomputable section

universe u

open scoped BigOperators Matrix

namespace Langlands.CartanE6Root

open TypeE6NegationWeyl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 3000000 in
private theorem radical_eq_span (v : Fin 6 → ZMod 3)
    (hv : ∀ i : Fin 6, (∑ j : Fin 6, (v j) * (CartanMatrix.E 6 i j : ℤ)) = 0) :
    ∃ c : ZMod 3, v = c • (fun i => (weights i : ZMod 3)) := by
  revert v
  decide

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) (b : P.Base) (e : b.support ≃ Fin 6)

include b in
/-- An automorphism is determined by its permutation of the coroots. -/
theorem finite_aut_of_coroot_span [Finite J] (hspan : P.corootSpan ℤ = ⊤) : Finite P.Aut := by
  apply Finite.of_injective (RootPairing.Equiv.indexHom P)
  intro g h hh
  apply RootPairing.Equiv.coweightHom_injective P
  apply MulOpposite.unop_injective
  apply LinearEquiv.toLinearMap_injective
  apply (IntegralWeylVector.corootBasis P b hspan).ext
  intro i
  simp only [IntegralWeylVector.corootBasis_apply]
  change g.toHom.coweightMap (P.coroot i) = h.toHom.coweightMap (P.coroot i)
  rw [RootPairing.Hom.coroot_coweightMap_apply, RootPairing.Hom.coroot_coweightMap_apply]
  exact congrArg (fun f : Equiv.Perm J => P.coroot (f.symm i)) hh

private def coweightAction : P.Aut →* (Y ≃ₗ[ℤ] Y) where
  toFun g := (g⁻¹).coweightEquiv
  map_one' := by
    rw [inv_one]
    exact congrArg MulOpposite.unop (map_one (RootPairing.Equiv.coweightHom P))
  map_mul' g h := by
    rw [mul_inv_rev]
    exact congrArg MulOpposite.unop (map_mul (RootPairing.Equiv.coweightHom P) h⁻¹ g⁻¹)

private theorem coweightAction_injective : Function.Injective (coweightAction P) := by
  intro g h hh
  apply inv_injective
  apply RootPairing.Equiv.coweightHom_injective P
  exact congrArg MulOpposite.op hh

/-- A simply connected based E6 datum has finite automorphism order
with prime support contained in 2, 3, 5 and at most a single factor of 5. -/
def TypeE6AutomorphismOrderStatement [Finite J] : Prop :=
  (∀ a c : b.support, P.pairing a.val c.val = CartanMatrix.E 6 (e a) (e c)) →
  P.corootSpan ℤ = ⊤ → Nat.card P.Aut ∣ 2 ^ 13 * 3 ^ 8 * 5

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1200 in
theorem typeE6AutomorphismOrder [Finite J] : TypeE6AutomorphismOrderStatement P b e := by
  classical
  intro hcart hspan
  let : Finite P.Aut := finite_aut_of_coroot_span P b hspan
  let B := (IntegralWeylVector.corootBasis P b hspan).reindex e
  let M := Units.mapEquiv (LinearMap.toMatrixAlgEquiv B).toMulEquiv
  let ρ := M.toMonoidHom.comp ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ Y).symm.toMonoidHom.comp
    (coweightAction P))
  have hρ : Function.Injective ρ := M.injective.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ Y).symm.injective.comp (coweightAction_injective P))
  let v : Fin 6 → ZMod 3 := fun i => (weights i : ZMod 3)
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    change (1 : ZMod 3) = 0 at h0
    exact one_ne_zero h0
  refine finiteIntegralRankSixGroupOrderWithLine P.Aut ρ hρ v hv fun g => ?_
  let y := B.equivFun.symm weights
  let z := (g⁻¹).coweightEquiv y
  have hB (i : Fin 6) : B i = P.coroot (e.symm i).val := by
    simp only [B, Module.Basis.reindex_apply, IntegralWeylVector.corootBasis_apply]
  have heval (x : X) (u : Fin 6 → ℤ) :
      (P.toLinearMap x (B.equivFun.symm u) : ZMod 3) =
        ∑ i : Fin 6, (u i : ZMod 3) * (P.toLinearMap x (P.coroot (e.symm i).val) : ZMod 3) := by
    rw [Module.Basis.equivFun_symm_apply, map_sum, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [hB, Int.cast_mul]
  have hy (a : J) : (P.toLinearMap (P.root a) y : ZMod 3) = 0 := by
    rw [heval]
    exact residue_root P b e hcart a
  have hz (a : J) : (P.toLinearMap (P.root a) z : ZMod 3) = 0 := by
    have h := DFunLike.congr_fun ((g⁻¹).toHom.weight_coweight_transpose_apply P P y) (P.root a)
    change P.toLinearMap ((g⁻¹).toHom.weightMap (P.root a)) y = P.toLinearMap (P.root a) z at h
    rw [RootPairing.Hom.root_weightMap_apply] at h
    rw [← h]
    exact hy _
  have hcoords (i : Fin 6) : ∑ j : Fin 6, (B.equivFun z j : ZMod 3) *
      (CartanMatrix.E 6 i j : ℤ) = 0 := by
    have h := heval (P.root (e.symm i).val) (B.equivFun z)
    rw [LinearEquiv.symm_apply_apply] at h
    simp only [P.root_coroot_eq_pairing, hcart, Equiv.apply_symm_apply] at h
    rw [← h]
    exact hz _
  obtain ⟨c, hc⟩ := radical_eq_span (fun i => (B.equivFun z i : ZMod 3)) hcoords
  refine ⟨c, ?_⟩
  have hmatrix : (ρ g : Matrix (Fin 6) (Fin 6) ℤ) *ᵥ weights = B.equivFun z := by
    rw [← show B.equivFun y = weights from B.equivFun.apply_symm_apply _]
    change LinearMap.toMatrix B B (g⁻¹).coweightEquiv.toLinearMap *ᵥ B.equivFun y = _
    exact LinearMap.toMatrix_mulVec_repr B B (g⁻¹).coweightEquiv.toLinearMap y
  funext i
  exact ((Int.castRingHom (ZMod 3)).map_mulVec (ρ g : Matrix (Fin 6) (Fin 6) ℤ) weights i).symm.trans
    ((congrArg (fun w : Fin 6 → ℤ => (w i : ZMod 3)) hmatrix).trans (congrFun hc i))

end Langlands.CartanE6Root
