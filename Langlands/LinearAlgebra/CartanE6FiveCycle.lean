import Langlands.LinearAlgebra.CartanE6Root
import Langlands.GroupScheme.Reductive.IntegralWeylVector
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.GroupTheory.OrderOfElement

/-! # A permutation basis for a five-cycle in the E6 Weyl group -/

noncomputable section

universe u

open scoped BigOperators Matrix

namespace Langlands.CartanE6Root

open RootReflectionCoefficients

private def basisMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     1, 1, 0, 0, 0, 0;
     1, 1, 1, 0, 0, 0;
     1, 1, 1, 1, 0, -1;
     1, 1, 1, 1, 1, -2]

private def inverseBasisMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     -1, 0, 1, 0, 0, 0;
     0, 0, -1, 1, 0, 0;
     0, 1, 0, -1, 1, 0;
     0, 1, 0, 0, -1, 1;
     0, 1, 0, 0, 0, 0]

private theorem left_inverse : inverseBasisMatrix * basisMatrix = 1 := by decide
private theorem right_inverse : basisMatrix * inverseBasisMatrix = 1 := by decide

/-- The cycle on coordinates `0, 1, 2, 3, 4`, fixing coordinate `5`. -/
def fiveCycle : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (![1, 2, 3, 4, 0, 5] : Fin 6 → Fin 6)
    ((Finite.injective_iff_bijective).mp (by decide))

private theorem reflect_basisMatrix_column (i : Fin 6) :
    reflect (CartanMatrix.E 6) 0 (reflect (CartanMatrix.E 6) 2
      (reflect (CartanMatrix.E 6) 3 (reflect (CartanMatrix.E 6) 4 (basisMatrix.col i)))) =
      basisMatrix.col (fiveCycle i) := by
  revert i
  decide

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) (b : P.Base) (e : b.support ≃ Fin 6)

private def a (i : Fin 6) : J := (e.symm i).val

/-- The four reflections along the length-four subchain of the long path.
The product is in the order giving `fiveCycle` on the coweight lattice. -/
def fiveCycleWeyl : P.Aut :=
  RootPairing.Equiv.reflection P (a P b e 4) * RootPairing.Equiv.reflection P (a P b e 3) *
    RootPairing.Equiv.reflection P (a P b e 2) * RootPairing.Equiv.reflection P (a P b e 0)

theorem fiveCycleWeyl_mem_weylGroup : fiveCycleWeyl P b e ∈ P.weylGroup := by
  unfold fiveCycleWeyl
  exact P.weylGroup.mul_mem (P.weylGroup.mul_mem
    (P.weylGroup.mul_mem (P.reflection_mem_weylGroup _) (P.reflection_mem_weylGroup _))
    (P.reflection_mem_weylGroup _)) (P.reflection_mem_weylGroup _)

/-- In simply connected type E6 the indicated Weyl element has order five
and permutes an integral basis as a cycle of length five and one fixed point. -/
def TypeE6FiveCycleStatement : Prop :=
  (∀ i j : b.support, P.pairing i.val j.val = CartanMatrix.E 6 (e i) (e j)) →
  P.corootSpan ℤ = ⊤ →
  orderOf (fiveCycleWeyl P b e) = 5 ∧
  ∃ B : Module.Basis (Fin 6) ℤ Y,
    ∀ i, (fiveCycleWeyl P b e).coweightEquiv (B i) = B (fiveCycle i)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
theorem typeE6FiveCycle : TypeE6FiveCycleStatement P b e := by
  classical
  intro hCartan hSpan
  let base := (Langlands.IntegralWeylVector.corootBasis P b hSpan).reindex e
  let changeBasis : (Fin 6 → ℤ) ≃ₗ[ℤ] (Fin 6 → ℤ) :=
    LinearEquiv.ofLinearMap basisMatrix.mulVecLin inverseBasisMatrix.mulVecLin
      (by rw [← Matrix.mulVecLin_mul, right_inverse, Matrix.mulVecLin_one])
      (by rw [← Matrix.mulVecLin_mul, left_inverse, Matrix.mulVecLin_one])
  let B := (Pi.basisFun ℤ (Fin 6)).map (changeBasis.trans base.equivFun.symm)
  have hB (i : Fin 6) : B i = base.equivFun.symm (basisMatrix.col i) := by
    simp only [B, Module.Basis.map_apply, Pi.basisFun_apply]
    change base.equivFun.symm (basisMatrix *ᵥ Pi.single i 1) = _
    congr 1
    rw [Matrix.mulVec_single, MulOpposite.op_one, one_smul]
  let w := fiveCycleWeyl P b e
  have hReflect (i : Fin 6) (v : Fin 6 → ℤ) :
      P.coreflection (a P b e i) (base.equivFun.symm v) =
        base.equivFun.symm (reflect (CartanMatrix.E 6) i v) := by
    have hs : ∀ r s : Fin 6, CartanMatrix.E 6 r s = CartanMatrix.E 6 s r := by decide
    have hbase (j : Fin 6) : base j = P.coroot (a P b e j) := by
      simp only [base, Module.Basis.reindex_apply, Langlands.IntegralWeylVector.corootBasis_apply, a]
    have hsum (x : Fin 6 → ℤ) : base.equivFun.symm x = ∑ j, x j • P.coroot (a P b e j) := by
      simp only [Module.Basis.equivFun_symm_apply, hbase]
    rw [hsum, P.coreflection_apply, hsum]
    have hp : P.root' (a P b e i) (∑ j : Fin 6, v j • P.coroot (a P b e j)) =
        ∑ j : Fin 6, v j * CartanMatrix.E 6 j i := by
      change P.toLinearMap (P.root (a P b e i)) (∑ j : Fin 6, v j • P.coroot (a P b e j)) = _
      simp only [map_sum, map_smul, smul_eq_mul, P.root_coroot_eq_pairing,
        a, hCartan, Equiv.apply_symm_apply, hs i]
    rw [hp]
    simp [reflect, sub_smul, Finset.sum_sub_distrib, ite_smul]
  have hAct (i : Fin 6) : w.coweightEquiv (B i) = B (fiveCycle i) := by
    rw [hB, hB]
    change P.coreflection (a P b e 0) (P.coreflection (a P b e 2)
      (P.coreflection (a P b e 3) (P.coreflection (a P b e 4) (base.equivFun.symm (basisMatrix.col i))))) = _
    rw [hReflect, hReflect, hReflect, hReflect, reflect_basisMatrix_column]
  have hPow (n : ℕ) (i : Fin 6) : (w ^ n).coweightEquiv (B i) = B ((fiveCycle^[n]) i) := by
    induction n generalizing i with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Function.iterate_succ_apply]
      change (w ^ n).coweightEquiv (w.coweightEquiv (B i)) = _
      rw [hAct, ih]
  have h5 : ∀ i : Fin 6, (fiveCycle^[5]) i = i := by decide
  have hw5 : w ^ 5 = 1 := by
    apply RootPairing.Equiv.coweightHom_injective P
    apply MulOpposite.unop_injective
    simp only [map_one, MulOpposite.unop_one]
    change (w ^ 5).coweightEquiv = LinearEquiv.refl ℤ Y
    apply LinearEquiv.toLinearMap_injective
    apply B.ext
    intro i
    exact (hPow 5 i).trans (congrArg B (h5 i))
  have hw : w ≠ 1 := by
    intro h
    have h0 := hAct 0
    rw [h] at h0
    exact (show (0 : Fin 6) ≠ fiveCycle 0 from by decide) (B.injective h0)
  have hord : orderOf w = 5 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp (orderOf_dvd_of_pow_eq_one hw5) with h | h
    · exact (hw (orderOf_eq_one_iff.mp h)).elim
    · exact h
  exact ⟨hord, B, hAct⟩

end Langlands.CartanE6Root
