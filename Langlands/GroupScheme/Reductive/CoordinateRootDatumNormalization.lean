import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Compatible full integral coordinates for a root datum -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.CoordinateRootDatum

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) {I : Type v} [Fintype I] [DecidableEq I]
  (B : Module.Basis I ℤ X)

/-- The coweight coordinates dual to a chosen basis of the entire weight lattice. -/
def dualCoordinates : Y ≃ₗ[ℤ] (I → ℤ) :=
  P.flip.toPerfPair.trans B.dualBasis.equivFun

@[simp] theorem dualCoordinates_apply (y : Y) (i : I) :
    dualCoordinates P B y i = P.toLinearMap (B i) y := by
  exact B.dualBasis_equivFun (P.flip.toPerfPair y) i

/-- Transport to the two full coordinate lattices using mutually dual coordinates. -/
def ofBasis : RootDatum J (I → ℤ) (I → ℤ) :=
  P.map (Equiv.refl J) B.equivFun (dualCoordinates P B)

/-- This coordinate choice retains the full root pairing, including central directions. -/
def ofBasisEquiv : RootPairing.Equiv P (ofBasis P B) :=
  SplitExistence.rootPairingMapEquiv P B.equivFun (dualCoordinates P B)

theorem pairing_eq_sum (x : X) (y : Y) :
    P.toLinearMap x y = ∑ i, B.equivFun x i * dualCoordinates P B y i := by
  conv_lhs => rw [← B.sum_repr x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, dualCoordinates_apply, Module.Basis.equivFun_apply]

/-- The full coordinate pairing is the standard integer dot product. -/
theorem ofBasis_pairing (m n : I → ℤ) :
    (ofBasis P B).toLinearMap m n = ∑ i, m i * n i := by
  change P.toLinearMap (B.equivFun.symm m) ((dualCoordinates P B).symm n) = _
  rw [pairing_eq_sum P B, B.equivFun.apply_symm_apply,
    (dualCoordinates P B).apply_symm_apply]

@[simp] theorem ofBasis_root (j : J) : (ofBasis P B).root j = B.equivFun (P.root j) := rfl

@[simp] theorem ofBasis_coroot (j : J) :
    (ofBasis P B).coroot j = dualCoordinates P B (P.coroot j) := rfl

/-- Reducedness is preserved under the full change of lattice coordinates. -/
theorem ofBasis_isReduced (hP : P.IsReduced) : (ofBasis P B).IsReduced := by
  let := hP
  refine ⟨fun α β hdep => ?_⟩
  have hdep' : ¬ LinearIndependent ℤ ![P.root α, P.root β] := by
    intro hli
    apply hdep
    convert hli.map_injOn B.equivFun.toLinearMap B.equivFun.injective.injOn using 1
    ext a
    fin_cases a <;> rfl
  rcases RootPairing.IsReduced.eq_or_eq_neg α β hdep' with h | h
  · left
    simp only [ofBasis_root, h]
  · right
    simp only [ofBasis_root, h, map_neg]

/-- Every finite-rank reduced root datum admits full mutually dual coordinates. -/
theorem exists_equiv_standard [Module.Finite ℤ X] (hP : P.IsReduced) :
    ∃ (I : Type u) (_ : Fintype I) (Q : RootDatum J (I → ℤ) (I → ℤ)),
      Nonempty (RootPairing.Equiv P Q) ∧ Q.IsReduced ∧
        ∀ m n, Q.toLinearMap m n = ∑ i, m i * n i := by
  classical
  have := SplitExistence.ChevalleyData.isTorsionFree_weight P
  let B := Module.Free.chooseBasis ℤ X
  exact ⟨_, inferInstance, ofBasis P B, ⟨ofBasisEquiv P B⟩,
    ofBasis_isReduced P B hP, ofBasis_pairing P B⟩

end Langlands.GroupScheme.CoordinateRootDatum
