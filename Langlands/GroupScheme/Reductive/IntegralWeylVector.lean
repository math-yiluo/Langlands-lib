import Langlands.GroupScheme.Reductive.RootDatum
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Reduced

/-! # The integral Weyl vector when the coroots generate the cocharacter lattice -/

noncomputable section

universe u v w

namespace Langlands.IntegralWeylVector

variable {J : Type u} {X : Type v} {Y : Type w}
  [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)

/-- The simple coroots form an integral basis when all coroots generate the lattice. -/
def corootBasis : Module.Basis b.support ℤ Y :=
  Module.Basis.mk b.linearIndepOn_coroot <| by
    change ⊤ ≤ Submodule.span ℤ (Set.range (P.coroot ∘ ((↑) : b.support → J)))
    simp [Set.range_comp, hspan]

@[simp] theorem corootBasis_apply (i : b.support) :
    corootBasis P b hspan i = P.coroot i := by
  simp [corootBasis]

/-- The unique integral weight taking the value one on every simple coroot. -/
def rho : X :=
  P.toLinearMap.toPerfPair.symm ((corootBasis P b hspan).constr ℤ (fun _ => 1))

@[simp] theorem pairing_rho_simple (i : b.support) :
    P.toLinearMap (rho P b hspan) (P.coroot i) = 1 := by
  unfold rho
  rw [LinearMap.apply_symm_toPerfPair_self, ← corootBasis_apply P b hspan i,
    Module.Basis.constr_basis]

theorem eq_rho_of_pairing_simple (x : X)
    (hx : ∀ i : b.support, P.toLinearMap x (P.coroot i) = 1) :
    x = rho P b hspan := by
  apply (LinearMap.IsPerfPair.bijective_left P.toLinearMap).injective
  apply (corootBasis P b hspan).ext
  intro i
  rw [corootBasis_apply, hx, pairing_rho_simple]

include hspan in
theorem eq_of_pairing_simple_eq (x x' : X)
    (h : ∀ i : b.support, P.toLinearMap x (P.coroot i) =
      P.toLinearMap x' (P.coroot i)) : x = x' := by
  apply (LinearMap.IsPerfPair.bijective_left P.toLinearMap).injective
  apply (corootBasis P b hspan).ext
  intro i
  simpa using h i

section PositiveSum

variable [Fintype J]

open Classical in
/-- The sum of the roots positive for the supplied base. -/
def positiveRootSum : X :=
  ∑ i ∈ Finset.univ.filter b.IsPos, P.root i

end PositiveSum

end Langlands.IntegralWeylVector
