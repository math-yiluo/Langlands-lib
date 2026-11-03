import Langlands.GroupScheme.Lie.ActionDifferential
import Langlands.GroupScheme.Torus.Weights

/-! # Weight spaces of a commutative group scheme acting through an automorphic action -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {R : CommRingCat.{u}} {H U : GroupScheme (Spec R)} [IsAffineHom U.X.hom]
  {T : CommGroupScheme (Spec R)}

/-- The weight space of a character `α` of `T` in the actual Lie algebra `Lie(U)(R)`, for an
action `a` of `H` on `U` and a homomorphism `j : T ⟶ H`: the elements `X` such that for every
test algebra `A` and every `t ∈ T(A)`, `d a(j(t)) X_A = α(t) • X_A`, where `d a` is the
differential of the action and `X_A` is the image of `X` in `Lie(U)(A)`. -/
def lieWeightSpace (a : AutomorphicAction H U) (j : T.toGrp ⟶ H) (α : characterLattice T) :
    Submodule R (Additive (lieKernel U R)) where
  carrier := {X | ∀ (A : Type u) [CommRing A] [Algebra R A] (t : Lie.AffinePoints T.toGrp A),
    a.differential (t ≫ j.hom.hom) (lieKernelMapLinear U (Algebra.ofId R A) X) =
      (Lie.characterValue α t : A) • lieKernelMapLinear U (Algebra.ofId R A) X}
  zero_mem' := by
    intro A _ _ t
    rw [map_zero, map_zero, smul_zero]
  add_mem' := by
    intro X Y hX hY A _ _ t
    rw [map_add, map_add, hX A t, hY A t, smul_add]
  smul_mem' := by
    intro c X hX A _ _ t
    rw [LinearMap.map_smulₛₗ, LinearEquiv.map_smul, hX A t, smul_comm]

theorem mem_lieWeightSpace {a : AutomorphicAction H U} {j : T.toGrp ⟶ H}
    {α : characterLattice T} {X : Additive (lieKernel U R)} :
    X ∈ a.lieWeightSpace j α ↔ ∀ (A : Type u) [CommRing A] [Algebra R A]
      (t : Lie.AffinePoints T.toGrp A),
      a.differential (t ≫ j.hom.hom) (lieKernelMapLinear U (Algebra.ofId R A) X) =
        (Lie.characterValue α t : A) • lieKernelMapLinear U (Algebra.ofId R A) X :=
  Iff.rfl

/-- The roots of `T` in `Lie(U)` for the action: the nonzero characters with a nonzero weight
space. No reducedness is imposed. -/
def lieRoots (a : AutomorphicAction H U) (j : T.toGrp ⟶ H) : Set (characterLattice T) :=
  {α | α ≠ 0 ∧ a.lieWeightSpace j α ≠ ⊥}

theorem mem_lieRoots {a : AutomorphicAction H U} {j : T.toGrp ⟶ H} {α : characterLattice T} :
    α ∈ a.lieRoots j ↔ α ≠ 0 ∧ a.lieWeightSpace j α ≠ ⊥ :=
  Iff.rfl

/-- Restricting the action along `f` gives the weight spaces for `j ≫ f`. -/
theorem lieWeightSpace_restrict (a : AutomorphicAction H U) {K : GroupScheme (Spec R)}
    (f : K ⟶ H) (j : T.toGrp ⟶ K) (α : characterLattice T) :
    (a.restrict f).lieWeightSpace j α = a.lieWeightSpace (j ≫ f) α := by
  ext X
  simp only [mem_lieWeightSpace, differential_restrict]
  rfl

theorem lieRoots_restrict (a : AutomorphicAction H U) {K : GroupScheme (Spec R)}
    (f : K ⟶ H) (j : T.toGrp ⟶ K) : (a.restrict f).lieRoots j = a.lieRoots (j ≫ f) := by
  ext α
  simp only [mem_lieRoots, lieWeightSpace_restrict]

/-- For conjugation along `i : H ⟶ U` these are the published adjoint weight spaces of
`j ≫ i`. -/
theorem lieWeightSpace_conjugation (i : H ⟶ U) (j : T.toGrp ⟶ H) (α : characterLattice T) :
    (conjugation i).lieWeightSpace j α = weightSpace (j ≫ i) α := by
  ext X
  simp only [mem_lieWeightSpace, mem_weightSpace, differential_conjugation]
  rfl

theorem lieRoots_conjugation (i : H ⟶ U) (j : T.toGrp ⟶ H) :
    (conjugation i).lieRoots j = roots (j ≫ i) := by
  ext α
  simp only [mem_lieRoots, mem_roots, lieWeightSpace_conjugation]

end Langlands.GroupScheme.AutomorphicAction
