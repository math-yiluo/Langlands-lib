import Langlands.Geometry.Building.RootUnitaryHeisenbergAssembly

/-! # Additivity of the Heisenberg cocycle in field coordinates

The cocycle of a Heisenberg normal form is additive in its second argument on rational
points. Hence for any additive coordinates of `V(k)` and of `U_{2a}(k)` the cocycle written in
these coordinates is additive in its second argument; this is the field `form_add` of
`HeisenbergUnitaryData`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RelativeRoot

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G U U₂ : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  {i : S.toGrp ⟶ G} {a : characterLattice S}
  {j : U ⟶ G} {hj : (subgroup i a).IsRepresentedBy j}
  {j₂ : U₂ ⟶ G} {hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂}
  {C : DoubleRootCommutatorPairing i a hj hj₂}

/-- The cocycle of a Heisenberg normal form is multiplicative in its second argument. -/
theorem HeisenbergNormalForm.cocycle_lift_mul_right (M : HeisenbergNormalForm C)
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i) {T : Over (Spec (CommRingCat.of k))}
    (x y y' : T ⟶ C.V.X) :
    lift x (y * y') ≫ M.cocycle = (lift x y ≫ M.cocycle) * (lift x y' ≫ M.cocycle) := by
  obtain ⟨d, e, he⟩ := C.weightVectorStructure.1
  have h2a : 2 • a ≠ 0 := hS.nsmul_ne_zero ha (by omega)
  obtain ⟨m, e', he'⟩ := weightVectorCoordinatesOfNoHigherRoots hS i h2a
    (hasNoHigherRoots_two_nsmul hhigh) hj₂
  have hb := (M.isBilinearVectorPairing_cocycle hS ha he he' T x x y y' 1).2.1
  apply (e' T).injective
  rw [map_mul]
  exact hb

/-- In any additive coordinates of `V(k)` and `U_{2a}(k)`, the cocycle is additive in its
second argument. -/
theorem HeisenbergNormalForm.form_add_of_cocycle_eq (M : HeisenbergNormalForm C)
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    {E : Type*} [AddCommGroup E] {H : AddSubgroup E}
    (first : Multiplicative E ≃* rationalPoints C.V) (second : Multiplicative H ≃* rationalPoints U₂)
    (form : E → E → E)
    (cocycle_eq : ∀ x y : E,
      (Multiplicative.toAdd
        (second.symm (lift (first (Multiplicative.ofAdd x)) (first (Multiplicative.ofAdd y)) ≫
          M.cocycle))).1 = form x y)
    (x y y' : E) : form x (y + y') = form x y + form x y' := by
  rw [← cocycle_eq, ← cocycle_eq, ← cocycle_eq, ofAdd_add, map_mul,
    HeisenbergNormalForm.cocycle_lift_mul_right M hS ha hhigh, map_mul, toAdd_mul]
  rfl

end Langlands.Geometry.Building
