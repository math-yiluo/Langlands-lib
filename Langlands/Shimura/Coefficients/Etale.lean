import Langlands.Shimura.Coefficients.Associated
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Associated coefficient sheaves on the actual small etale site -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory AlgebraicGeometry

variable (X : Scheme.{u}) {G : Type u} [Group G]
variable (Y : Action X.Etale G)

/-- The finite etale cover and geometric free-transitive condition on an actual
deck action. This predicate supplies no sheaf or descent comparison. -/
def IsFiniteGeometricTorsor : Prop :=
  Finite G ∧ IsFinite Y.V.hom ∧ Function.Surjective Y.V.hom ∧
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (a b : Spec (CommRingCat.of Ω) ⟶ Y.V.left),
      a ≫ Y.V.hom = b ≫ Y.V.hom →
        ∃! g : G, a ≫ (Y.ρ g).left = b

variable {R : Type u} [CommRing R]

/-- The associated small-etale sheaf from a genuine etale cover action and
module representation, using the proved invariant-sheaf construction. -/
def etaleAssociatedFunctor :
    Action (ModuleCat.{u} R) G ⥤
      Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R) :=
  constantAssociatedFunctor (Scheme.smallEtaleTopology X) Y

/-- Equivariant coefficient systems give actual sheaf systems with all
transition identities and compositions inherited from the constructed functor. -/
def etaleAssociatedSystem
    (D : ℕᵒᵖ ⥤ Action (ModuleCat.{u} R) G) :
    ℕᵒᵖ ⥤ Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R) :=
  D ⋙ etaleAssociatedFunctor X Y

@[simp] theorem etaleAssociatedSystem_obj
    (D : ℕᵒᵖ ⥤ Action (ModuleCat.{u} R) G) (n : ℕᵒᵖ) :
    (etaleAssociatedSystem X Y D).obj n =
      (etaleAssociatedFunctor X Y).obj (D.obj n) := rfl

@[simp] theorem etaleAssociatedSystem_map
    (D : ℕᵒᵖ ⥤ Action (ModuleCat.{u} R) G)
    {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (etaleAssociatedSystem X Y D).map f =
      (etaleAssociatedFunctor X Y).map (D.map f) := rfl

end Langlands.Shimura.Coefficients
