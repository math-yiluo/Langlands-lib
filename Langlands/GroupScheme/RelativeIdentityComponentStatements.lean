import Langlands.GroupScheme.RelativeIdentityComponent

/-! # Smooth relative identity-component structure targets

Existence and properties concern the actual all-test representation predicate.
Base change is unrestricted. Affineness over a DVR is a separate target.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeIdentityComponent

/-- A smooth group scheme has a smooth relative identity component with
geometrically connected fibres, represented by an actual open subgroup. -/
def SmoothExistenceStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), Smooth G.X.hom →
    ∃ (H : GroupScheme S) (i : H ⟶ G),
      IsRelativeIdentityComponent G i ∧
        Smooth H.X.hom ∧ GeometricallyConnected H.X.hom

/-- Every actual open subgroup representing the relative identity component
of a smooth group scheme is normal on all test schemes. -/
def SmoothNormalityStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), Smooth G.X.hom →
    ∀ (H : GroupScheme S) (i : H ⟶ G),
      IsRelativeIdentityComponent G i → (SubgroupFunctor.range i).IsNormal

/-- Pulling back a represented relative identity component of a smooth group
scheme along any morphism of base schemes again represents that component. -/
def SmoothBaseChangeStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), Smooth G.X.hom →
    ∀ (H : GroupScheme S) (i : H ⟶ G), IsRelativeIdentityComponent G i →
      ∀ (S' : Scheme.{u}) (b : S' ⟶ S),
        IsRelativeIdentityComponent ((GroupScheme.baseChange b).obj G)
          ((GroupScheme.baseChange b).map i)

/-- The existence, all-test normality and arbitrary-base-change targets for
smooth relative identity components, in the same arbitrary universe. -/
def SmoothStructureStatement : Prop :=
  SmoothExistenceStatement.{u} ∧
    SmoothNormalityStatement.{u} ∧ SmoothBaseChangeStatement.{u}

end Langlands.GroupScheme.RelativeIdentityComponent
