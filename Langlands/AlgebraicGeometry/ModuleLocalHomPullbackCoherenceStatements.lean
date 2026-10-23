import Langlands.AlgebraicGeometry.ModuleLocalHomPullback

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Langlands.Scheme.Modules

/-- Identity pullback of a local map agrees with the canonical identity comparisons. -/
def LocalHomPullbackIdentityStatement : Prop :=
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (M N : X.Modules) (U : X.Opens)
    (h : LocalHom M N U),
    localHomPullback (𝟙 X) U h =
      ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app M).over U ≫ h ≫
        ((AlgebraicGeometry.Scheme.Modules.pullbackId X).inv.app N).over U

/-- Successive local pullbacks agree with pullback along the composite. -/
def LocalHomPullbackCompositionStatement : Prop :=
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M N : Z.Modules) (U : Z.Opens) (h : LocalHom M N U),
    localHomPullback f (g ⁻¹ᵁ U) (localHomPullback g U h) =
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app M).over ((f ≫ g) ⁻¹ᵁ U) ≫
        localHomPullback (f ≫ g) U h ≫
        ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app N).over ((f ≫ g) ⁻¹ᵁ U)

/-- Canonical identity and composition coherence of the local pullback construction. -/
def LocalHomPullbackCoherenceStatement : Prop :=
  LocalHomPullbackIdentityStatement.{u} ∧ LocalHomPullbackCompositionStatement.{u}

end Langlands.Scheme.Modules
