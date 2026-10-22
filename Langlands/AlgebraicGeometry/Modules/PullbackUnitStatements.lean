import Langlands.AlgebraicGeometry.Modules.PullbackUnit

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Langlands.Scheme.Modules

/-- Characterization of the unit comparison by the pullback-pushforward adjunction. -/
def PullbackUnitAdjunctionStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (pullbackUnitIso f).hom = unitToPushforwardUnit f

/-- Compatibility with the existing pullback comparison for identity maps. -/
def PullbackUnitIdentityStatement : Prop :=
  ∀ X : Scheme.{u}, (pullbackUnitIso (𝟙 X)).hom =
    (Scheme.Modules.pullbackId X).hom.app (SheafOfModules.unit X.ringCatSheaf)

/-- Compatibility with the existing pullback comparison for composites. -/
def PullbackUnitCompositionStatement : Prop :=
  ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z),
    (Scheme.Modules.pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
      (pullbackUnitIso (f ≫ g)).hom =
    (Scheme.Modules.pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom

/-- The adjunction, identity and composition laws for the canonical unit comparison. -/
def PullbackUnitCoherenceStatement : Prop :=
  PullbackUnitAdjunctionStatement.{u} ∧
    PullbackUnitIdentityStatement.{u} ∧ PullbackUnitCompositionStatement.{u}

end Langlands.Scheme.Modules
