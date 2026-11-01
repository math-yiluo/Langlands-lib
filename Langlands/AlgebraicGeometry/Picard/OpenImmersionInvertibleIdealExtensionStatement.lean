import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-! # Extending an actual invertible ideal across an open immersion -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- An invertible ideal on an open subscheme extends as an invertible ideal
when the target is locally Noetherian and its complementary stalks are
factorial. The comparison preserves the actual inclusions in the structure
modules. This defines the proposition, without proving it. -/
def OpenImmersionInvertibleIdealExtensionStatement : Prop :=
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] (Y : Scheme.{u})
    (j : Y ⟶ X) [IsOpenImmersion j],
    (∀ x : X, x ∉ Set.range j →
      UniqueFactorizationMonoid (X.presheaf.stalk x)) →
    ∀ (D : LineBundle Y)
      (s : D.obj ⟶ SheafOfModules.unit Y.ringCatSheaf) [Mono s],
      ∃ (E : LineBundle X)
        (t : E.obj ⟶ SheafOfModules.unit X.ringCatSheaf),
        Mono t ∧
          ∃ e : ((LineBundle.pullback j).obj E).obj ≅ D.obj,
            (Scheme.Modules.pullback j).map t ≫
                (Langlands.Scheme.Modules.pullbackUnitIso j).hom =
              e.hom ≫ s

end Langlands.AlgebraicGeometry.Picard
