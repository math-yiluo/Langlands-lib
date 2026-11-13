import Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Fppf Picard classes of a proper flat family with integral fibres and a section -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

namespace Langlands.AlgebraicGeometry.Picard

/-- Let `f : X ⟶ S` be proper, flat, locally of finite presentation, with geometrically integral
fibres and a section. For every `S`-scheme `T`, every element of the fppf Picard class sheaf of
`f` at `T` is the class of a line bundle on `T ×_S X`. Two line bundles `L`, `L'` on `T ×_S X`
have the same class exactly when `L ≅ L' ⊗ g^* N` for an invertible module `N` on `T`, where
`g : T ×_S X ⟶ T` is the projection. -/
def ProperFlatIntegralSheafClassTwistStatement : Prop :=
  ∀ {S X : Scheme.{u}} (f : X ⟶ S),
    IsProper f → Flat f → LocallyOfFinitePresentation f → GeometricallyIntegral f →
    (∃ ε : S ⟶ X, ε ≫ f = 𝟙 S) →
    ∀ T : Over S,
      (∀ ξ : (RelativePicard.classSheafPresheaf f).obj (op T),
        ∃ L : LineBundle ((relativeSpace f).obj T), RelativePicard.sheafClassOf f T L = ξ) ∧
      ∀ L L' : LineBundle ((relativeSpace f).obj T),
        RelativePicard.sheafClassOf f T L = RelativePicard.sheafClassOf f T L' ↔
          ∃ N : T.left.Modules, Scheme.Modules.IsInvertible N ∧
            Nonempty (L.obj ≅
              L'.obj ⊗ (Scheme.Modules.pullback ((relativeProjection f).app T)).obj N)

end Langlands.AlgebraicGeometry.Picard
