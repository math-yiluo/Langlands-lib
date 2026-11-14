import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisor
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The relative effective Cartier locus of a flat closed subscheme of a proper flat family -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Let `B` be a locally noetherian scheme, `q : Y ⟶ B` a proper flat morphism and `Z` an ideal
sheaf on `Y` whose closed subscheme is flat over `B`. Then there is an open subscheme `U ⊆ B`
such that for every pullback square
```
YT --gY--> Y
|qT        |q
v          v
T  --g---> B
```
of schemes, the pulled-back ideal `Z.comap gY` is a relative effective Cartier ideal for `qT`
exactly when `g` lands in `U`. -/
def RelativeEffectiveCartierLocusStatement : Prop :=
  ∀ {B Y : Scheme.{u}} (q : Y ⟶ B) (Z : Y.IdealSheafData),
    IsLocallyNoetherian B → IsProper q → Flat q → Flat (Z.subschemeι ≫ q) →
    ∃ U : B.Opens, ∀ {T YT : Scheme.{u}} (g : T ⟶ B) (qT : YT ⟶ T) (gY : YT ⟶ Y),
      IsPullback gY qT q g →
        (IsRelativeEffectiveCartierIdeal qT (Z.comap gY) ↔ Set.range g.base ⊆ (U : Set B))

end Langlands.AlgebraicGeometry.Picard
