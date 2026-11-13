import Langlands.GroupScheme.IntegralModel.CongruenceTower
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Henselian

/-! # Lifting congruence-level points of smooth groups over a Henselian ring

KP Lemma 8.1.3 for group schemes: over a Henselian local ring, the reduction
of integral sections of a smooth group scheme modulo every positive power of
the maximal ideal is surjective.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

/-- **KP Lemma 8.1.3, group-scheme form.** Over a Henselian local ring `R`,
for every smooth group scheme `Y` over `Spec R` and every positive level `n`,
the actual reduction map `Y(R) → Y(R/𝔪ⁿ)` on sections is surjective. -/
def HenselianCongruenceLiftingStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [HenselianLocalRing R]
    (Y : GroupScheme (Spec (CommRingCat.of R))),
    Smooth Y.X.hom →
    ∀ n : ℕ+, Function.Surjective (baseChangeSectionHom (congruenceBaseMap R n) Y)

end Langlands.GroupScheme.IntegralModel
