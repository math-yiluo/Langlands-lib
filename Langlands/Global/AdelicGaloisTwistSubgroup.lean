import Langlands.Global.AdelicGaloisTwistNormOne
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction

/-! # Galois twisting of norm-one points of subgroups (Lemma S)

Interfaces for the proof of `GaloisBorelTwistingStatement`: the Galois twist `galoisTwist`
of the upper adelic points of `G_L` preserves the norm-one subgroup, and it carries norm-one
points of a closed subgroup `f : P → G_L` to conjugates of norm-one points of any closed
subgroup `g : Q → G_L` whose `m`-conjugate has the same range as the canonical Galois
translate of `f`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Lemma S1: the Galois twist of a norm-one upper adelic point of `G_L` is norm-one. -/
def GaloisTwistNormOneStatement : Prop :=
  ∀ (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (σ : L ≃ₐ[F] L)
    (x : AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)),
    x ∈ normOneSubgroup L (AffineWeil.unitBaseChange F L G) →
      galoisTwist F L G σ x ∈ normOneSubgroup L (AffineWeil.unitBaseChange F L G)

/-- Lemma S2: if the canonical Galois translate of a closed subgroup `f : P → G_L` has the
same range as the conjugate by a rational point `m` of a closed subgroup `g : Q → G_L`, then
the Galois twist of the image of a norm-one point of `P` is the `m`-conjugate of the image of
a norm-one point of `Q`. -/
def GaloisTwistSubgroupStatement : Prop :=
  ∀ (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (σ : L ≃ₐ[F] L)
    (P Q : GroupScheme (Spec (CommRingCat.of L)))
    (f : P ⟶ AffineWeil.unitBaseChange F L G) (g : Q ⟶ AffineWeil.unitBaseChange F L G)
    (m : rationalPoints (AffineWeil.unitBaseChange F L G)),
    IsClosedSubgroup f → IsClosedSubgroup g →
    SubgroupFunctor.range (radicalGaloisHom f σ) =
        SubgroupFunctor.range (g ≫ ((AffineWeil.unitBaseChange F L G).innerIso m).hom) →
    ∀ p : normOneSubgroup L P, ∃ q : normOneSubgroup L Q,
      galoisTwist F L G σ (map L P (AffineWeil.unitBaseChange F L G) f p) =
        rationalSection F L G m * map L Q (AffineWeil.unitBaseChange F L G) g q *
          (rationalSection F L G m)⁻¹

end Langlands.Global.AdelicGaloisUnit
