import Langlands.Global.AdelicGaloisBorelTwisting
import Langlands.Global.AdelicSplitSiegelOverlap

/-! # Twisted split factorization with Galois inverse-orbit matching (Springer §3.5) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance : IsAffineHom (AffineWeil.unitBaseChange F L G).X.hom :=
  isAffineHom_of_isAffine _

variable (T : CommGroupScheme (Spec (CommRingCat.of L)))
  (i : T.toGrp ⟶ AffineWeil.unitBaseChange F L G) (ν : cocharacterLattice T)

/-- Springer's §3.5 dichotomy over the splitting field. There are a compact set `C`, an
upper root bound `c` and a threshold `d` such that the scalar extension of every
`g ∈ G(𝔸_F)¹` factors as `x · i(t) · p · q`, with `x ∈ C`, a norm-one torus factor whose
simple-root norms are at most `c`, a norm-one minimal-parabolic factor and a rational point
`q`. Moreover, whenever some simple root `α` has `|α(t)| ≤ d`, the conjugate by `q⁻¹` of
the maximal standard parabolic `P_(Δ \ {α})` belongs to a family of standard parabolic
conjugates, indexed by the Galois group, that satisfies the inverse-orbit matching
condition of `IsMaximalSplitTorus.eq_simpleRelativeRoots_of_inverse_orbit_matching`. -/
def HasTwistedOverlapMatching : Prop :=
  ∃ C : Set (AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)), IsCompact C ∧
    ∃ c d : ℝ≥0ˣ, ∀ g : normOneSubgroup F G,
      ∃ x ∈ C, ∃ (t : AdelicGroupPoints L T.toGrp)
        (p : normOneSubgroup L (Standard.parabolicScheme i ν ∅))
        (q : rationalPoints (AffineWeil.unitBaseChange F L G)),
        (scalarExtensionNormOneMap F L G g : AdelicGroupPoints L _) =
            x * map L T.toGrp _ i t * map L _ _ (Standard.parabolicHom i ν ∅) p *
              rationalSection F L G q ∧
          map L T.toGrp _ i t ∈ normOneSubgroup L (AffineWeil.unitBaseChange F L G) ∧
          (∀ β ∈ simpleRelativeRoots i ν, PositiveRealTorus.normCharacter L T β t ≤ c) ∧
          ∀ α ∈ simpleRelativeRoots i ν, PositiveRealTorus.normCharacter L T α t ≤ d →
            ∃ J : (L ≃ₐ[F] L) → Set (characterLattice T),
              (∀ σ, J σ ⊆ simpleRelativeRoots i ν) ∧
                J 1 = simpleRelativeRoots i ν \ {α} ∧
                ∀ σ : L ≃ₐ[F] L,
                  SubgroupFunctor.range
                      (radicalGaloisHom (Standard.parabolicHom i ν (J σ⁻¹) ≫
                        ((AffineWeil.unitBaseChange F L G).innerIso q⁻¹).hom) σ) =
                    SubgroupFunctor.range (Standard.parabolicHom i ν (J 1) ≫
                      ((AffineWeil.unitBaseChange F L G).innerIso q⁻¹).hom)

end Langlands.Global.AdelicGaloisUnit

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme

/-- Springer's §3.5 argument as a conditional statement: the split fundamental-set theorem
and the split overlap estimate, applied over the splitting field of a finite Galois split
maximal model carrying a Galois twisting of its Borel pair, give the twisted factorization
with inverse-orbit matching. -/
def SplitGaloisOverlapMatchingStatement : Prop :=
  AdelicSiegelFactors.SplitAdelicFundamentalSetStatement.{u} →
    AdelicSiegelFactors.SplitSiegelOverlapStatement.{u} →
      ∀ (F : Type u) [Field F] [NumberField F]
        (G : GroupScheme (Spec (CommRingCat.of F)))
        [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
        IsConnectedReductive G →
          letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
          ∀ D : FiniteGaloisSplitMaximalModel G,
            letI : NumberField D.carrier := NumberField.of_module_finite F D.carrier
            ∀ ν : cocharacterLattice D.torus,
              IsGenericCocharacter D.inclusion ν →
                HasGaloisBorelTwisting F D.carrier G D.torus D.inclusion ν →
                  HasTwistedOverlapMatching F D.carrier G D.torus D.inclusion ν

end Langlands.Global.AdelicGaloisUnit
