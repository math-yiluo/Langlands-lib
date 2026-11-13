import Langlands.Global.AdelicGaloisBoundedRootCompact
import Langlands.GroupScheme.Descent.GaloisParabolicOrbitMatching
import Langlands.GroupScheme.GaloisPointRational

/-! # Galois twisting of a split Borel pair on upper-field adelic points -/

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

/-- The upper-field adelic point of a rational point given as a section over the base. -/
abbrev rationalSection (m : rationalPoints (AffineWeil.unitBaseChange F L G)) :
    AdelicGroupPoints L (AffineWeil.unitBaseChange F L G) :=
  rational L (AffineWeil.unitBaseChange F L G)
    (rationalCoeffEquiv L (AffineWeil.unitBaseChange F L G) m)

/-- One Galois automorphism `σ` acts on the upper adelic points by the continuous
homomorphism `φ`, and carries the split Borel pair `(P_∅, T)` to its conjugate by the
rational point `m`. The map `a` is the induced permutation of the simple roots. -/
def IsGaloisBorelTwist (σ : L ≃ₐ[F] L)
    (φ : AdelicGroupPoints L (AffineWeil.unitBaseChange F L G) →ₜ*
      AdelicGroupPoints L (AffineWeil.unitBaseChange F L G))
    (m : rationalPoints (AffineWeil.unitBaseChange F L G))
    (a : characterLattice T → characterLattice T) : Prop :=
  (∀ q : rationalPoints (AffineWeil.unitBaseChange F L G),
    φ (rationalSection F L G q) = rationalSection F L G (rationalConjugate F L G σ q)) ∧
  (∀ g : normOneSubgroup F G,
    φ (scalarExtensionNormOneMap F L G g : AdelicGroupPoints L _) =
      scalarExtensionNormOneMap F L G g) ∧
  (∀ t : AdelicGroupPoints L T.toGrp, ∃ t' : AdelicGroupPoints L T.toGrp,
    φ (map L T.toGrp _ i t) =
        rationalSection F L G m * map L T.toGrp _ i t' * (rationalSection F L G m)⁻¹ ∧
      (map L T.toGrp _ i t ∈ normOneSubgroup L (AffineWeil.unitBaseChange F L G) →
        map L T.toGrp _ i t' ∈ normOneSubgroup L (AffineWeil.unitBaseChange F L G)) ∧
      ∀ β ∈ simpleRelativeRoots i ν, ∃ β' ∈ simpleRelativeRoots i ν,
        PositiveRealTorus.normCharacter L T β t' = PositiveRealTorus.normCharacter L T β' t) ∧
  (∀ p : normOneSubgroup L (Standard.parabolicScheme i ν ∅),
    ∃ p' : normOneSubgroup L (Standard.parabolicScheme i ν ∅),
      φ (map L _ _ (Standard.parabolicHom i ν ∅) p) =
        rationalSection F L G m * map L _ _ (Standard.parabolicHom i ν ∅) p' *
          (rationalSection F L G m)⁻¹) ∧
  ∀ β ∈ simpleRelativeRoots i ν, a β ∈ simpleRelativeRoots i ν ∧
    SubgroupFunctor.range
        (radicalGaloisHom (Standard.parabolicHom i ν (simpleRelativeRoots i ν \ {β})) σ) =
      SubgroupFunctor.range
        (Standard.parabolicHom i ν (simpleRelativeRoots i ν \ {a β}) ≫
          ((AffineWeil.unitBaseChange F L G).innerIso m).hom)

/-- A family of Galois twists, one for every automorphism of `L/F`, whose simple-root
permutations form an action of the Galois group on the simple roots. -/
def HasGaloisBorelTwisting : Prop :=
  ∃ (φ : (L ≃ₐ[F] L) → (AdelicGroupPoints L (AffineWeil.unitBaseChange F L G) →ₜ*
      AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)))
    (m : (L ≃ₐ[F] L) → rationalPoints (AffineWeil.unitBaseChange F L G))
    (a : (L ≃ₐ[F] L) → characterLattice T → characterLattice T),
    (∀ σ, IsGaloisBorelTwist F L G T i ν σ (φ σ) (m σ) (a σ)) ∧
      (∀ β ∈ simpleRelativeRoots i ν, a 1 β = β) ∧
      ∀ σ τ, ∀ β ∈ simpleRelativeRoots i ν, a (σ * τ) β = a σ (a τ β)

end Langlands.Global.AdelicGaloisUnit

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme

/-- Every connected reductive group over a number field has a finite Galois splitting
field with a split maximal torus, a generic cocharacter and a Galois twisting of the
resulting split Borel pair. -/
def GaloisBorelTwistingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      ∃ D : FiniteGaloisSplitMaximalModel G,
        letI : NumberField D.carrier := NumberField.of_module_finite F D.carrier
        ∃ ν : cocharacterLattice D.torus,
          IsGenericCocharacter D.inclusion ν ∧
            HasGaloisBorelTwisting F D.carrier G D.torus D.inclusion ν

end Langlands.Global.AdelicGaloisUnit
