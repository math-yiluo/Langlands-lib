import Langlands.Global.AdelicEisensteinConstantTermStatement
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.Representation.Aubert.General.RationalPointFamily
import Langlands.Representation.Aubert.General.RationalWeylRootAction

/-! # Weyl double coset representatives on actual adelic points -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.Aubert.General.RationalPointFamily

/-- The standard parabolic double cosets admit a finite family of rational
normalizer representatives with the two relative root positivity conditions. -/
def EisensteinDoubleCosetsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] (_hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    [Mono i.hom.hom.left] (_hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (_hν : IsGenericCocharacter i ν)
    (P Q : Finset (SimpleRoot i ν)),
    ∃ (I : Type u) (_ : Finite I) (n : I → normalizerPoints i),
      IsDoubleCosetRepresentatives F (Standard.parabolicHom i ν (rootSet i ν Q))
        (Standard.parabolicHom i ν (rootSet i ν P)) (fun j => (n j).val) ∧
      ∀ j : I,
        (∀ α ∈ rootSet i ν P,
          schemeWeylCharacterAction i (QuotientGroup.mk (n j)) α ∈ positiveRelativeRoots i ν) ∧
        (∀ α ∈ rootSet i ν Q,
          schemeWeylCharacterAction i (QuotientGroup.mk (n j))⁻¹ α ∈ positiveRelativeRoots i ν)

end Langlands.Global
