import Langlands.Global.AdelicEisensteinConstantTermStatement
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.Representation.Aubert.General.RationalPointFamily
import Langlands.Representation.Aubert.General.RationalWeylRootAction

/-! # Standard parabolics in the adelic geometric lemma -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.Aubert.General.RationalPointFamily

/-- The geometric-lemma parabolics for a rational normalizer representative with
both Levi root sign conditions are canonical standard subparabolics. A compact
with Iwasawa coverage for the minimal standard parabolic serves both of them. -/
def EisensteinGeometricLemmaDatumStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (_hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    [Mono i.hom.hom.left] (_hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (_hν : IsGenericCocharacter i ν)
    (P Q : Finset (SimpleRoot i ν)) (n : normalizerPoints i),
    (∀ α ∈ rootSet i ν P,
      schemeWeylCharacterAction i (QuotientGroup.mk n) α ∈ positiveRelativeRoots i ν) →
    (∀ α ∈ rootSet i ν Q,
      schemeWeylCharacterAction i (QuotientGroup.mk n)⁻¹ α ∈ positiveRelativeRoots i ν) →
    ∃ (P₁ Q₁ : Finset (SimpleRoot i ν)),
      P₁ ⊆ P ∧ Q₁ ⊆ Q ∧
      ∃ (f : Standard.parabolicScheme i ν (rootSet i ν P₁) ⟶
          Standard.parabolicScheme i ν (rootSet i ν P))
        (g' : Standard.parabolicScheme i ν (rootSet i ν Q₁) ⟶
          Standard.parabolicScheme i ν (rootSet i ν Q)),
        f ≫ Standard.parabolicHom i ν (rootSet i ν P) =
          Standard.parabolicHom i ν (rootSet i ν P₁) ∧
        g' ≫ Standard.parabolicHom i ν (rootSet i ν Q) =
          Standard.parabolicHom i ν (rootSet i ν Q₁) ∧
        IsGeometricLemmaDatum
          (Standard.parabolicHom i ν (rootSet i ν P))
          (Standard.unipotentToParabolic i ν (rootSet i ν P))
          (Standard.parabolicHom i ν (rootSet i ν Q))
          (Standard.unipotentToParabolic i ν (rootSet i ν Q)) f g' n.val ∧
        ∀ K : Subgroup (AdelicGroupPoints F G),
          IsIwasawaCompact (Standard.parabolicHom i ν ∅) K →
            IsIwasawaCompact (f ≫ Standard.parabolicHom i ν (rootSet i ν P)) K ∧
            IsIwasawaCompact (g' ≫ Standard.parabolicHom i ν (rootSet i ν Q)) K

end Langlands.Global
