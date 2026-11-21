import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.AdelicIntertwiningOperator

/-! # Exclusion of competing Weyl exponents from the leading chamber -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints RealTorusSpace
  Langlands.Aubert.General.RationalPointFamily

/-- After transport to a sufficiently regular parameter for the reference
parabolic, only the selected Weyl translate can give leading exponents
among the indicated competing translates with finitely many shifts. -/
def EisensteinNonleadingWeylTermsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (P Q : StandardIndex F G fam.i fam.ν)
    [Fintype (relativeWeylGroup fam.i)]
    [Mono (CommGroupScheme.groupHom (fam.f Q)).hom.hom.left]
    (proj : fam.P Q ⟶ fam.M Q) (n : normalizerPoints fam.i) (c : fam.M Q ⟶ fam.M P),
    fam.l Q ≫ proj = 𝟙 (fam.M Q) →
    IsWeylConjugation (fam.p P) (fam.l P) (fam.p Q) (fam.l Q) n.val c →
    let w : relativeWeylGroup fam.i := QuotientGroup.mk n
    (∀ α ∈ Q.val, schemeWeylCharacterAction fam.i w⁻¹ α ∈ P.val) →
    ∀ S : Set (Vstar fam.T), S.Finite →
    let rQ : ParabolicRootPresentation (fam.p Q) (fam.l Q) (fam.a Q) :=
      ⟨⟨fam.T, fam.i, fam.ν, Q.val, fam.f Q⟩, fam.isCompatible Q⟩
    let hA := (fam.isCompatible Q).splitComponent.isCentralSplitTorus.1.1
    let hT := fam.maximalSplit.isSplitSubtorus.1
    ∃ R : ℝ, ∀ lam : ComplexCharacterParameter F (fam.P P),
      rQ.IsRegularParameter hA hT R (weylParameter (fam.l P) c proj lam) →
      ∀ v : relativeWeylGroup fam.i, v ≠ w →
        (∀ α ∈ P.val, schemeWeylCharacterAction fam.i v α ∈ positiveRelativeRoots fam.i fam.ν) →
        ∀ (J : StandardIndex F G fam.i fam.ν) (exponent : ComplexCharacterParameter F (fam.P J))
          (shift : Vstar fam.T), shift ∈ S →
          fam.chamberEmbedding J (parameterRealPart F (fam.P J) exponent) =
            relativeWeylRealCharacterAction fam.i v
              (fam.chamberEmbedding P (parameterRealPart F (fam.P P) lam)) + shift →
          ¬ fam.IsLeadingExponent J exponent

end Langlands.Global
