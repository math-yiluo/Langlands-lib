import Langlands.GroupScheme.Rational.RelativeCentralDirections

/-! # Intrinsic root-complement and split-central-direction targets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.GroupScheme

/-- The actual root span and restrictions of rational characters of the group
are complementary in the full character space, over both `ℚ` and `ℝ`. This
target has no root-system-realization premise. -/
def RelativeCharacterRootComplementStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i →
    haveI := hG.isAffineHom
    IsCompl (relativeRootSpan i) (rationalCharacterRestrictRat i).range ∧
    IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range

/-- The actual split component embeds into the chosen maximal split torus with
cocharacter image the common root annihilator. This subspace is fixed pointwise
by the actual relative Weyl group and has the rational-character rank. -/
def RelativeSplitCentralDirectionsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    Module.Finite ℝ (V T) ∧
    Module.Finite ℝ (Vstar T) ∧
    Module.finrank ℝ (V T) = splitTorusRank T ∧
    Module.finrank ℝ (Vstar T) = splitTorusRank T ∧
    Module.finrank ℝ (relativeCentralDirections i) = rationalCharacterRank G ∧
    (∀ (w : relativeWeylGroup i) (v : V T), v ∈ relativeCentralDirections i →
      relativeWeylRealAction i w v = v) ∧
    ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G),
      IsSplitComponent a →
      ∃ f : A ⟶ T,
        CommGroupScheme.groupHom f ≫ i = a ∧
        IsClosedSubgroup (CommGroupScheme.groupHom f) ∧
        Function.Injective (cocharacterMapReal f) ∧
        (cocharacterMapReal f).range = relativeCentralDirections i ∧
        (rationalCharacterRestrictRat (CommGroupScheme.groupHom f)).ker =
          relativeRootSpan i ∧
        (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)).ker =
          relativeRootSpanReal i

/-- The complementary character directions and their actual split-central
cocharacter realization, under intrinsic reductive and maximal-split hypotheses. -/
def RelativeCentralDirectionsStatement : Prop :=
  RelativeCharacterRootComplementStatement.{u} ∧
    RelativeSplitCentralDirectionsStatement.{u}

end Langlands.GroupScheme
