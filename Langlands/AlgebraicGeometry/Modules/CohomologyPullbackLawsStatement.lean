import Langlands.AlgebraicGeometry.Modules.CohomologyPullback

/-!
# Laws for the canonical pullback on actual relative cohomology
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Pullback along the identity, with the canonical coefficient identification. -/
def RelativeCohomologyPullbackIdentityStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (X : Over (Spec R)) (M : X.left.Modules) (n : ℕ),
    relativeCohomologyPullback (𝟙 X) M n ≫
        (relativeCohomology X.hom n).map
          ((Scheme.Modules.pullbackId X.left).hom.app M) =
      𝟙 _

/-- Pullback along a composite, with the canonical pullback-composition
identification on coefficients. -/
def RelativeCohomologyPullbackCompositionStatement : Prop :=
  ∀ (R : CommRingCat.{u}) {X Y Z : Over (Spec R)}
    (h : Y ⟶ X) (k : Z ⟶ Y) (M : X.left.Modules) (n : ℕ),
    relativeCohomologyPullback h M n ≫
        relativeCohomologyPullback k ((Scheme.Modules.pullback h.left).obj M) n ≫
        (relativeCohomology Z.hom n).map
          ((Scheme.Modules.pullbackComp k.left h.left).hom.app M) =
      relativeCohomologyPullback (k ≫ h) M n

/-- Naturality of canonical cohomology pullback in the coefficient module. -/
def RelativeCohomologyPullbackCoefficientNaturalityStatement : Prop :=
  ∀ (R : CommRingCat.{u}) {X Y : Over (Spec R)} (h : Y ⟶ X)
    (M M' : X.left.Modules) (φ : M ⟶ M') (n : ℕ),
    (relativeCohomology X.hom n).map φ ≫ relativeCohomologyPullback h M' n =
      relativeCohomologyPullback h M n ≫
        (relativeCohomology Y.hom n).map ((Scheme.Modules.pullback h.left).map φ)

/-- Degree-zero normalization by the actual adjunction-unit map on sections. -/
def RelativeCohomologyPullbackDegreeZeroStatement : Prop :=
  ∀ (R : CommRingCat.{u}) {X Y : Over (Spec R)} (h : Y ⟶ X)
    (M : X.left.Modules),
    relativeCohomologyPullback h M 0 ≫
        (relativeCohomologyZeroIso Y.hom).hom.app
          ((Scheme.Modules.pullback h.left).obj M) =
      (relativeCohomologyZeroIso X.hom).hom.app M ≫
        relativeGlobalSectionsPullback h M

/-- A split pair induces a cohomological retraction after the canonical
identification of its twice-pulled-back coefficients. -/
def RelativeCohomologyPullbackSplitRetractionStatement : Prop :=
  ∀ (R : CommRingCat.{u}) {X Y : Over (Spec R)}
    (m : Y ⟶ X) (j : X ⟶ Y) (w : j ≫ m = 𝟙 X)
    (M : X.left.Modules) (n : ℕ),
    relativeCohomologyPullback m M n ≫
        relativeCohomologyPullback j ((Scheme.Modules.pullback m.left).obj M) n ≫
        (relativeCohomology X.hom n).map
          ((relativeCohomologySplitCoefficientIso m j w).hom.app M) =
      𝟙 _

/-- The identity, composition, coefficient-naturality, degree-zero and
split-retraction laws for the published actual cohomology pullback. -/
def RelativeCohomologyPullbackLawsStatement : Prop :=
  RelativeCohomologyPullbackIdentityStatement.{u} ∧
    RelativeCohomologyPullbackCompositionStatement.{u} ∧
    RelativeCohomologyPullbackCoefficientNaturalityStatement.{u} ∧
    RelativeCohomologyPullbackDegreeZeroStatement.{u} ∧
    RelativeCohomologyPullbackSplitRetractionStatement.{u}

end Langlands.AlgebraicGeometry.Modules.DerivedSections
