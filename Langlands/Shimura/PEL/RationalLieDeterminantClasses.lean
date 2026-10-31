import Langlands.AbelianScheme.RationalAlgebraActionClasses
import Langlands.Shimura.PEL.RationalLieDeterminantCondition

/-! # The Harris determinant condition on actual rational action classes -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AbelianScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E K A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
    (hΦ : IsCMSection E K Φ)
    {S : Scheme.{0}}
    (s : S ⟶ Spec (CommRingCat.of (D.kottwitzCocharacterReflexField C)))

/-- The actual all-chart determinant condition is invariant under an equivariant
rational isomorphism, including its actual rational inverse. -/
theorem harrisRationalLieDeterminantCondition_actionIso
    {X Y : RationalAlgebraAction S A} (e : X ≅ Y) :
    D.HarrisRationalLieDeterminantCondition C hΦ s X.abelianScheme X.action ↔
      D.HarrisRationalLieDeterminantCondition C hΦ s Y.abelianScheme Y.action :=
  D.harrisRationalLieDeterminantCondition_iso C hΦ s X.action Y.action
    (RationalAlgebraAction.underlyingIso e)
    (RationalAlgebraAction.intertwines e.hom)

/-- The actual Harris determinant condition descends to actual action classes. -/
def HarrisRationalLieDeterminantClassCondition
    (q : RationalAlgebraAction.IsoClass S A) : Prop :=
  Quotient.lift
    (fun X : RationalAlgebraAction S A =>
      D.HarrisRationalLieDeterminantCondition C hΦ s X.abelianScheme X.action)
    (by
      intro X Y h
      rcases h with ⟨e⟩
      exact propext (D.harrisRationalLieDeterminantCondition_actionIso C hΦ s e)) q

@[simp]
theorem harrisRationalLieDeterminantClassCondition_classOf
    (X : RationalAlgebraAction S A) :
    D.HarrisRationalLieDeterminantClassCondition C hΦ s
        (RationalAlgebraAction.classOf X) ↔
      D.HarrisRationalLieDeterminantCondition C hΦ s X.abelianScheme X.action :=
  Iff.rfl

/-- The quotient predicate agrees with every actual representative of a class. -/
theorem harrisRationalLieDeterminantClassCondition_iff_of_classOf_eq
    (q : RationalAlgebraAction.IsoClass S A) (X : RationalAlgebraAction S A)
    (hX : RationalAlgebraAction.classOf X = q) :
    D.HarrisRationalLieDeterminantClassCondition C hΦ s q ↔
      D.HarrisRationalLieDeterminantCondition C hΦ s X.abelianScheme X.action := by
  subst q
  rfl

/-- A class satisfies the predicate exactly when an actual representative does. -/
theorem harrisRationalLieDeterminantClassCondition_iff_exists
    (q : RationalAlgebraAction.IsoClass S A) :
    D.HarrisRationalLieDeterminantClassCondition C hΦ s q ↔
      ∃ X : RationalAlgebraAction S A,
        RationalAlgebraAction.classOf X = q ∧
          D.HarrisRationalLieDeterminantCondition C hΦ s X.abelianScheme X.action := by
  constructor
  · intro h
    obtain ⟨X, hX⟩ := RationalAlgebraAction.classOf_surjective q
    exact ⟨X, hX,
      (D.harrisRationalLieDeterminantClassCondition_iff_of_classOf_eq
        C hΦ s q X hX).mp h⟩
  · rintro ⟨X, hX, h⟩
    exact (D.harrisRationalLieDeterminantClassCondition_iff_of_classOf_eq
      C hΦ s q X hX).mpr h

/-- Fixed-base actual rational action classes satisfying the Harris determinant condition. -/
def HarrisRationalLieDeterminantClass :=
  {q : RationalAlgebraAction.IsoClass S A //
    D.HarrisRationalLieDeterminantClassCondition C hΦ s q}

/-- An actual determinant-compatible abelian scheme with action defines a class. -/
def harrisRationalLieDeterminantClassOf (X : RationalAlgebraAction S A)
    (hX : D.HarrisRationalLieDeterminantCondition C hΦ s X.abelianScheme X.action) :
    D.HarrisRationalLieDeterminantClass C hΦ s :=
  ⟨RationalAlgebraAction.classOf X, hX⟩

@[simp]
theorem harrisRationalLieDeterminantClassOf_val (X : RationalAlgebraAction S A)
    (hX : D.HarrisRationalLieDeterminantCondition C hΦ s X.abelianScheme X.action) :
    (D.harrisRationalLieDeterminantClassOf C hΦ s X hX).val =
      RationalAlgebraAction.classOf X := rfl

/-- Equality of determinant classes is precisely actual equivariant rational isomorphism. -/
theorem harrisRationalLieDeterminantClassOf_eq_iff
    (X Y : RationalAlgebraAction S A)
    (hX : D.HarrisRationalLieDeterminantCondition C hΦ s X.abelianScheme X.action)
    (hY : D.HarrisRationalLieDeterminantCondition C hΦ s Y.abelianScheme Y.action) :
    D.harrisRationalLieDeterminantClassOf C hΦ s X hX =
        D.harrisRationalLieDeterminantClassOf C hΦ s Y hY ↔ Nonempty (X ≅ Y) := by
  rw [Subtype.ext_iff]
  exact RationalAlgebraAction.classOf_eq_iff

/-- The class equality retains the actual inverse and the full algebra intertwining law. -/
theorem harrisRationalLieDeterminantClassOf_eq_iff_rationalIso
    (X Y : RationalAlgebraAction S A)
    (hX : D.HarrisRationalLieDeterminantCondition C hΦ s X.abelianScheme X.action)
    (hY : D.HarrisRationalLieDeterminantCondition C hΦ s Y.abelianScheme Y.action) :
    D.harrisRationalLieDeterminantClassOf C hΦ s X hX =
        D.harrisRationalLieDeterminantClassOf C hΦ s Y hY ↔
      ∃ e : Langlands.Rationalization.of X.abelianScheme ≅
          Langlands.Rationalization.of Y.abelianScheme,
        ∀ a : A, comp0 _ _ _ (X.action a) e.hom =
          comp0 _ _ _ e.hom (Y.action a) := by
  rw [Subtype.ext_iff]
  exact RationalAlgebraAction.classOf_eq_iff_rationalIso

/-- Every determinant class has an actual representative satisfying the condition. -/
theorem harrisRationalLieDeterminantClassOf_surjective
    (q : D.HarrisRationalLieDeterminantClass C hΦ s) :
    ∃ (X : RationalAlgebraAction S A)
      (hX : D.HarrisRationalLieDeterminantCondition C hΦ s X.abelianScheme X.action),
      D.harrisRationalLieDeterminantClassOf C hΦ s X hX = q := by
  obtain ⟨X, hX, h⟩ :=
    (D.harrisRationalLieDeterminantClassCondition_iff_exists C hΦ s q.val).mp q.property
  exact ⟨X, h, Subtype.ext hX⟩

/-- For an agreeing integral action, the class predicate is the integral condition. -/
theorem harrisRationalLieDeterminantClassCondition_classOf_iff_integral
    (X : RationalAlgebraAction S A)
    (α : D.harrisHodgePELIntegralOrder C →+* Langlands.AbelianScheme.End X.abelianScheme)
    (hα : ∀ a, endToEnd0 X.abelianScheme (α a) = X.action (a : A)) :
    D.HarrisRationalLieDeterminantClassCondition C hΦ s
        (RationalAlgebraAction.classOf X) ↔
      D.HarrisLieDeterminantCondition C hΦ s X.abelianScheme α :=
  D.harrisRationalLieDeterminantCondition_iff_integral C hΦ s
    X.abelianScheme X.action α hα

end Langlands.Shimura.CentralSimpleUnitaryData
