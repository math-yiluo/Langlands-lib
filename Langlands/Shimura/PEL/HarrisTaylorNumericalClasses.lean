import Langlands.AbelianScheme.RationalAlgebraActionClasses
import Langlands.Shimura.PEL.HarrisTaylorLieCondition

/-! # Actual rational action classes with the Harris–Taylor numerical conditions -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open Langlands.AbelianScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.HarrisTaylor

variable (L K : Type) [Field L] [NumberField L] [IsCMField L]
    [Field K] [NumberField K] [IsCMField K] [Algebra L K]
    {S : Scheme.{0}} (s : S ⟶ Spec (.of K))
    {A : Type} [Ring A] [Algebra ℚ A] [Algebra K A] (n : ℕ)

/-- An actual equivariant rational isomorphism preserves the all-chart central trace test. -/
theorem centralLieTraceCondition_actionIso
    {X Y : RationalAlgebraAction S A} (e : X ≅ Y) :
    CentralLieTraceCondition L s X.abelianScheme X.action n ↔
      CentralLieTraceCondition L s Y.abelianScheme Y.action n :=
  centralLieTraceCondition_iso L s X.action n Y.action
    (RationalAlgebraAction.underlyingIso e)
    (RationalAlgebraAction.intertwines e.hom)

/-- The all-chart central trace condition on the actual equivariant rational-isomorphism quotient. -/
def CentralLieTraceClassCondition (q : RationalAlgebraAction.IsoClass S A) : Prop :=
  Quotient.lift
    (fun X : RationalAlgebraAction S A =>
      CentralLieTraceCondition L s X.abelianScheme X.action n)
    (by
      intro X Y h
      rcases h with ⟨e⟩
      exact propext (centralLieTraceCondition_actionIso L K s n e)) q

@[simp]
theorem centralLieTraceClassCondition_classOf (X : RationalAlgebraAction S A) :
    CentralLieTraceClassCondition L K s n (RationalAlgebraAction.classOf X) ↔
      CentralLieTraceCondition L s X.abelianScheme X.action n := Iff.rfl

/-- The central trace quotient predicate agrees with every actual representative. -/
theorem centralLieTraceClassCondition_iff_of_classOf_eq
    (q : RationalAlgebraAction.IsoClass S A) (X : RationalAlgebraAction S A)
    (hX : RationalAlgebraAction.classOf X = q) :
    CentralLieTraceClassCondition L K s n q ↔
      CentralLieTraceCondition L s X.abelianScheme X.action n := by
  subst q
  rfl

variable (E : Type) [Field E] [NumberField E]

/-- The image of actual dimension-and-trace satisfying representatives in the actual quotient.
Only existence of a satisfying representative is used for the dimension conjunct. -/
def NumericalActionClassCondition (q : RationalAlgebraAction.IsoClass S A) : Prop :=
  ∃ X : RationalAlgebraAction S A, RationalAlgebraAction.classOf X = q ∧
    NumericalCondition L s E X.abelianScheme X.action n

/-- A numerically satisfying representative defines a class in the constructed image. -/
theorem numericalActionClassCondition_classOf (X : RationalAlgebraAction S A)
    (hX : NumericalCondition L s E X.abelianScheme X.action n) :
    NumericalActionClassCondition L K s n E (RationalAlgebraAction.classOf X) :=
  ⟨X, rfl, hX⟩

/-- Every numerical class satisfies the well-defined central trace quotient predicate. -/
theorem numericalActionClassCondition_centralTrace
    (q : RationalAlgebraAction.IsoClass S A)
    (hq : NumericalActionClassCondition L K s n E q) :
    CentralLieTraceClassCondition L K s n q := by
  obtain ⟨X, hX, hnum⟩ := hq
  exact (centralLieTraceClassCondition_iff_of_classOf_eq L K s n q X hX).mpr hnum.2

/-- Fixed-base equivariant rational-isomorphism classes with a dimension-and-trace
satisfying actual abelian-scheme representative. -/
def NumericalActionClass :=
  {q : RationalAlgebraAction.IsoClass S A // NumericalActionClassCondition L K s n E q}

/-- Take the actual rational-isomorphism class of a numerically satisfying action. -/
def numericalActionClassOf (X : RationalAlgebraAction S A)
    (hX : NumericalCondition L s E X.abelianScheme X.action n) :
    NumericalActionClass L K s n E (A := A) :=
  ⟨RationalAlgebraAction.classOf X,
    numericalActionClassCondition_classOf L K s n E X hX⟩

@[simp]
theorem numericalActionClassOf_val (X : RationalAlgebraAction S A)
    (hX : NumericalCondition L s E X.abelianScheme X.action n) :
    (numericalActionClassOf L K s n E X hX).val =
      RationalAlgebraAction.classOf X := rfl

/-- Equality of satisfying classes is exactly actual equivariant rational isomorphism. -/
theorem numericalActionClassOf_eq_iff (X Y : RationalAlgebraAction S A)
    (hX : NumericalCondition L s E X.abelianScheme X.action n)
    (hY : NumericalCondition L s E Y.abelianScheme Y.action n) :
    numericalActionClassOf L K s n E X hX =
      numericalActionClassOf L K s n E Y hY ↔ Nonempty (X ≅ Y) := by
  rw [Subtype.ext_iff]
  exact RationalAlgebraAction.classOf_eq_iff

/-- The equality criterion retains the actual rational inverse and full action equation. -/
theorem numericalActionClassOf_eq_iff_rationalIso (X Y : RationalAlgebraAction S A)
    (hX : NumericalCondition L s E X.abelianScheme X.action n)
    (hY : NumericalCondition L s E Y.abelianScheme Y.action n) :
    numericalActionClassOf L K s n E X hX =
      numericalActionClassOf L K s n E Y hY ↔
        ∃ e : Langlands.Rationalization.of X.abelianScheme ≅
            Langlands.Rationalization.of Y.abelianScheme,
          ∀ a : A, comp0 _ _ _ (X.action a) e.hom =
            comp0 _ _ _ e.hom (Y.action a) := by
  rw [Subtype.ext_iff]
  exact RationalAlgebraAction.classOf_eq_iff_rationalIso

/-- Every constructed numerical class has an actual satisfying representative. -/
theorem numericalActionClassOf_surjective (q : NumericalActionClass L K s n E (A := A)) :
    ∃ (X : RationalAlgebraAction S A)
      (hX : NumericalCondition L s E X.abelianScheme X.action n),
      numericalActionClassOf L K s n E X hX = q := by
  obtain ⟨X, hX, hnum⟩ := q.property
  exact ⟨X, hnum, Subtype.ext hX⟩

/-- Forgetting the numerical restriction embeds these classes into the actual ambient quotient. -/
theorem numericalActionClass_val_injective :
    Function.Injective
      (fun q : NumericalActionClass L K s n E (A := A) => q.val) :=
  Subtype.val_injective

/-- Every actual representative of a numerical class satisfies the central trace test. -/
theorem numericalActionClass_centralTrace
    (q : NumericalActionClass L K s n E (A := A)) (X : RationalAlgebraAction S A)
    (hX : RationalAlgebraAction.classOf X = q.val) :
    CentralLieTraceCondition L s X.abelianScheme X.action n :=
  (centralLieTraceClassCondition_iff_of_classOf_eq L K s n q.val X hX).mp
    (numericalActionClassCondition_centralTrace L K s n E q.val q.property)

end Langlands.Shimura.HarrisTaylor
