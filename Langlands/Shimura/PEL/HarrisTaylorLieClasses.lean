import Langlands.AbelianScheme.RationalAlgebraActionClasses
import Langlands.Shimura.PEL.HarrisTaylorLieCompatibility
import Langlands.Shimura.PEL.HarrisTaylorLieCondition

/-! # Actual rational action classes with positive Lie compatibility -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField Algebra
open Langlands.AbelianScheme

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.HarrisTaylor

variable (L : Type) [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L]
    {K : Type} [Field K] [NumberField K] [Algebra L K]
    (E : Type) [Field E] [Algebra E K]
    {S : Scheme.{0}} (s : S ⟶ Spec (.of K))
    {A : Type} [Ring A] [Algebra ℚ A] [Algebra K A] (n : ℕ)

/-- An actual equivariant rational isomorphism preserves positive Lie compatibility. -/
theorem lieCompatibility_actionIso
    {X Y : RationalAlgebraAction S A} (e : X ≅ Y) :
    LieCompatibility L E s X.abelianScheme X.action n ↔
      LieCompatibility L E s Y.abelianScheme Y.action n :=
  lieCompatibility_iso L E s X.action Y.action
    (RationalAlgebraAction.underlyingIso e)
    (RationalAlgebraAction.intertwines e.hom) n

/-- Positive Lie compatibility descends to actual equivariant rational-isomorphism classes. -/
def LieCompatibilityClassCondition (q : RationalAlgebraAction.IsoClass S A) : Prop :=
  Quotient.lift
    (fun X : RationalAlgebraAction S A =>
      LieCompatibility L E s X.abelianScheme X.action n)
    (by
      intro X Y h
      rcases h with ⟨e⟩
      exact propext (lieCompatibility_actionIso L E s n e)) q

@[simp]
theorem lieCompatibilityClassCondition_classOf (X : RationalAlgebraAction S A) :
    LieCompatibilityClassCondition L E s n (RationalAlgebraAction.classOf X) ↔
      LieCompatibility L E s X.abelianScheme X.action n := Iff.rfl

/-- The quotient predicate agrees with positive Lie compatibility on every representative. -/
theorem lieCompatibilityClassCondition_iff_of_classOf_eq
    (q : RationalAlgebraAction.IsoClass S A) (X : RationalAlgebraAction S A)
    (hX : RationalAlgebraAction.classOf X = q) :
    LieCompatibilityClassCondition L E s n q ↔
      LieCompatibility L E s X.abelianScheme X.action n := by
  subst q
  rfl

variable [NumberField E]

/-- The actual prescribed dimension and positive Lie compatibility of the same action. -/
def DimensionLieCondition (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B) : Prop :=
  PrescribedRelativeDimension E B n ∧ LieCompatibility L E s B i n

/-- One actual representative satisfies both dimension and positive Lie compatibility. -/
def DimensionLieActionClassCondition (q : RationalAlgebraAction.IsoClass S A) : Prop :=
  ∃ X : RationalAlgebraAction S A, RationalAlgebraAction.classOf X = q ∧
    DimensionLieCondition L E s n X.abelianScheme X.action

/-- Lie compatibility is invariant; dimension remains the image of actual representatives. -/
theorem dimensionLieActionClassCondition_iff
    (q : RationalAlgebraAction.IsoClass S A) :
    DimensionLieActionClassCondition L E s n q ↔
      LieCompatibilityClassCondition L E s n q ∧
        ∃ X : RationalAlgebraAction S A, RationalAlgebraAction.classOf X = q ∧
          PrescribedRelativeDimension E X.abelianScheme n := by
  constructor
  · rintro ⟨X, hX, hdim, hlie⟩
    exact ⟨(lieCompatibilityClassCondition_iff_of_classOf_eq L E s n q X hX).mpr hlie,
      X, hX, hdim⟩
  · rintro ⟨hlie, X, hX, hdim⟩
    exact ⟨X, hX, hdim,
      (lieCompatibilityClassCondition_iff_of_classOf_eq L E s n q X hX).mp hlie⟩

/-- Every representative of a joint image class satisfies the actual positive Lie condition. -/
theorem dimensionLieActionClassCondition_lieCompatibility
    (q : RationalAlgebraAction.IsoClass S A)
    (hq : DimensionLieActionClassCondition L E s n q)
    (X : RationalAlgebraAction S A) (hX : RationalAlgebraAction.classOf X = q) :
    LieCompatibility L E s X.abelianScheme X.action n :=
  (lieCompatibilityClassCondition_iff_of_classOf_eq L E s n q X hX).mp
    ((dimensionLieActionClassCondition_iff L E s n q).mp hq).1

/-- A representative belongs to the joint image exactly through a satisfying isomorphic action. -/
theorem dimensionLieActionClassCondition_classOf_iff (X : RationalAlgebraAction S A) :
    DimensionLieActionClassCondition L E s n (RationalAlgebraAction.classOf X) ↔
      ∃ Y : RationalAlgebraAction S A, Nonempty (Y ≅ X) ∧
        DimensionLieCondition L E s n Y.abelianScheme Y.action := by
  constructor
  · rintro ⟨Y, hY, h⟩
    exact ⟨Y, RationalAlgebraAction.classOf_eq_iff.mp hY, h⟩
  · rintro ⟨Y, hY, h⟩
    exact ⟨Y, RationalAlgebraAction.classOf_eq_iff.mpr hY, h⟩

/-- Actual rational action classes admitting one dimension-and-Lie satisfying representative. -/
def DimensionLieActionClass :=
  {q : RationalAlgebraAction.IsoClass S A // DimensionLieActionClassCondition L E s n q}

/-- A jointly satisfying actual action defines its actual rational-isomorphism class. -/
def dimensionLieActionClassOf (X : RationalAlgebraAction S A)
    (hX : DimensionLieCondition L E s n X.abelianScheme X.action) :
    DimensionLieActionClass L E s n (A := A) :=
  ⟨RationalAlgebraAction.classOf X, X, rfl, hX⟩

@[simp]
theorem dimensionLieActionClassOf_val (X : RationalAlgebraAction S A)
    (hX : DimensionLieCondition L E s n X.abelianScheme X.action) :
    (dimensionLieActionClassOf L E s n X hX).val = RationalAlgebraAction.classOf X := rfl

/-- Equality of joint image classes is exactly actual equivariant rational isomorphism. -/
theorem dimensionLieActionClassOf_eq_iff (X Y : RationalAlgebraAction S A)
    (hX : DimensionLieCondition L E s n X.abelianScheme X.action)
    (hY : DimensionLieCondition L E s n Y.abelianScheme Y.action) :
    dimensionLieActionClassOf L E s n X hX = dimensionLieActionClassOf L E s n Y hY ↔
      Nonempty (X ≅ Y) := by
  rw [Subtype.ext_iff]
  exact RationalAlgebraAction.classOf_eq_iff

/-- Equality retains the actual rational inverse and full algebra action equation. -/
theorem dimensionLieActionClassOf_eq_iff_rationalIso (X Y : RationalAlgebraAction S A)
    (hX : DimensionLieCondition L E s n X.abelianScheme X.action)
    (hY : DimensionLieCondition L E s n Y.abelianScheme Y.action) :
    dimensionLieActionClassOf L E s n X hX = dimensionLieActionClassOf L E s n Y hY ↔
      ∃ e : Langlands.Rationalization.of X.abelianScheme ≅
          Langlands.Rationalization.of Y.abelianScheme,
        ∀ a : A, comp0 _ _ _ (X.action a) e.hom = comp0 _ _ _ e.hom (Y.action a) := by
  rw [Subtype.ext_iff]
  exact RationalAlgebraAction.classOf_eq_iff_rationalIso

/-- Every joint image class has one actual representative satisfying both conditions. -/
theorem dimensionLieActionClassOf_surjective
    (q : DimensionLieActionClass L E s n (A := A)) :
    ∃ (X : RationalAlgebraAction S A)
      (hX : DimensionLieCondition L E s n X.abelianScheme X.action),
      dimensionLieActionClassOf L E s n X hX = q := by
  obtain ⟨X, hX, h⟩ := q.property
  exact ⟨X, h, Subtype.ext hX⟩

/-- Forgetting the joint restriction embeds these classes into the actual ambient quotient. -/
theorem dimensionLieActionClass_val_injective :
    Function.Injective (fun q : DimensionLieActionClass L E s n (A := A) => q.val) :=
  Subtype.val_injective

end Langlands.Shimura.HarrisTaylor
