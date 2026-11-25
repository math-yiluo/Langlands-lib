/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.FourierTransform.FdCoefficientComparison
public import WeilConjectures.CategoryTheory.StageSystem.CommonStageCalculus

/-! # Presentations for raw scalar comparisons

Source: trace-definition coefficient-category sentence, extracted raw localization
argument, steps 7--8 (blueprint: lem-fd-raw-localization-scalar-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FdRawLocalization

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The existing completed integral transition.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
abbrev U {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :=
  sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
    (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
    (pbcFiniteFieldInclusion l Ω h) T

/-- The specified shift of the existing completed transition.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
instance uCommShift {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    (U l Ω T h).CommShift ℤ :=
  (GeneralAlgebraicallyClosedCoefficients.integralScalarCommShift_existsUnique l
    (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
    (pbcFiniteFieldInclusion l Ω h) T).exists.choose

/-- The existing ordinary integral transition.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
abbrev C {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :=
  pbcIntegralScalarExtension l Ω T dT.out iT.out h

/-- Completed integral associativity, including the actual coefficient-inclusion transport.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
def integralAssoc {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M) :
    U l Ω T h ⋙ U l Ω T k ≅ U l Ω T (h.trans k) :=
  sfIntegralScalarComp l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
    (pbcFiniteFieldInclusion l Ω h) T 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
    (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω k) ≪≫
  eqToIso (congrArg (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω M) · T)
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k))

/-- Completed integral unit with the multiplication/completeness normalization.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
def integralUnit (E : Padic.FiniteCoefficientFields l Ω) :
    U l Ω T (le_refl E) ≅ 𝟭 _ :=
  eqToIso (congrArg (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω E) · T)
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 E)) ≪≫
  sfIntegralScalarUnit l (pbcFiniteField.{u} l Ω E) T 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime))

/-- The specified framework rational transition on the common small-field presentation.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
abbrev scalar {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :=
  GeneralAlgebraicallyClosedCoefficients.transition l Ω T E L h

/-- The coefficient owner's specified rational shift.
Source: blueprint order 1462 (blueprint: lem-fd-raw-localization-scalar-coherence). -/
instance scalarCommShift {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    (scalar l Ω T h).CommShift ℤ :=
  GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω T E L h

/-- The coefficient owner's balanced-tensor associator.
Source: blueprint order 1462 (blueprint: lem-fd-raw-localization-scalar-coherence). -/
abbrev assoc {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M) :=
  GeneralAlgebraicallyClosedCoefficients.associator l Ω T E L M h k

/-- The coefficient owner's normalized unit.
Source: blueprint order 1462 (blueprint: lem-fd-raw-localization-scalar-coherence). -/
abbrev unit (E : Padic.FiniteCoefficientFields l Ω) :=
  GeneralAlgebraicallyClosedCoefficients.unitor l Ω T E

/-- The published PBC raw scalar system, including literal identity extensions.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
abbrev P := pbcScalarSystem l Ω T dT.out iT.out

variable (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)

/-- The supplied integral identity functor, with its quotient-normalized coefficient transport.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
abbrev I (E : Padic.FiniteCoefficientFields l Ω) := (stage E).integral.functor

/-- Its supplied raw rationalization, fixing the recorded pure tensor coordinates.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
abbrev suppliedJ (E : Padic.FiniteCoefficientFields l Ω) := (stage E).rational.functor

/-- The supplied rational functors in the owner's named stage presentation.
HEq fixes the entire functors and their specified shifts; this is only size-presentation
transport, with no scalar comparison or coherence assumed.
Source: coefficient-stage transport in def-fd-coefficient-comparison-datum
(blueprint: lem-fd-raw-localization-scalar-coherence). -/
structure RationalFamily where
  functor : ∀ E : Padic.FiniteCoefficientFields l Ω,
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E ⥤ pbcStageCategory l Ω T E
  identity : ∀ E, HEq (functor E) (suppliedJ l Ω T stage E)
  [shift : ∀ E, (functor E).CommShift ℤ]
  shift_identity : ∀ E (n : ℤ),
    HEq ((functor E).commShiftIso n) ((suppliedJ l Ω T stage E).commShiftIso n)

attribute [instance] RationalFamily.shift

variable (family : RationalFamily l Ω T stage)

/-- The supplied rational functor on the owner's coefficient stage.
Source: coefficient-stage transport (blueprint: lem-fd-raw-localization-scalar-coherence). -/
abbrev J (E : Padic.FiniteCoefficientFields l Ω) := family.functor E

/-- The type of the specified inverse comparison after raw rationalization.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
abbrev RawComparison := ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
  scalar l Ω T h ⋙ J l Ω T stage family L ≅ J l Ω T stage family E ⋙ (P l Ω T).T h

/-- The three successive inverse comparisons before either associator contraction.
Source: trace-definition scalar comparison, displayed D
(blueprint: lem-fd-raw-localization-scalar-coherence). -/
def fourComparison (j : RawComparison l Ω T stage family)
    {E L M N : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M) (m : M ≤ N)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :=
  (j m).hom.app ((scalar l Ω T k).obj ((scalar l Ω T h).obj K)) ≫
    ((P l Ω T).T m).map ((j k).hom.app ((scalar l Ω T h).obj K)) ≫
    ((P l Ω T).T m).map (((P l Ω T).T k).map ((j h).hom.app K))

/-- The first framework associator contraction in the four-field diagram.
Source: trace-definition scalar comparison, first four-field contraction
(blueprint: lem-fd-raw-localization-scalar-coherence). -/
def leftContraction {E L M N : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :=
  (scalar l Ω T m).map ((assoc l Ω T h k).hom.app K) ≫
    (assoc l Ω T (h.trans k) m).hom.app K

/-- The second framework associator contraction in the four-field diagram.
Source: trace-definition scalar comparison, second four-field contraction
(blueprint: lem-fd-raw-localization-scalar-coherence). -/
def rightContraction {E L M N : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :=
  (assoc l Ω T k m).hom.app ((scalar l Ω T h).obj K) ≫
    (assoc l Ω T h (k.trans m)).hom.app K

end WeilConjectures.FdRawLocalization
