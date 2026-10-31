import Langlands.AbelianScheme.Tate.WeilCompactOpenLevels
import Langlands.Shimura.PEL.ScalarExtensionRegular
import Langlands.Shimura.PEL.TraceSimilitudesLevels
import Langlands.Shimura.PEL.RationalInput
import Langlands.Shimura.PEL.HarrisPositiveInput

/-! # Harris trace-form indices for actual Weil level towers -/

universe u v w z

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField Module _root_.Algebra

variable {E : Type v} {K : Type w} {B : Type z}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring B] [Algebra E B] [Algebra K B] [IsScalarTower E K B]
    [Algebra ℚ B] [IsScalarTower ℚ E B]
    {n : ℕ} (D : CentralSimpleUnitaryData E K B n)
    (β : Bˣ) (hβ : D.involution (β : B) = -(β : B))

/-- The inverse-unit trace form on the skew-twisted regular module satisfies
the published rational PEL source conditions. -/
theorem harrisRationalPELConditions :
    PEL.RationalPELConditions
      (D.skewTwist β hβ).toSecondKindInvolution.rationalInvolution
      ((D.skewTwist β hβ).tracePairing β⁻¹) := by
  let : Module.Finite E B := Module.Finite.of_basis D.totallyRealBasis
  let : Module.Finite ℚ B := FiniteDimensional.trans ℚ E B
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    (D.skewTwist β hβ).tracePairing_isAlt β⁻¹
      (D.involution.skewAdjoint_inverse_skew β hβ),
    (D.skewTwist β hβ).tracePairing_nondegenerate β⁻¹,
    (D.skewTwist β hβ).tracePairing_respectsInvolution β⁻¹⟩

/-- In particular the canonically constructed positive Harris input has these
finite, faithful, alternating and nondegenerate source properties. -/
theorem harrisPositiveRationalPELConditions
    {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ) :
    PEL.RationalPELConditions
      (D.harrisPositivePELAlgebra C).toSecondKindInvolution.rationalInvolution
      (D.harrisPositivePELForm C) :=
  D.harrisRationalPELConditions (D.harrisPositivePELUnit C)
    (D.harrisPositivePELUnit_skew C)

/-- Transport full compact-open levels from the opposite original Harris group
to the scalar-extension group acting on the actual Weil frames. -/
def harrisWeilFiniteAdelicLevelFunctor :
    CompactOpenLevel
        D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ ⥤
      PEL.FiniteAdelicScalarExtensionLevel B B
        ((D.skewTwist β hβ).tracePairing β⁻¹) :=
  CompactOpenLevel.transportFunctor
    (D.harrisFiniteAdelicScalarExtensionContinuousEquiv β hβ)

@[simp] theorem harrisWeilFiniteAdelicLevelFunctor_obj_mem
    (U : CompactOpenLevel
      D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ)
    (g : D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) :
    D.harrisFiniteAdelicScalarExtensionContinuousEquiv β hβ g ∈
        ((D.harrisWeilFiniteAdelicLevelFunctor β hβ).obj U).toSubgroup ↔
      g ∈ U.subgroup :=
  CompactOpenLevel.transport_mem _ _ _

@[simp] theorem harrisWeilFiniteAdelicLevelFunctor_map_element
    {U W : CompactOpenLevel
      D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ}
    (f : U ⟶ W) :
    ((D.harrisWeilFiniteAdelicLevelFunctor β hβ).map f).element =
      D.harrisFiniteAdelicScalarExtensionContinuousEquiv β hβ f.element := rfl

/-- Inclusion of the original compact-open levels becomes inclusion of their
actual transported subgroups. -/
theorem harrisWeilFiniteAdelicLevelFunctor_inclusion
    {U W : CompactOpenLevel
      D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ}
    (hU : U.subgroup ≤ W.subgroup) :
    (D.harrisWeilFiniteAdelicLevelFunctor β hβ).map (CompactOpenLevel.inclusion hU) =
      CompactOpenLevel.inclusion
        (show ((D.harrisWeilFiniteAdelicLevelFunctor β hβ).obj U).toSubgroup ≤
            ((D.harrisWeilFiniteAdelicLevelFunctor β hβ).obj W).toSubgroup from
          fun _ hg => hU hg) := by
  apply CompactOpenLevel.Arrow.ext
  exact (D.harrisFiniteAdelicScalarExtensionContinuousEquiv β hβ).map_one

/-- The away analogue uses the same original involution and inverse-unit form. -/
def harrisWeilPrimeToLevelFunctor (m : ℕ) :
    CompactOpenLevel
        (D.toSecondKindInvolution.rationalInvolution.Points
          (Langlands.Global.PrimeToFiniteAdeles m))ᵐᵒᵖ ⥤
      PEL.PrimeToScalarExtensionLevel B B
        ((D.skewTwist β hβ).tracePairing β⁻¹) m :=
  CompactOpenLevel.transportFunctor
    (D.harrisPrimeToScalarExtensionContinuousEquiv β hβ m)

@[simp] theorem harrisWeilPrimeToLevelFunctor_obj_mem (m : ℕ)
    (U : CompactOpenLevel
      (D.toSecondKindInvolution.rationalInvolution.Points
        (Langlands.Global.PrimeToFiniteAdeles m))ᵐᵒᵖ)
    (g : (D.toSecondKindInvolution.rationalInvolution.Points
      (Langlands.Global.PrimeToFiniteAdeles m))ᵐᵒᵖ) :
    D.harrisPrimeToScalarExtensionContinuousEquiv β hβ m g ∈
        ((D.harrisWeilPrimeToLevelFunctor β hβ m).obj U).toSubgroup ↔
      g ∈ U.subgroup :=
  CompactOpenLevel.transport_mem _ _ _

@[simp] theorem harrisWeilPrimeToLevelFunctor_map_element (m : ℕ)
    {U W : CompactOpenLevel
      (D.toSecondKindInvolution.rationalInvolution.Points
        (Langlands.Global.PrimeToFiniteAdeles m))ᵐᵒᵖ}
    (f : U ⟶ W) :
    ((D.harrisWeilPrimeToLevelFunctor β hβ m).map f).element =
      D.harrisPrimeToScalarExtensionContinuousEquiv β hβ m f.element := rfl

theorem harrisWeilPrimeToLevelFunctor_inclusion (m : ℕ)
    {U W : CompactOpenLevel
      (D.toSecondKindInvolution.rationalInvolution.Points
        (Langlands.Global.PrimeToFiniteAdeles m))ᵐᵒᵖ}
    (hU : U.subgroup ≤ W.subgroup) :
    (D.harrisWeilPrimeToLevelFunctor β hβ m).map (CompactOpenLevel.inclusion hU) =
      CompactOpenLevel.inclusion
        (show ((D.harrisWeilPrimeToLevelFunctor β hβ m).obj U).toSubgroup ≤
            ((D.harrisWeilPrimeToLevelFunctor β hβ m).obj W).toSubgroup from
          fun _ hg => hU hg) := by
  apply CompactOpenLevel.Arrow.ext
  exact (D.harrisPrimeToScalarExtensionContinuousEquiv β hβ m).map_one

/-- The full Hecke intersection is the actual intersection after transport.
Its topological-group hypotheses follow from the Harris source data. -/
theorem harrisWeilFiniteAdelicLevelFunctor_heckeLevel
    (U W : CompactOpenLevel
      D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ)
    (g : D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) :
    letI : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
    (D.harrisWeilFiniteAdelicLevelFunctor β hβ).obj
        (CompactOpenLevel.heckeLevel U W g) =
      CompactOpenLevel.heckeLevel
        ((D.harrisWeilFiniteAdelicLevelFunctor β hβ).obj U)
        ((D.harrisWeilFiniteAdelicLevelFunctor β hβ).obj W)
        (D.harrisFiniteAdelicScalarExtensionContinuousEquiv β hβ g) := by
  let : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
  exact CompactOpenLevel.transport_heckeLevel _ _ _ _

/-- The same actual Hecke-intersection comparison away from the modulus. -/
theorem harrisWeilPrimeToLevelFunctor_heckeLevel (m : ℕ)
    (U W : CompactOpenLevel
      (D.toSecondKindInvolution.rationalInvolution.Points
        (Langlands.Global.PrimeToFiniteAdeles m))ᵐᵒᵖ)
    (g : (D.toSecondKindInvolution.rationalInvolution.Points
      (Langlands.Global.PrimeToFiniteAdeles m))ᵐᵒᵖ) :
    letI : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
    (D.harrisWeilPrimeToLevelFunctor β hβ m).obj
        (CompactOpenLevel.heckeLevel U W g) =
      CompactOpenLevel.heckeLevel
        ((D.harrisWeilPrimeToLevelFunctor β hβ m).obj U)
        ((D.harrisWeilPrimeToLevelFunctor β hβ m).obj W)
        (D.harrisPrimeToScalarExtensionContinuousEquiv β hβ m g) := by
  let : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
  exact CompactOpenLevel.transport_heckeLevel _ _ _ _

end Langlands.Shimura.CentralSimpleUnitaryData

namespace Langlands.AbelianScheme.Tate

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme Langlands.Shimura Langlands.Shimura.PEL
open NumberField _root_.Algebra
open GroupScheme.Tate (Index)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (polarizationMap : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
    evaluationA stability composition unitCoherence associativity comparison symmetry)
  {E : Type v} {K : Type w} {B : Type z}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring B] [Algebra E B] [Algebra K B] [IsScalarTower E K B]
  [Algebra ℚ B] [IsScalarTower ℚ E B]
  {n : ℕ} (D : CentralSimpleUnitaryData E K B n)
  (β : Bˣ) (hβ : D.involution (β : B) = -(β : B))
  (i : B →ₐ[ℚ] Rationalization.End A)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})

local notation "ψH" => CentralSimpleUnitaryData.tracePairing (D.skewTwist β hβ) β⁻¹

section Full

variable (h : Global.RationalProfiniteIntegerAdeleComparison)
  (hu : ∀ j : Index (fun _ => True), IsUnit (j.val : Γ(S, ⊤)))
  [hμfin : ∀ j : Index (fun _ => True), IsFinite (mu S j.val).X.hom]
  [hμet : ∀ j : Index (fun _ => True), Etale (mu S j.val).X.hom]

local notation "HarrisG" =>
  D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ
local notation "HarrisIndex" => CompactOpenLevel HarrisG
local notation "IndexFunctor" => D.harrisWeilFiniteAdelicLevelFunctor β hβ
local notation "scalarEquiv" => D.harrisFiniteAdelicScalarExtensionContinuousEquiv β hβ

local notation "ActualTower" => weilAdelicCompactOpenLevelTower preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  hA geometryA MA evaluationA polarizationMap h i B ψH s hs htor hu
  (hμfin := hμfin) (hμet := hμet)
local notation "levelTranslate" => weilAdelicLevelTranslate preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap h i B ψH
  htor hu (s := s) (hs := hs) (hμfin := hμfin) (hμet := hμet)
local notation "levelForget" => weilAdelicLevelForget preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap h i B ψH
  htor hu (s := s) (hs := hs) (hμfin := hμfin) (hμet := hμet)

/-- Actual full Weil-compatible invariant orbits at a transported Harris level. -/
abbrev HarrisWeilAdelicLevel (U : HarrisIndex) :=
  (ActualTower).obj ((IndexFunctor).obj U)

local notation "HarrisLevel" => HarrisWeilAdelicLevel preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  hA geometryA MA evaluationA polarizationMap D β hβ i s hs htor h hu
  (hμfin := hμfin) (hμet := hμet)

/-- The actual full Weil tower indexed by compact opens of the opposite
original Harris group, with its existing transporter multiplication. -/
def harrisWeilAdelicLevelTower : HarrisIndex ⥤ Type (max u z) :=
  IndexFunctor ⋙ ActualTower

local notation "HarrisTower" => harrisWeilAdelicLevelTower preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  hA geometryA MA evaluationA polarizationMap D β hβ i s hs htor h hu
  (hμfin := hμfin) (hμet := hμet)

@[simp] theorem harrisWeilAdelicLevelTower_obj (U : HarrisIndex) :
    (HarrisTower).obj U = HarrisLevel U := rfl

/-- An actual transporter acts by the published fixed-level translation of
Weil-compatible frame orbits through its scalar-extension image. -/
@[simp] theorem harrisWeilAdelicLevelTower_map {U W : HarrisIndex}
    (f : U ⟶ W) (q : HarrisLevel U) :
    (HarrisTower).map f q =
      levelTranslate (scalarEquiv f.element) ((IndexFunctor).map f).respects q := rfl

omit hμfin hμet in
/-- At the frame level the Harris action is eta composed with right multiplication. -/
theorem harrisWeilAdelicFrameRightAction_apply (g : HarrisG)
    (eta : WeilAdelicFrame preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility
      polarizationMap h i B ψH s)
    (x : Global.FiniteAdeles ℚ ⊗[ℚ] B) :
    letI : MulAction
        (ScalarExtensionSimilitudePoints B B (Global.FiniteAdeles ℚ) ψH)ᵐᵒᵖ
        (WeilAdelicFrame preservation composition unitCoherence associativity
          comparison symmetry stability hA geometryA MA evaluationA compatibility
          polarizationMap h i B ψH s) :=
      weilAdelicFrameRightAction preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
      polarizationMap h i B ψH s
    (MulOpposite.op (scalarEquiv g) • eta).1 x =
      eta.1 (x * (g.unop.val.1 : Global.FiniteAdeles ℚ ⊗[ℚ] B)) := rfl

/-- Forgetting the original Harris subgroup is the actual fixed-level
forgetting map for the transported subgroups. -/
@[simp] theorem harrisWeilAdelicLevelTower_inclusion {U W : HarrisIndex}
    (hU : U.subgroup ≤ W.subgroup) (q : HarrisLevel U) :
    (HarrisTower).map (CompactOpenLevel.inclusion hU) q =
      levelForget
        (show ((IndexFunctor).obj U).toSubgroup ≤ ((IndexFunctor).obj W).toSubgroup
          from fun _ hg => hU hg) q := by
  change (ActualTower).map ((IndexFunctor).map (CompactOpenLevel.inclusion hU)) q = _
  rw [D.harrisWeilFiniteAdelicLevelFunctor_inclusion β hβ hU]
  rfl

/-- First leg of the actual Harris-indexed full Hecke correspondence. -/
def harrisWeilAdelicHeckeLeft (U W : HarrisIndex) (g : HarrisG) :
    letI : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
    HarrisLevel (CompactOpenLevel.heckeLevel U W g) → HarrisLevel U := by
  letI : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
  exact fun q => (HarrisTower).map (CompactOpenLevel.heckeLeft U W g) q

/-- Second leg, using the original opposite-group element and unchanged multiplier. -/
def harrisWeilAdelicHeckeRight (U W : HarrisIndex) (g : HarrisG) :
    letI : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
    HarrisLevel (CompactOpenLevel.heckeLevel U W g) → HarrisLevel W := by
  letI : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
  exact fun q => (HarrisTower).map (CompactOpenLevel.heckeRight U W g) q

/-- The first leg forgets exactly the transported intermediate subgroup. -/
@[simp] theorem harrisWeilAdelicHeckeLeft_eq (U W : HarrisIndex) (g : HarrisG) :
    letI : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
    ∀ q : HarrisLevel (CompactOpenLevel.heckeLevel U W g),
      harrisWeilAdelicHeckeLeft preservation composition unitCoherence associativity
        comparison symmetry stability compatibility hA geometryA MA evaluationA
        polarizationMap D β hβ i s hs htor h hu U W g q =
      levelForget
        (show ((IndexFunctor).obj (CompactOpenLevel.heckeLevel U W g)).toSubgroup ≤
          ((IndexFunctor).obj U).toSubgroup from fun _ hg => hg.1) q := by
  let : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
  intro q
  exact harrisWeilAdelicLevelTower_inclusion preservation composition unitCoherence
    associativity comparison symmetry stability compatibility hA geometryA MA evaluationA
    polarizationMap D β hβ i s hs htor h hu
    (U := CompactOpenLevel.heckeLevel U W g) (W := U) (fun _ hg => hg.1) q

/-- The second leg translates by the actual scalar-extension image of g. -/
@[simp] theorem harrisWeilAdelicHeckeRight_eq (U W : HarrisIndex) (g : HarrisG) :
    letI : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
    ∀ q : HarrisLevel (CompactOpenLevel.heckeLevel U W g),
      harrisWeilAdelicHeckeRight preservation composition unitCoherence associativity
        comparison symmetry stability compatibility hA geometryA MA evaluationA
        polarizationMap D β hβ i s hs htor h hu U W g q =
      levelTranslate (scalarEquiv g)
        ((IndexFunctor).map (CompactOpenLevel.heckeRight U W g)).respects q := by
  let : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
  intro q
  rfl

end Full

section Away

variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  (hu : ∀ j : Index (fun j => Nat.Coprime j m), IsUnit (j.val : Γ(S, ⊤)))
  [hμfin : ∀ j : Index (fun j => Nat.Coprime j m), IsFinite (mu S j.val).X.hom]
  [hμet : ∀ j : Index (fun j => Nat.Coprime j m), Etale (mu S j.val).X.hom]

local notation "HarrisG" =>
  (D.toSecondKindInvolution.rationalInvolution.Points (Global.PrimeToFiniteAdeles m))ᵐᵒᵖ
local notation "HarrisIndex" => CompactOpenLevel HarrisG
local notation "IndexFunctor" => D.harrisWeilPrimeToLevelFunctor β hβ m
local notation "scalarEquiv" => D.harrisPrimeToScalarExtensionContinuousEquiv β hβ m

local notation "ActualTower" => weilPrimeToAdelicCompactOpenLevelTower preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  hA geometryA MA evaluationA polarizationMap hAway i B ψH s hs htor hu
  (hμfin := hμfin) (hμet := hμet)
local notation "levelTranslate" => weilPrimeToAdelicLevelTranslate preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap hAway i B ψH
  htor hu (s := s) (hs := hs) (hμfin := hμfin) (hμet := hμet)
local notation "levelForget" => weilPrimeToAdelicLevelForget preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  rationalWeilGeometricTransport hA geometryA MA evaluationA polarizationMap hAway i B ψH
  htor hu (s := s) (hs := hs) (hμfin := hμfin) (hμet := hμet)

/-- Actual away Weil-compatible invariant orbits at a transported Harris level. -/
abbrev HarrisWeilPrimeToAdelicLevel (U : HarrisIndex) :=
  (ActualTower).obj ((IndexFunctor).obj U)

local notation "HarrisLevel" => HarrisWeilPrimeToAdelicLevel preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  hA geometryA MA evaluationA polarizationMap D β hβ i s hs htor hAway hu
  (hμfin := hμfin) (hμet := hμet)

/-- The actual away Weil tower indexed by compact opens of the opposite
original Harris group, with its existing transporter multiplication. -/
def harrisWeilPrimeToAdelicLevelTower : HarrisIndex ⥤ Type (max u z) :=
  IndexFunctor ⋙ ActualTower

local notation "HarrisTower" => harrisWeilPrimeToAdelicLevelTower preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  hA geometryA MA evaluationA polarizationMap D β hβ i s hs htor hAway hu
  (hμfin := hμfin) (hμet := hμet)

@[simp] theorem harrisWeilPrimeToAdelicLevelTower_obj (U : HarrisIndex) :
    (HarrisTower).obj U = HarrisLevel U := rfl

/-- An actual transporter acts by the published fixed-level translation of
Weil-compatible frame orbits through its scalar-extension image. -/
@[simp] theorem harrisWeilPrimeToAdelicLevelTower_map {U W : HarrisIndex}
    (f : U ⟶ W) (q : HarrisLevel U) :
    (HarrisTower).map f q =
      levelTranslate (scalarEquiv f.element) ((IndexFunctor).map f).respects q := rfl

omit hμfin hμet in
/-- At the frame level the Harris action is eta composed with right multiplication. -/
theorem harrisWeilPrimeToAdelicFrameRightAction_apply (g : HarrisG)
    (eta : WeilPrimeToAdelicFrame preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility
      polarizationMap h i B ψH s hAway)
    (x : Global.PrimeToFiniteAdeles m ⊗[ℚ] B) :
    letI : MulAction
        (ScalarExtensionSimilitudePoints B B (Global.PrimeToFiniteAdeles m) ψH)ᵐᵒᵖ
        (WeilPrimeToAdelicFrame preservation composition unitCoherence associativity
          comparison symmetry stability hA geometryA MA evaluationA compatibility
          polarizationMap h i B ψH s hAway) :=
      weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
      polarizationMap h i B ψH s hAway
    (MulOpposite.op (scalarEquiv g) • eta).1 x =
      eta.1 (x * (g.unop.val.1 : Global.PrimeToFiniteAdeles m ⊗[ℚ] B)) := rfl

/-- Forgetting the original Harris subgroup is the actual fixed-level
forgetting map for the transported subgroups. -/
@[simp] theorem harrisWeilPrimeToAdelicLevelTower_inclusion {U W : HarrisIndex}
    (hU : U.subgroup ≤ W.subgroup) (q : HarrisLevel U) :
    (HarrisTower).map (CompactOpenLevel.inclusion hU) q =
      levelForget
        (show ((IndexFunctor).obj U).toSubgroup ≤ ((IndexFunctor).obj W).toSubgroup
          from fun _ hg => hU hg) q := by
  change (ActualTower).map ((IndexFunctor).map (CompactOpenLevel.inclusion hU)) q = _
  rw [D.harrisWeilPrimeToLevelFunctor_inclusion β hβ m hU]
  rfl

/-- First leg of the actual Harris-indexed away Hecke correspondence. -/
def harrisWeilPrimeToAdelicHeckeLeft (U W : HarrisIndex) (g : HarrisG) :
    letI : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
    HarrisLevel (CompactOpenLevel.heckeLevel U W g) → HarrisLevel U := by
  letI : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
  exact fun q => (HarrisTower).map (CompactOpenLevel.heckeLeft U W g) q

/-- Second leg, using the original opposite-group element and unchanged multiplier. -/
def harrisWeilPrimeToAdelicHeckeRight (U W : HarrisIndex) (g : HarrisG) :
    letI : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
    HarrisLevel (CompactOpenLevel.heckeLevel U W g) → HarrisLevel W := by
  letI : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
  exact fun q => (HarrisTower).map (CompactOpenLevel.heckeRight U W g) q

/-- The first leg forgets exactly the transported intermediate subgroup. -/
@[simp] theorem harrisWeilPrimeToAdelicHeckeLeft_eq (U W : HarrisIndex) (g : HarrisG) :
    letI : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
    ∀ q : HarrisLevel (CompactOpenLevel.heckeLevel U W g),
      harrisWeilPrimeToAdelicHeckeLeft preservation composition unitCoherence associativity
        comparison symmetry stability compatibility hA geometryA MA evaluationA
        polarizationMap D β hβ i s hs htor hAway hu U W g q =
      levelForget
        (show ((IndexFunctor).obj (CompactOpenLevel.heckeLevel U W g)).toSubgroup ≤
          ((IndexFunctor).obj U).toSubgroup from fun _ hg => hg.1) q := by
  let : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
  intro q
  exact harrisWeilPrimeToAdelicLevelTower_inclusion preservation composition unitCoherence
    associativity comparison symmetry stability compatibility hA geometryA MA evaluationA
    polarizationMap D β hβ i s hs htor hAway hu
    (U := CompactOpenLevel.heckeLevel U W g) (W := U) (fun _ hg => hg.1) q

/-- The second leg translates by the actual scalar-extension image of g. -/
@[simp] theorem harrisWeilPrimeToAdelicHeckeRight_eq (U W : HarrisIndex) (g : HarrisG) :
    letI : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
    ∀ q : HarrisLevel (CompactOpenLevel.heckeLevel U W g),
      harrisWeilPrimeToAdelicHeckeRight preservation composition unitCoherence associativity
        comparison symmetry stability compatibility hA geometryA MA evaluationA
        polarizationMap D β hβ i s hs htor hAway hu U W g q =
      levelTranslate (scalarEquiv g)
        ((IndexFunctor).map (CompactOpenLevel.heckeRight U W g)).respects q := by
  let : Module.Finite ℚ B := (D.harrisRationalPELConditions β hβ).finite_module
  intro q
  rfl

end Away

end Langlands.AbelianScheme.Tate
