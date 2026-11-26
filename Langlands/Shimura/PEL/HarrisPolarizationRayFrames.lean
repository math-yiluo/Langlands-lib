import Langlands.Shimura.PEL.HarrisIntegralFrameReduction
import Langlands.Shimura.PEL.FormIsoTransport
import Langlands.Shimura.PEL.PolarizedWeilOrderModel
import Langlands.AbelianScheme.Tate.WeilAlongHom0
import Langlands.AlgebraicGeometry.Picard.RationalPolarizationCompatibility

/-! # Harris frames under rational rescaling of the polarization -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (P : Prerequisites.{0}) {S : Scheme.{0}}

local notation "PObj" => PositivePolarizedAction D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  (S := S)
local notation "PAll" => (fun _ : ℕ => True)
local notation "Af" => Global.FiniteAdeles ℚ
local notation "Vf" => Af ⊗[ℚ] A
local notation:max "BOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.abelianScheme
local notation:max "WOf" X:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.PolarizedAction.dualWitness P X
local notation:max "DOf" X:max =>
  letI := auxiliaryStarRing D C
  (WOf X).dual P
local notation:max "PolOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).polarization
local notation:max "ActionOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.action
local notation "RescaleEq" X:max lam:max q:max =>
  Rationalization.ofHom lam = rationalUnitMultiple q (Rationalization.ofHom (PolOf X))

/-- Keeping the actual family and action, replace the polarization by an
actual polarization in the same nonzero rational scalar orbit. -/
abbrev harrisRescalePolarization (X : PObj) (lam : BOf X ⟶ DOf X) (q : ℚˣ)
    (hpol : (WOf X).IsPolarization P lam) (hq : RescaleEq X lam q) : PObj := by
  let := auxiliaryStarRing D C
  refine { X with polarization := lam, isPolarization := hpol, involutionCompatible := ?_ }
  have hres := (isInvolutionCompatible_rationalUnitMultiple_iff P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability X.hasDual
    X.dualEndAdditivity X.inversePoincare X.evaluation X.geometry X.actionObj.action.toRingHom
    (Rationalization.ofHom X.polarization) q).mpr X.involutionCompatible
  exact hq.symm ▸ hres

variable [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)

local notation "T" => Over.mk s
local notation "R" => Γ((Over.mk s).left, ⊤)
local notation "Frame" X:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (X).hasDual (X).geometry
    (X).inversePoincare (X).evaluation compatibility (X).polarization h
    (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation "FormAlong" X:max =>
  letI := auxiliaryStarRing D C
  adelicWeilAlongHomBilinearMap P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (X).hasDual (X).geometry
    (X).inversePoincare (X).evaluation compatibility T

/-- Rational rescaling changes the twist identification by a scalar and
keeps the same adelic map of the original regular source. -/
def harrisRescalePolarizationFrameEquiv (X : PObj) (lam : BOf X ⟶ DOf X) (q : ℚˣ)
    (hpol : (WOf X).IsPolarization P lam) (hq : RescaleEq X lam q) :
    Frame X ≃ Frame (harrisRescalePolarization D C P X lam q hpol hq) := by
  let := auxiliaryStarRing D C
  let := scalarExtensionAlgebraModule A A Af
  let := Tate.finiteAdeleAlgebraModule (BOf X) T PAll h (ActionOf X)
  let := GroupScheme.Tate.finiteAdeleModule (BOf X).toGrp T PAll h
  let := TateTwist.Divisibility.finiteAdeleModule R PAll h
  let V := GroupScheme.Tate.RationalFull (BOf X).toGrp T
  change FormIso (A ⊗[ℚ] Af) ((D.harrisHodgePELForm C).baseChange Af)
      ((FormAlong X) (PolOf X) PAll h) ≃
    FormIso (A ⊗[ℚ] Af) ((D.harrisHodgePELForm C).baseChange Af)
      ((FormAlong X) lam PAll h)
  refine FormIso.transport (LinearEquiv.refl (A ⊗[ℚ] Af) V)
    (LinearEquiv.smulOfUnit (Units.map (algebraMap ℚ Af) q)) ?_
  intro x y
  change (FormAlong X) lam PAll h x y =
    TateTwist.Divisibility.finiteAdeleAction R PAll h (algebraMap ℚ Af (q : ℚ))
      ((FormAlong X) (PolOf X) PAll h x y)
  rw [TateTwist.Divisibility.finiteAdeleAction_diagonal,
    adelicWeilAlongHomBilinearMap_apply, adelicWeilAlongHomBilinearMap_apply,
    ← rationalWeilAlongHom0BilinearMap_ofHom, ← rationalWeilAlongHom0BilinearMap_ofHom]
  have hs := rationalWeilAlongHom0BilinearMap_smul P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability X.hasDual X.geometry
    X.inversePoincare X.evaluation compatibility T (q : ℚ)
    (Rationalization.ofHom X.polarization) PAll x y
  exact hq.symm ▸ hs

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
