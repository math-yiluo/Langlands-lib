import Langlands.Automorphic.GroupSchemeTensorForms
import Langlands.Automorphic.GroupSchemeCuspidalFormL2

/-! # Tensor-smooth cusp forms and their actual quotient L² realization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme
open Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (hrho : IsClosedSubgroup rho) (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf)
  (hN : 0 < N)

local instance tensorCuspFiniteSmoothAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- Literal tensor-smooth forms with every actual normalized proper-parabolic constant term zero. -/
def tensorAdelicCuspidalSubrepresentation :
    Subrepresentation (finitePlotSmoothFiniteRightAction F G) where
  toSubmodule :=
    (tensorAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule ⊓
      (normalizedParabolicCuspidalSubrepresentation F G hPD hG).toSubmodule.comap
        (finitePlotSmoothRationalSubrepresentation F G).toSubmodule.subtype
  apply_mem_toSubmodule c _f hf :=
    ⟨(tensorAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).apply_mem_toSubmodule c hf.1,
      (normalizedParabolicCuspidalSubrepresentation F G hPD hG).apply_mem_toSubmodule
        (AdelicGroupPoints.ofFinite F G c) hf.2⟩

theorem mem_tensorAdelicCuspidalSubrepresentation (f : FinitePlotSmoothRationalFunctions F G) :
    f ∈ tensorAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN ↔
      f ∈ tensorAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN ∧
      ∀ (P : ProperRationalParabolic G) (g : AdelicGroupPoints F G),
        constantTerm F G (properRationalParabolicRadicals hPD hG P)
          (properParabolicQuotientMeasure F G hPD hG P) f.val g = 0 := by
  change (_ ∧ f.val ∈ normalizedParabolicCuspidalSubrepresentation F G hPD hG) ↔ _
  rw [mem_normalizedParabolicCuspidalSubrepresentation_iff]
  rfl

abbrev TensorAdelicCuspidalForms :=
  (tensorAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule

def tensorAdelicCuspidalFiniteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G)
      (TensorAdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN) :=
  (tensorAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toRepresentation

/-- Faithful original-function inclusion into the earlier broader cusp forms. -/
def tensorAdelicCuspidalToCuspidal :
    (tensorAdelicCuspidalFiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).IntertwiningMap
      (adelicCuspidalFiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN) where
  toLinearMap :=
    (tensorAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule.inclusion
      (by intro _ hf; exact ⟨hf.1.1, hf.2⟩)
  isIntertwining' _ := by ext; rfl

theorem tensorAdelicCuspidalToCuspidal_injective :
    Function.Injective
      (tensorAdelicCuspidalToCuspidal F G Kinf rho hsmooth hcalc hPD hG hrho hK hN) :=
  fun _ _ h => Subtype.ext (congrArg
    (fun f : AdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN => f.val) h)

def tensorAdelicCuspidalToContinuous :
    TensorAdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN →ₗ[ℂ]
      ContinuousRationalFunctions F G :=
  (adelicCuspidalToContinuous F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).comp
    (tensorAdelicCuspidalToCuspidal F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toLinearMap

/-- Convergence is established independently of the zero constant-term condition. -/
theorem tensorAdelicCuspidal_constantTerm_convergent
    (f : TensorAdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN)
    (P : ProperRationalParabolic G) :
    HasConvergentConstantTerm F G (properRationalParabolicRadicals hPD hG P)
      (properParabolicQuotientMeasure F G hPD hG P)
      (tensorAdelicCuspidalToContinuous F G Kinf rho hsmooth hcalc hPD hG hrho hK hN f) :=
  adelicCuspidal_constantTerm_convergent F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
    (tensorAdelicCuspidalToCuspidal F G Kinf rho hsmooth hcalc hPD hG hrho hK hN f) P

theorem tensorAdelicCuspidal_hasFiniteLevel
    (f : TensorAdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN) :
    HasFiniteLevel F G
      (tensorAdelicCuspidalToContinuous F G Kinf rho hsmooth hcalc hPD hG hrho hK hN f) :=
  adelicCuspidal_hasFiniteLevel F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
    (tensorAdelicCuspidalToCuspidal F G Kinf rho hsmooth hcalc hPD hG hrho hK hN f)

variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)

local notation "Q" => PositiveRationalQuotient F G T i

/-- Tensor membership of the actual positive-quotient pullback is separately imposed. -/
def tensorPositiveQuotientSubrepresentation :
    Subrepresentation (continuousPositiveQuotientFiniteRightAction F G T i) where
  toSubmodule := (tensorSmoothSubrepresentation F G).toSubmodule.comap
    (positiveQuotientContinuousPullback F G T i)
  apply_mem_toSubmodule c f hf := by
    change positiveQuotientContinuousPullback F G T i
      (continuousPositiveQuotientRightAction F G T i (AdelicGroupPoints.ofFinite F G c) f) ∈
        (tensorSmoothSubrepresentation F G).toSubmodule
    rw [positiveQuotientContinuousPullback_rightAction]
    exact (tensorSmoothSubrepresentation F G).apply_mem_toSubmodule
      (AdelicGroupPoints.ofFinite F G c) hf

variable (measureQ : Measure (PositiveRationalQuotient F G T i))
  (hInvariant : QuotientMeasureRightInvariant F G T i measureQ)

/-- The actual earlier quotient cusp-form L² construction restricted by literal tensor smoothness. -/
def positiveTensorCuspidalFormL2Subrepresentation :
    Subrepresentation (continuousPositiveQuotientFiniteRightAction F G T i) where
  toSubmodule :=
    (positiveCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      measureQ hInvariant).toSubmodule ⊓
        (tensorPositiveQuotientSubrepresentation F G T i).toSubmodule
  apply_mem_toSubmodule c _f hf :=
    ⟨(positiveCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      measureQ hInvariant).apply_mem_toSubmodule c hf.1,
      (tensorPositiveQuotientSubrepresentation F G T i).apply_mem_toSubmodule c hf.2⟩

abbrev PositiveTensorCuspidalFormL2Functions :=
  (positiveTensorCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
    measureQ hInvariant).toSubmodule

def positiveTensorCuspidalFormL2FiniteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G)
      (PositiveTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
        measureQ hInvariant) :=
  (positiveTensorCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
    measureQ hInvariant).toRepresentation

/-- The quotient representative pulls back to an original tensor cusp form and has genuine MemLp2. -/
theorem mem_positiveTensorCuspidalFormL2Subrepresentation (f : C(Q, ℂ)) :
    f ∈ positiveTensorCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
        measureQ hInvariant ↔
      (∃ phi : TensorAdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN,
        tensorAdelicCuspidalToContinuous F G Kinf rho hsmooth hcalc hPD hG hrho hK hN phi =
          positiveQuotientContinuousPullback F G T i f) ∧ MemLp f 2 measureQ := by
  constructor
  · rintro ⟨⟨⟨phi, hphi⟩, hlp⟩, htensor⟩
    have ht : phi.val.val ∈ tensorSmoothSubrepresentation F G := by
      change positiveQuotientContinuousPullback F G T i f ∈ tensorSmoothSubrepresentation F G at htensor
      rw [← hphi] at htensor
      exact htensor
    let psi : TensorAdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN :=
      ⟨phi.val, ⟨⟨phi.property.1, ht⟩, phi.property.2⟩⟩
    exact ⟨⟨psi, hphi⟩, hlp⟩
  · rintro ⟨⟨phi, hphi⟩, hlp⟩
    refine ⟨⟨⟨tensorAdelicCuspidalToCuspidal F G Kinf rho hsmooth hcalc hPD hG hrho hK hN phi,
      hphi⟩, hlp⟩, ?_⟩
    change positiveQuotientContinuousPullback F G T i f ∈ tensorSmoothSubrepresentation F G
    rw [← hphi]
    exact phi.property.1.2

/-- The tensor restriction forgets to the exact earlier quotient L² construction equivariantly. -/
def positiveTensorCuspidalFormL2ToCuspidal :
    (positiveTensorCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      measureQ hInvariant).IntertwiningMap
      (positiveCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
        measureQ hInvariant) where
  toLinearMap :=
    (positiveTensorCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      measureQ hInvariant).toSubmodule.inclusion (by intro _ hf; exact hf.1)
  isIntertwining' _ := by ext; rfl

/-- The resulting class is in the actual quotient Lp2 and uses the unchanged original map. -/
def positiveTensorCuspidalFormL2ToLp :
    (positiveTensorCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      measureQ hInvariant).IntertwiningMap (quotientL2FiniteRightAction F G T i measureQ hInvariant) :=
  (positiveCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
    measureQ hInvariant).comp
      (positiveTensorCuspidalFormL2ToCuspidal F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
        measureQ hInvariant)

theorem coeFn_positiveTensorCuspidalFormL2ToLp
    (f : PositiveTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      measureQ hInvariant) :
    positiveTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
        measureQ hInvariant f =ᵐ[measureQ] (f.val : Q → ℂ) :=
  coeFn_positiveCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
    measureQ hInvariant
    (positiveTensorCuspidalFormL2ToCuspidal F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      measureQ hInvariant f)

/-- Full support makes this actual continuous quotient realization faithful. -/
theorem positiveTensorCuspidalFormL2ToLp_injective [measureQ.IsOpenPosMeasure] :
    Function.Injective
      (positiveTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
        measureQ hInvariant) := by
  intro f g h
  have he := positiveCuspidalFormL2ToLp_injective F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
    measureQ hInvariant h
  exact Subtype.ext (congrArg
    (fun z : PositiveCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      measureQ hInvariant => z.val) he)

/-- The algebraic tensor-cusp image retains the actual quotient finite action. -/
def tensorCuspidalFormQuotientL2Image :
    Subrepresentation (quotientL2FiniteRightAction F G T i measureQ hInvariant) :=
  (positiveTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
    measureQ hInvariant).range

end Langlands.Automorphic.GroupSchemeFunctions
