import Langlands.Automorphic.GroupSchemeForms
import Langlands.Automorphic.GroupSchemeParabolicMeasure
import Langlands.Global.AdelicSubgroupHaarNormalization

/-! # Normalized parabolic vanishing on the broader finite-smooth form carrier -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme

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

local instance cuspFiniteSmoothAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- Actual forms whose normalized constant term vanishes for every proper rational parabolic. -/
def adelicCuspidalSubrepresentation :
    Subrepresentation (finitePlotSmoothFiniteRightAction F G) where
  toSubmodule :=
    (adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule ⊓
      (normalizedParabolicCuspidalSubrepresentation F G hPD hG).toSubmodule.comap
        (finitePlotSmoothRationalSubrepresentation F G).toSubmodule.subtype
  apply_mem_toSubmodule c _f hf :=
    ⟨(adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).apply_mem_toSubmodule c hf.1,
      (normalizedParabolicCuspidalSubrepresentation F G hPD hG).apply_mem_toSubmodule
        (AdelicGroupPoints.ofFinite F G c) hf.2⟩

/-- Membership displays every source condition and all actual mass-one constant terms. -/
theorem mem_adelicCuspidalSubrepresentation (f : FinitePlotSmoothRationalFunctions F G) :
    f ∈ adelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN ↔
      IsAdelicAutomorphicForm F G Kinf rho hsmooth hcalc f ∧
      ∀ (P : ProperRationalParabolic G) (g : AdelicGroupPoints F G),
        constantTerm F G (properRationalParabolicRadicals hPD hG P)
          (properParabolicQuotientMeasure F G hPD hG P) f.val g = 0 := by
  change (f ∈ adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN ∧
    f.val ∈ normalizedParabolicCuspidalSubrepresentation F G hPD hG) ↔ _
  rw [mem_adelicAutomorphicSubrepresentation,
    mem_normalizedParabolicCuspidalSubrepresentation_iff]

abbrev AdelicCuspidalForms :=
  (adelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule

def adelicCuspidalFiniteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G)
      (AdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN) :=
  (adelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toRepresentation

/-- The original form inclusion is injective and intertwines positive finite translation. -/
def adelicCuspidalToAutomorphic :
    (adelicCuspidalFiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).IntertwiningMap
      (adelicAutomorphicFiniteRightAction F G Kinf rho hsmooth hcalc hG hrho hK hN) where
  toLinearMap :=
    (adelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule.inclusion (by intro _ hf; exact hf.1)
  isIntertwining' _ := by ext; rfl

theorem adelicCuspidalToAutomorphic_injective :
    Function.Injective
      (adelicCuspidalToAutomorphic F G Kinf rho hsmooth hcalc hPD hG hrho hK hN) :=
  fun _ _ h => Subtype.ext (congrArg
    (fun s : AdelicAutomorphicForms F G Kinf rho hsmooth hcalc hG hrho hK hN => s.val) h)

/-- Faithful realization as the original continuous rational-invariant function. -/
def adelicCuspidalToContinuous :
    AdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN →ₗ[ℂ]
      ContinuousRationalFunctions F G :=
  (adelicAutomorphicToContinuous F G Kinf rho hsmooth hcalc hG hrho hK hN).comp
    (adelicCuspidalToAutomorphic F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toLinearMap

theorem adelicCuspidalToContinuous_injective :
    Function.Injective
      (adelicCuspidalToContinuous F G Kinf rho hsmooth hcalc hPD hG hrho hK hN) :=
  (adelicAutomorphicToContinuous_injective F G Kinf rho hsmooth hcalc hG hrho hK hN).comp
    (adelicCuspidalToAutomorphic_injective F G Kinf rho hsmooth hcalc hPD hG hrho hK hN)

@[simp]
theorem adelicCuspidalToContinuous_finiteRightAction
    (c : FiniteAdelicGroupPoints F G)
    (f : AdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN) :
    adelicCuspidalToContinuous F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        (adelicCuspidalFiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN c f) =
      finiteRightAction F G c
        (adelicCuspidalToContinuous F G Kinf rho hsmooth hcalc hPD hG hrho hK hN f) := rfl

/-- Compact radical quotients and normalized finite Borel measures give absolute convergence. -/
theorem adelicCuspidal_constantTerm_convergent
    (f : AdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN)
    (P : ProperRationalParabolic G) :
    HasConvergentConstantTerm F G (properRationalParabolicRadicals hPD hG P)
      (properParabolicQuotientMeasure F G hPD hG P)
      (adelicCuspidalToContinuous F G Kinf rho hsmooth hcalc hPD hG hrho hK hN f) :=
  hasConvergentNormalizedParabolicConstantTerm F G hPD hG P _

theorem adelicCuspidal_hasFiniteLevel
    (f : AdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN) :
    HasFiniteLevel F G
      (adelicCuspidalToContinuous F G Kinf rho hsmooth hcalc hPD hG hrho hK hN f) :=
  adelicAutomorphic_hasFiniteLevel F G Kinf rho hsmooth hcalc hG hrho hK hN
    (adelicCuspidalToAutomorphic F G Kinf rho hsmooth hcalc hPD hG hrho hK hN f)

theorem adelicCuspidalFiniteRightAction_isSmooth :
    Langlands.IsSmooth
      (adelicCuspidalFiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN) := by
  intro f
  obtain ⟨L, hL⟩ := f.val.property.2
  refine ⟨L, fun l => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hL l

/-- Every genuine initial Haar produces the identical normalized constant-term value. -/
theorem normalizedParabolicConstantTerm_initialHaar_independent
    (P : ProperRationalParabolic G)
    (ν : Measure (AdelicSubgroupPoints.adelicPoints F G (properRationalParabolicRadicals hPD hG P)))
    [ν.IsHaarMeasure] (f : ContinuousRationalFunctions F G) (g : AdelicGroupPoints F G) :
    constantTerm F G (properRationalParabolicRadicals hPD hG P)
        (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasureFrom F G _ ν) f g =
      constantTerm F G (properRationalParabolicRadicals hPD hG P)
        (properParabolicQuotientMeasure F G hPD hG P) f g := by
  rw [AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasureFrom_eq]
  rfl

/-- The optional uniform-growth refinement is formed inside the identical actual carrier. -/
def uniformAdelicCuspidalSubrepresentation :
    Subrepresentation (finitePlotSmoothFiniteRightAction F G) :=
  adelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN ⊓
    adelicUniformGrowthFiniteSubrepresentation F G rho hsmooth hcalc hN

end Langlands.Automorphic.GroupSchemeFunctions
