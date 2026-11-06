import Langlands.Automorphic.GroupSchemeTensorSmooth
import Langlands.Automorphic.GroupSchemeLocallyConstantFiniteLevel
import Langlands.Automorphic.GroupSchemeCompactFiniteness

/-! # Tensor-smooth forms with actual full compact finiteness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  (C : OpenSubgroup (FiniteAdelicGroupPoints F G))

local instance tensorFormsContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

local instance tensorFormsFinitePlotAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- The actual Kinf*C subgroup acts on the unchanged continuous rational functions. -/
def continuousActualCompactAction :
    Representation ℂ (adelicCompactProductSubgroup F G Kinf C)
      (ContinuousRationalFunctions F G) :=
  (continuousRightAction F G).comp (adelicCompactProductSubgroup F G Kinf C).subtype

/-- The original finite-smooth inclusion intertwines restriction to the actual full subgroup. -/
def finitePlotSmoothToContinuousActualCompact :
    (finitePlotSmoothActualCompactAction F G Kinf C).IntertwiningMap
      (continuousActualCompactAction F G Kinf C) where
  toLinearMap := (finitePlotSmoothRationalSubrepresentation F G).toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

/-- Finiteness in the original carrier is exactly full compact finiteness in the continuous carrier. -/
theorem isAdelicInfiniteFinite_iff_continuousActualCompactFinite
    (hC : IsCompact (C : Set (FiniteAdelicGroupPoints F G)))
    (f : FinitePlotSmoothRationalFunctions F G) :
    IsAdelicInfiniteFinite F G Kinf f ↔
      Langlands.FiniteVectors.IsFiniteVector (continuousActualCompactAction F G Kinf C) f.val := by
  rw [isAdelicInfiniteFinite_iff_actualCompactFinite F G Kinf C hC]
  exact (Langlands.FiniteVectors.isFiniteVector_map_iff
    (finitePlotSmoothToContinuousActualCompact F G Kinf C) Subtype.val_injective f).symm

/-- Full compact finiteness includes finiteness for the specified finite subgroup. -/
theorem continuousFiniteSubgroupFinite_of_actualCompactFinite
    (f : ContinuousRationalFunctions F G)
    (hf : Langlands.FiniteVectors.IsFiniteVector (continuousActualCompactAction F G Kinf C) f) :
    Langlands.FiniteVectors.IsFiniteVector (continuousFiniteSubgroupAction F G C) f := by
  let S := Langlands.FiniteVectors.orbitSpan (continuousActualCompactAction F G Kinf C) f
  let : Module.Finite ℂ S := hf
  apply Submodule.finiteDimensional_of_le (S₂ := S)
  apply Submodule.span_le.mpr
  rintro _ ⟨c, rfl⟩
  let k : adelicCompactProductSubgroup F G Kinf C :=
    ⟨AdelicGroupPoints.ofFinite F G c.val,
      ⟨(1, c.val), ⟨Kinf.one_mem, c.property⟩, rfl⟩⟩
  exact Langlands.FiniteVectors.action_mem_orbitSpan
    (continuousActualCompactAction F G Kinf C) k f

/-- Every actual tensor-smooth full-compact-finite function has actual compact finite level. -/
theorem tensorActualCompactFinite_hasFiniteLevel
    (hC : IsCompact (C : Set (FiniteAdelicGroupPoints F G)))
    (f : ContinuousRationalFunctions F G) (htensor : f ∈ tensorSmoothSubrepresentation F G)
    (hfin : Langlands.FiniteVectors.IsFiniteVector (continuousActualCompactAction F G Kinf C) f) :
    HasFiniteLevel F G f :=
  hasFiniteLevel_of_finiteLocallyConstant_finiteVector F G C hC f
    (tensorSmooth_le_plotSmooth F G htensor).2
    (continuousFiniteSubgroupFinite_of_actualCompactFinite F G Kinf C f hfin)

/-- The original function acquires the earlier finite-smooth carrier without assuming its level. -/
def tensorCompactToFinitePlotSmooth
    (hC : IsCompact (C : Set (FiniteAdelicGroupPoints F G)))
    (f : ContinuousRationalFunctions F G) (htensor : f ∈ tensorSmoothSubrepresentation F G)
    (hfin : Langlands.FiniteVectors.IsFiniteVector (continuousActualCompactAction F G Kinf C) f) :
    FinitePlotSmoothRationalFunctions F G :=
  ⟨f, (tensorSmooth_le_plotSmooth F G htensor).1,
    hasFiniteLevel_mem_finiteSmooth F G f
      (tensorActualCompactFinite_hasFiniteLevel F G Kinf C hC f htensor hfin)⟩

@[simp]
theorem tensorCompactToFinitePlotSmooth_val
    (hC : IsCompact (C : Set (FiniteAdelicGroupPoints F G)))
    (f : ContinuousRationalFunctions F G) (htensor : f ∈ tensorSmoothSubrepresentation F G)
    (hfin : Langlands.FiniteVectors.IsFiniteVector (continuousActualCompactAction F G Kinf C) f) :
    (tensorCompactToFinitePlotSmooth F G Kinf C hC f htensor hfin).val = f := rfl

/-- The original carrier omits no function satisfying tensor smoothness and full compact finiteness. -/
theorem tensorCompactToFinitePlotSmooth_infiniteFinite
    (hC : IsCompact (C : Set (FiniteAdelicGroupPoints F G)))
    (f : ContinuousRationalFunctions F G) (htensor : f ∈ tensorSmoothSubrepresentation F G)
    (hfin : Langlands.FiniteVectors.IsFiniteVector (continuousActualCompactAction F G Kinf C) f) :
    IsAdelicInfiniteFinite F G Kinf
      (tensorCompactToFinitePlotSmooth F G Kinf C hC f htensor hfin) :=
  (isAdelicInfiniteFinite_iff_continuousActualCompactFinite F G Kinf C hC _).mpr hfin

variable {d N : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hG : Langlands.GroupScheme.IsConnectedReductive G)
  (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf) (hN : 0 < N)

/-- The original broader form space restricted by literal algebraic-tensor membership. -/
def tensorAdelicAutomorphicSubrepresentation :
    Subrepresentation (finitePlotSmoothFiniteRightAction F G) where
  toSubmodule :=
    (adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule ⊓
      (tensorSmoothSubrepresentation F G).toSubmodule.comap
        (finitePlotSmoothRationalSubrepresentation F G).toSubmodule.subtype
  apply_mem_toSubmodule c _f hf :=
    ⟨(adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).apply_mem_toSubmodule c hf.1,
      (tensorSmoothSubrepresentation F G).apply_mem_toSubmodule
        (AdelicGroupPoints.ofFinite F G c) hf.2⟩

/-- The displayed tensor, full compact, center and growth conditions are exact on original functions. -/
theorem mem_tensorAdelicAutomorphicSubrepresentation_iff
    (hC : IsCompact (C : Set (FiniteAdelicGroupPoints F G)))
    (f : FinitePlotSmoothRationalFunctions F G) :
    f ∈ tensorAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN ↔
      f.val ∈ tensorSmoothSubrepresentation F G ∧
      Langlands.FiniteVectors.IsFiniteVector (continuousActualCompactAction F G Kinf C) f.val ∧
      IsAdelicCenterFinite F G hsmooth hcalc f ∧ HasAdelicModerateGrowth F G rho f.val := by
  change (f ∈ adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN ∧
    f.val ∈ tensorSmoothSubrepresentation F G) ↔ _
  rw [mem_adelicAutomorphicSubrepresentation]
  unfold IsAdelicAutomorphicForm
  rw [isAdelicInfiniteFinite_iff_continuousActualCompactFinite F G Kinf C hC]
  tauto

abbrev TensorAdelicAutomorphicForms :=
  (tensorAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule

def tensorAdelicAutomorphicFiniteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G)
      (TensorAdelicAutomorphicForms F G Kinf rho hsmooth hcalc hG hrho hK hN) :=
  (tensorAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toRepresentation

/-- The source tensor restriction has a faithful original-function form inclusion. -/
def tensorAdelicAutomorphicToAutomorphic :
    (tensorAdelicAutomorphicFiniteRightAction F G Kinf rho hsmooth hcalc hG hrho hK hN).IntertwiningMap
      (adelicAutomorphicFiniteRightAction F G Kinf rho hsmooth hcalc hG hrho hK hN) where
  toLinearMap :=
    (tensorAdelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule.inclusion
      (by intro _ hf; exact hf.1)
  isIntertwining' _ := by ext; rfl

theorem tensorAdelicAutomorphicToAutomorphic_injective :
    Function.Injective
      (tensorAdelicAutomorphicToAutomorphic F G Kinf rho hsmooth hcalc hG hrho hK hN) :=
  fun _ _ h => Subtype.ext (congrArg
    (fun f : AdelicAutomorphicForms F G Kinf rho hsmooth hcalc hG hrho hK hN => f.val) h)

/-- Tensor-restricted forms inherit actual compact finite level on the same functions. -/
theorem tensorAdelicAutomorphic_hasFiniteLevel
    (f : TensorAdelicAutomorphicForms F G Kinf rho hsmooth hcalc hG hrho hK hN) :
    HasFiniteLevel F G f.val.val :=
  adelicAutomorphic_hasFiniteLevel F G Kinf rho hsmooth hcalc hG hrho hK hN
    (tensorAdelicAutomorphicToAutomorphic F G Kinf rho hsmooth hcalc hG hrho hK hN f)

/-- Their finite adelic action is smooth, with the same actual open stabilizer. -/
theorem tensorAdelicAutomorphicFiniteRightAction_isSmooth :
    Langlands.IsSmooth
      (tensorAdelicAutomorphicFiniteRightAction F G Kinf rho hsmooth hcalc hG hrho hK hN) := by
  intro f
  obtain ⟨L, hL⟩ := f.val.property.2
  refine ⟨L, fun l => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hL l

end Langlands.Automorphic.GroupSchemeFunctions
