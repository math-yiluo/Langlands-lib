import Langlands.Automorphic.GroupSchemeAdelicUniformGrowth
import Langlands.Global.FiniteAdelicGroupCompactOpen
import Langlands.Global.InfinitePlaceLeviIwasawaBaseChange
import Langlands.Representation.FiniteVectors
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Forms on the original general-reductive finite plot-smooth carrier -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

local instance formsFiniteSmoothAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

section CompactFiniteLevel

variable [LocallyOfFiniteType G.X.hom]

/-- Actual compact open existence shrinks every common open stabilizer to compact finite level. -/
theorem hasFiniteLevel_iff_mem_finiteSmooth (f : ContinuousRationalFunctions F G) :
    HasFiniteLevel F G f ↔ f ∈ finiteSmoothSubrepresentation F G := by
  refine ⟨hasFiniteLevel_mem_finiteSmooth F G f, ?_⟩
  rintro ⟨L, hL⟩
  let C := FiniteAdelicGroupPoints.compactOpenSubgroup F G
  refine ⟨(C ⊓ L).toSubgroup, (C ⊓ L).isOpen, ?_, ?_⟩
  · exact (FiniteAdelicGroupPoints.isCompact_compactOpenSubgroup F G).inter_right L.isClosed
  · intro l
    exact hL ⟨l.val, l.property.2⟩

theorem finitePlotSmooth_hasFiniteLevel (f : FinitePlotSmoothRationalFunctions F G) :
    HasFiniteLevel F G f.val :=
  (hasFiniteLevel_iff_mem_finiteSmooth F G f.val).mpr f.property.2

end CompactFiniteLevel

/-- The original right action restricted to the finite adelic factor. -/
def finitePlotSmoothFiniteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G) (FinitePlotSmoothRationalFunctions F G) :=
  (finitePlotSmoothRightAction F G).comp (AdelicGroupPoints.ofFinite F G).toMonoidHom

variable (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))

/-- The actual positive right action of a specified infinite subgroup. -/
def finitePlotSmoothInfiniteSubgroupAction :
    Representation ℂ Kinf (FinitePlotSmoothRationalFunctions F G) :=
  (finitePlotSmoothRightAction F G).comp
    ((AdelicGroupPoints.ofInfinite F G).toMonoidHom.comp Kinf.subtype)

/-- Finiteness of the full function's orbit, not independent finite bounds on each slice. -/
def IsAdelicInfiniteFinite (f : FinitePlotSmoothRationalFunctions F G) : Prop :=
  Langlands.FiniteVectors.IsFiniteVector (finitePlotSmoothInfiniteSubgroupAction F G Kinf) f

/-- The actual finite-vector subspace for the specified infinite subgroup. -/
def adelicInfiniteFiniteSubmodule : Submodule ℂ (FinitePlotSmoothRationalFunctions F G) :=
  (Langlands.FiniteVectors.subrepresentation
    (finitePlotSmoothInfiniteSubgroupAction F G Kinf)).toSubmodule

/-- Finite translation intertwines the whole infinite subgroup action. -/
def finitePlotSmoothInfiniteTranslate (c : FiniteAdelicGroupPoints F G) :
    (finitePlotSmoothInfiniteSubgroupAction F G Kinf).IntertwiningMap
      (finitePlotSmoothInfiniteSubgroupAction F G Kinf) where
  toLinearMap := finitePlotSmoothFiniteRightAction F G c
  isIntertwining' k := by
    have hcomm : Commute (AdelicGroupPoints.ofFinite F G c)
        (AdelicGroupPoints.ofInfinite F G k.val) := by
      change AdelicGroupPoints.ofFinite F G c * AdelicGroupPoints.ofInfinite F G k.val = _
      simp only [AdelicGroupPoints.ofFinite_eq_pair, AdelicGroupPoints.ofInfinite_eq_pair,
        AdelicGroupPoints.pair_mul, one_mul, mul_one]
    change finitePlotSmoothRightAction F G (AdelicGroupPoints.ofFinite F G c) *
        finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G k.val) =
      finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G k.val) *
        finitePlotSmoothRightAction F G (AdelicGroupPoints.ofFinite F G c)
    rw [← map_mul, ← map_mul, hcomm.eq]

theorem IsAdelicInfiniteFinite.finiteRightAction
    {f : FinitePlotSmoothRationalFunctions F G} (hf : IsAdelicInfiniteFinite F G Kinf f)
    (c : FiniteAdelicGroupPoints F G) :
    IsAdelicInfiniteFinite F G Kinf (finitePlotSmoothFiniteRightAction F G c f) :=
  hf.map (finitePlotSmoothInfiniteTranslate F G Kinf c)

variable {d N : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

/-- The actual associative center of the actual complex tangent enveloping algebra. -/
abbrev AdelicEnvelopingCenter := Subalgebra.center ℂ (AdelicEnvelopingAlgebra F G hsmooth)

/-- Restriction of the original differential action to its actual center. -/
def adelicCenterAction :
    AdelicEnvelopingCenter F G hsmooth →ₐ[ℂ]
      Module.End ℂ (FinitePlotSmoothRationalFunctions F G) :=
  (adelicEnvelopingAction F G hsmooth hcalc).comp
    (Subalgebra.center ℂ (AdelicEnvelopingAlgebra F G hsmooth)).val

/-- Finite dimensionality of the one actual global center orbit. -/
def IsAdelicCenterFinite (f : FinitePlotSmoothRationalFunctions F G) : Prop :=
  Langlands.FiniteVectors.IsFiniteVector (adelicCenterAction F G hsmooth hcalc).toMonoidHom f

def adelicCenterFiniteSubmodule : Submodule ℂ (FinitePlotSmoothRationalFunctions F G) :=
  (Langlands.FiniteVectors.subrepresentation
    (adelicCenterAction F G hsmooth hcalc).toMonoidHom).toSubmodule

/-- Evaluate the center action at one full adelic function. -/
def adelicCenterOrbitMap (f : FinitePlotSmoothRationalFunctions F G) :
    AdelicEnvelopingCenter F G hsmooth →ₗ[ℂ] FinitePlotSmoothRationalFunctions F G where
  toFun z := adelicCenterAction F G hsmooth hcalc z f
  map_add' _ _ := by simp [map_add, LinearMap.add_apply]
  map_smul' _ _ := by simp [map_smul, LinearMap.smul_apply]

/-- One ideal annihilates the original function at all arguments simultaneously. -/
def adelicCenterAnnihilator (f : FinitePlotSmoothRationalFunctions F G) :
    Ideal (AdelicEnvelopingCenter F G hsmooth) where
  carrier := {z | adelicCenterAction F G hsmooth hcalc z f = 0}
  zero_mem' := by simp
  add_mem' hz hw := by simp_all
  smul_mem' a z hz := by
    change adelicCenterAction F G hsmooth hcalc (a * z) f = 0
    rw [map_mul, Module.End.mul_apply, hz, map_zero]

/-- The common orbit equals the range of its linear orbit map. -/
theorem adelicCenterOrbitSpan_eq_range (f : FinitePlotSmoothRationalFunctions F G) :
    Langlands.FiniteVectors.orbitSpan (adelicCenterAction F G hsmooth hcalc).toMonoidHom f =
      LinearMap.range (adelicCenterOrbitMap F G hsmooth hcalc f) := by
  change Submodule.span ℂ (Set.range (adelicCenterOrbitMap F G hsmooth hcalc f)) = _
  exact Submodule.span_eq (LinearMap.range (adelicCenterOrbitMap F G hsmooth hcalc f))

/-- Source central finiteness is one finite-codimensional ideal for the entire function. -/
theorem isAdelicCenterFinite_iff_exists_ideal (f : FinitePlotSmoothRationalFunctions F G) :
    IsAdelicCenterFinite F G hsmooth hcalc f ↔
      ∃ J : Ideal (AdelicEnvelopingCenter F G hsmooth),
        Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ J.restrictScalars ℂ) ∧
        ∀ z ∈ J, adelicCenterAction F G hsmooth hcalc z f = 0 := by
  have hfinite : IsAdelicCenterFinite F G hsmooth hcalc f ↔
      Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸
        (adelicCenterAnnihilator F G hsmooth hcalc f).restrictScalars ℂ) := by
    change Module.Finite ℂ (Langlands.FiniteVectors.orbitSpan
      (adelicCenterAction F G hsmooth hcalc).toMonoidHom f) ↔ _
    rw [adelicCenterOrbitSpan_eq_range]
    change Module.Finite ℂ (LinearMap.range (adelicCenterOrbitMap F G hsmooth hcalc f)) ↔
      Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸
        LinearMap.ker (adelicCenterOrbitMap F G hsmooth hcalc f))
    exact (Module.Finite.equiv_iff
      (adelicCenterOrbitMap F G hsmooth hcalc f).quotKerEquivRange).symm
  constructor
  · intro hf
    exact ⟨adelicCenterAnnihilator F G hsmooth hcalc f, hfinite.mp hf, fun _ hz => hz⟩
  · rintro ⟨J, hJ, h⟩
    apply hfinite.mpr
    let := hJ
    have hle : J.restrictScalars ℂ ≤
        (adelicCenterAnnihilator F G hsmooth hcalc f).restrictScalars ℂ := h
    exact Module.Finite.of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)

/-- Finite right translation intertwines the actual entire center orbit. -/
def adelicCenterTranslate (c : FiniteAdelicGroupPoints F G) :
    Representation.IntertwiningMap (adelicCenterAction F G hsmooth hcalc).toMonoidHom
      (adelicCenterAction F G hsmooth hcalc).toMonoidHom where
  toLinearMap := finitePlotSmoothFiniteRightAction F G c
  isIntertwining' z := by
    apply LinearMap.ext
    intro f
    exact (finitePlotSmoothEnvelopingAction_finiteRightAction F G hsmooth hcalc z.val c f).symm

theorem IsAdelicCenterFinite.finiteRightAction
    {f : FinitePlotSmoothRationalFunctions F G} (hf : IsAdelicCenterFinite F G hsmooth hcalc f)
    (c : FiniteAdelicGroupPoints F G) :
    IsAdelicCenterFinite F G hsmooth hcalc (finitePlotSmoothFiniteRightAction F G c f) :=
  hf.map (adelicCenterTranslate F G hsmooth hcalc c)

/-- The broader form conditions on the original finite plot-smooth carrier.
No global finite-tensor condition from GH (6.1) is imposed or deduced here. -/
def IsAdelicAutomorphicForm (f : FinitePlotSmoothRationalFunctions F G) : Prop :=
  IsAdelicInfiniteFinite F G Kinf f ∧ IsAdelicCenterFinite F G hsmooth hcalc f ∧
    HasAdelicModerateGrowth F G rho f.val

/-- Finite-smooth forms for a specified maximal compact and closed matrix embedding.
The geometric premises are explicit and do not enter the group definition. -/
def adelicAutomorphicSubrepresentation
    (_hG : Langlands.GroupScheme.IsConnectedReductive G)
    (_hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
    (_hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf) (hN : 0 < N) :
    Subrepresentation (finitePlotSmoothFiniteRightAction F G) where
  toSubmodule := adelicInfiniteFiniteSubmodule F G Kinf ⊓
    (adelicCenterFiniteSubmodule F G hsmooth hcalc ⊓
      (adelicGrowthSubrepresentation F G rho hN).toSubmodule.comap
        (finitePlotSmoothRationalSubrepresentation F G).toSubmodule.subtype)
  apply_mem_toSubmodule c _f hf :=
    ⟨IsAdelicInfiniteFinite.finiteRightAction F G Kinf hf.1 c,
      IsAdelicCenterFinite.finiteRightAction F G hsmooth hcalc hf.2.1 c,
      (adelicGrowthSubrepresentation F G rho hN).apply_mem_toSubmodule
        (AdelicGroupPoints.ofFinite F G c) hf.2.2⟩

variable (hG : Langlands.GroupScheme.IsConnectedReductive G)
  (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf) (hN : 0 < N)

@[simp]
theorem mem_adelicAutomorphicSubrepresentation (f : FinitePlotSmoothRationalFunctions F G) :
    f ∈ adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN ↔
      IsAdelicAutomorphicForm F G Kinf rho hsmooth hcalc f := by
  change (IsAdelicInfiniteFinite F G Kinf f ∧ IsAdelicCenterFinite F G hsmooth hcalc f ∧
    f.val ∈ adelicGrowthSubrepresentation F G rho hN) ↔ _
  rw [mem_adelicGrowthSubrepresentation]
  rfl

abbrev AdelicAutomorphicForms :=
  (adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule

def adelicAutomorphicFiniteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G)
      (AdelicAutomorphicForms F G Kinf rho hsmooth hcalc hG hrho hK hN) :=
  (adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toRepresentation

/-- The form realization is the injective original-function inclusion. -/
def adelicAutomorphicToContinuous :
    AdelicAutomorphicForms F G Kinf rho hsmooth hcalc hG hrho hK hN →ₗ[ℂ]
      ContinuousRationalFunctions F G :=
  (finitePlotSmoothRationalSubrepresentation F G).toSubmodule.subtype.comp
    (adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN).toSubmodule.subtype

theorem adelicAutomorphicToContinuous_injective :
    Function.Injective (adelicAutomorphicToContinuous F G Kinf rho hsmooth hcalc hG hrho hK hN) :=
  Subtype.val_injective.comp Subtype.val_injective

@[simp]
theorem adelicAutomorphicToContinuous_finiteRightAction
    (c : FiniteAdelicGroupPoints F G)
    (f : AdelicAutomorphicForms F G Kinf rho hsmooth hcalc hG hrho hK hN) :
    adelicAutomorphicToContinuous F G Kinf rho hsmooth hcalc hG hrho hK hN
        (adelicAutomorphicFiniteRightAction F G Kinf rho hsmooth hcalc hG hrho hK hN c f) =
      finiteRightAction F G c
        (adelicAutomorphicToContinuous F G Kinf rho hsmooth hcalc hG hrho hK hN f) := rfl

/-- Every form has actual compact finite level; no supplied finite subgroup is needed. -/
theorem adelicAutomorphic_hasFiniteLevel
    (f : AdelicAutomorphicForms F G Kinf rho hsmooth hcalc hG hrho hK hN) :
    HasFiniteLevel F G
      (adelicAutomorphicToContinuous F G Kinf rho hsmooth hcalc hG hrho hK hN f) := by
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  exact finitePlotSmooth_hasFiniteLevel F G f.val

/-- The actual finite adelic form action has an open stabilizer at every vector. -/
theorem adelicAutomorphicFiniteRightAction_isSmooth :
    Langlands.IsSmooth
      (adelicAutomorphicFiniteRightAction F G Kinf rho hsmooth hcalc hG hrho hK hN) := by
  intro f
  obtain ⟨L, hL⟩ := f.val.property.2
  refine ⟨L, fun l => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hL l

include hG in
/-- Expand the implemented orbit/growth conditions with compact finite level.
This is not a comparison with the algebraic tensor carrier of GH (6.1). -/
theorem isAdelicAutomorphicForm_iff_source_conditions
    (f : FinitePlotSmoothRationalFunctions F G) :
    IsAdelicAutomorphicForm F G Kinf rho hsmooth hcalc f ↔
      HasFiniteLevel F G f.val ∧ IsAdelicInfiniteFinite F G Kinf f ∧
      (∃ J : Ideal (AdelicEnvelopingCenter F G hsmooth),
        Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ J.restrictScalars ℂ) ∧
        ∀ z ∈ J, adelicCenterAction F G hsmooth hcalc z f = 0) ∧
      HasAdelicModerateGrowth F G rho f.val := by
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  unfold IsAdelicAutomorphicForm
  rw [isAdelicCenterFinite_iff_exists_ideal]
  exact ⟨fun h => ⟨finitePlotSmooth_hasFiniteLevel F G f, h⟩, fun h => h.2⟩

/-- The uniform-growth refinement uses the same original form carrier. -/
def uniformAdelicAutomorphicSubrepresentation :
    Subrepresentation (finitePlotSmoothFiniteRightAction F G) :=
  adelicAutomorphicSubrepresentation F G Kinf rho hsmooth hcalc hG hrho hK hN ⊓
    adelicUniformGrowthFiniteSubrepresentation F G rho hsmooth hcalc hN

end Langlands.Automorphic.GroupSchemeFunctions
