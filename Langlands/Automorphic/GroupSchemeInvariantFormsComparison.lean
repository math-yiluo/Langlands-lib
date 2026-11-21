import Langlands.Automorphic.GroupSchemeInvariantFormsComparisonStatement

/-! # From actual scalar automorphic functions to the existing form carrier -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

local notation "A" => FinitePlotSmoothRationalFunctions F G
local notation "Points" => AdelicGroupPoints F G

local instance : AddCommGroup A := Module.addCommMonoidToAddCommGroup ℂ

/-- A rational-invariant smooth scalar function determines an element of
the original finite plot-smooth carrier by the same function. -/
def ofRationalSmoothFunction (φ : Points → ℂ)
    (hΓ : IsLeftInvariantUnder F G (AdelicGroupPoints.rationalSubgroup F G) φ)
    (hs : IsAdelicSmoothFunction F G φ) : A := by
  let f : ContinuousRationalFunctions F G :=
    ⟨⟨φ, fun q x => hΓ _ ⟨q, rfl⟩ x⟩, hs.1⟩
  refine ⟨f, (mem_infinitePlotSmoothSubrepresentation F G f).mpr hs.2.1, ?_⟩
  obtain ⟨L, hL, hl⟩ := hs.2.2
  refine ⟨⟨L, hL⟩, fun l => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact hl l l.property x

@[simp]
theorem evaluate_ofRationalSmoothFunction (φ : Points → ℂ)
    (hΓ : IsLeftInvariantUnder F G (AdelicGroupPoints.rationalSubgroup F G) φ)
    (hs : IsAdelicSmoothFunction F G φ) :
    evaluate F G (ofRationalSmoothFunction F G φ hΓ hs).val = φ := rfl

/-- Evaluation on the original finite plot-smooth carrier is an injective linear map. -/
def finitePlotSmoothEvaluation : A →ₗ[ℂ] (Points → ℂ) :=
  ⟨⟨fun f => evaluate F G f.val, fun _ _ => rfl⟩, fun _ _ => rfl⟩

theorem finitePlotSmoothEvaluation_injective :
    Function.Injective (finitePlotSmoothEvaluation F G) :=
  fun _ _ h => Subtype.ext (Subtype.ext (Subtype.ext h))

theorem isInfiniteSubgroupFiniteFunction_evaluate_iff (K : Subgroup (InfiniteAdelicGroupPoints F G))
    (f : A) :
    IsInfiniteSubgroupFiniteFunction F G K (evaluate F G f.val) ↔
      IsAdelicInfiniteFinite F G K f := by
  let S := FiniteVectors.orbitSpan (finitePlotSmoothInfiniteSubgroupAction F G K) f
  have hS : S.map (finitePlotSmoothEvaluation F G) =
      Submodule.span ℂ (Set.range fun k : K =>
        fun g => evaluate F G f.val (g * AdelicGroupPoints.ofInfinite F G k)) := by
    change (Submodule.span ℂ (Set.range _)).map _ = _
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  change Module.Finite ℂ (Submodule.span ℂ _) ↔ Module.Finite ℂ S
  rw [← hS]
  exact (Module.Finite.equiv_iff
    (Submodule.equivMapOfInjective _ (finitePlotSmoothEvaluation_injective F G) S)).symm

variable {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))

theorem isCenterFiniteFunction_evaluate_iff (f : A) :
    IsCenterFiniteFunction F G hsmooth hcalc (evaluate F G f.val) ↔
      IsAdelicCenterFinite F G hsmooth hcalc f := by
  rw [isAdelicCenterFinite_iff_exists_ideal]
  constructor
  · rintro ⟨J, hJ, h⟩
    refine ⟨J, hJ, fun z hz => ?_⟩
    apply finitePlotSmoothSlice_injective F G
    funext b
    change finitePlotSmoothSlice F G b (finitePlotSmoothCenterAction F G hsmooth hcalc z f) =
      finitePlotSmoothSlice F G b 0
    rw [finitePlotSmoothSlice_centerAction, map_zero]
    exact h z hz b (finitePlotSmoothSlice F G b f).property
  · rintro ⟨J, hJ, h⟩
    refine ⟨J, hJ, fun z hz b hs => ?_⟩
    change plotSmoothCenterAction F G hsmooth hcalc z (finitePlotSmoothSlice F G b f) = 0
    rw [← finitePlotSmoothSlice_centerAction]
    change finitePlotSmoothSlice F G b (adelicCenterAction F G hsmooth hcalc z f) = 0
    rw [h z hz, map_zero]

/-- The scalar predicates on an evaluated rational form agree with the
conditions on the original carrier. -/
theorem isAutomorphicFunctionOn_evaluate_iff (K : Subgroup (InfiniteAdelicGroupPoints F G)) (f : A) :
    IsAutomorphicFunctionOn F G hsmooth hcalc (AdelicGroupPoints.rationalSubgroup F G)
      K rho (evaluate F G f.val) ↔
      IsAdelicAutomorphicForm F G K rho hsmooth hcalc f := by
  rw [IsAutomorphicFunctionOn, IsAdelicAutomorphicForm,
    isInfiniteSubgroupFiniteFunction_evaluate_iff, isCenterFiniteFunction_evaluate_iff]
  constructor
  · exact fun h => h.2.2
  · intro h
    refine ⟨?_, ?_, h⟩
    · rintro x ⟨q, rfl⟩ g
      exact f.val.val.property q g
    · refine ⟨f.val.property, fun b => (finitePlotSmoothSlice F G b f).property, ?_⟩
      obtain ⟨L, hL⟩ := f.property.2
      refine ⟨L.toSubgroup, L.isOpen, fun l hl x => ?_⟩
      exact congrArg (fun v : ContinuousRationalFunctions F G => evaluate F G v x) (hL ⟨l, hl⟩)

/-- The actual comparison for rational-invariant scalar automorphic functions. -/
theorem rationalAutomorphicFunctionComparison : RationalAutomorphicFunctionComparisonStatement.{u} := by
  intro F _ _ G _ K N d rho hsmooth hcalc φ
  constructor
  · intro h
    let f := ofRationalSmoothFunction F G φ h.1 h.2.1
    exact ⟨f, rfl, (isAutomorphicFunctionOn_evaluate_iff F G hsmooth hcalc rho K f).mp h⟩
  · rintro ⟨f, rfl, h⟩
    exact (isAutomorphicFunctionOn_evaluate_iff F G hsmooth hcalc rho K f).mpr h

variable (K : Subgroup (InfiniteAdelicGroupPoints F G))
  (hG : Langlands.GroupScheme.IsConnectedReductive G)
  (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  (hK : Langlands.CompactIwasawa.IsMaximalCompact K) (hN : 0 < N)

/-- Scalar functions obtained by evaluating the original automorphic submodule. -/
def rationalAutomorphicFunctionSubmodule : Submodule ℂ (Points → ℂ) :=
  (adelicAutomorphicSubrepresentation F G K rho hsmooth hcalc hG hrho hK hN).toSubmodule.map
    (finitePlotSmoothEvaluation F G)

theorem mem_rationalAutomorphicFunctionSubmodule (φ : Points → ℂ) :
    φ ∈ rationalAutomorphicFunctionSubmodule F G hsmooth hcalc rho K hG hrho hK hN ↔
      IsAutomorphicFunctionOn F G hsmooth hcalc (AdelicGroupPoints.rationalSubgroup F G) K rho φ := by
  rw [rationalAutomorphicFunctionSubmodule, Submodule.mem_map,
    rationalAutomorphicFunctionComparison F G K rho hsmooth hcalc φ]
  constructor
  · rintro ⟨f, hf, hφ⟩
    exact ⟨f, hφ, (mem_adelicAutomorphicSubrepresentation F G K rho hsmooth hcalc
      hG hrho hK hN f).mp hf⟩
  · rintro ⟨f, hφ, hf⟩
    exact ⟨f, (mem_adelicAutomorphicSubrepresentation F G K rho hsmooth hcalc
      hG hrho hK hN f).mpr hf, hφ⟩

end Langlands.Automorphic.GroupSchemeFunctions
