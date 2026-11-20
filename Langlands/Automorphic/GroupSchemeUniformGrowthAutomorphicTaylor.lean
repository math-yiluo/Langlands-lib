import Langlands.Analysis.HolomorphicFiniteRankTaylor
import Langlands.Automorphic.FullOperatorAction
import Langlands.Automorphic.GeneralLinearAdelicForms
import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.Automorphic.GroupSchemeUniformGrowthTaylor

/-! # Automorphy of Taylor vectors of regular automorphic curves -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G))

local instance : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

local notation "V" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "A" => FinitePlotSmoothRationalFunctions F G
local notation "P" => AdelicGroupPoints F G

private abbrev underlying (v : V) : A :=
  (v : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val

private def evaluateFunctions : A →ₗ[ℂ] (P → ℂ) where
  toFun v := evaluate F G v.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem evaluateFunctions_injective : Function.Injective (evaluateFunctions F G) :=
  fun _ _ h => Subtype.ext (Subtype.ext (Subtype.ext h))

private theorem finiteVector_iff_finiteEvaluationSpan {M : Type*} [Monoid M]
    (a : Representation ℂ M A) (v : A) :
    FiniteVectors.IsFiniteVector a v ↔
      FiniteDimensional ℂ (Submodule.span ℂ (range fun m => evaluateFunctions F G (a m v))) := by
  let S := FiniteVectors.orbitSpan a v
  have hS : Submodule.map (evaluateFunctions F G) S =
      Submodule.span ℂ (range fun m => evaluateFunctions F G (a m v)) := by
    change Submodule.map (evaluateFunctions F G) (Submodule.span ℂ (range fun m => a m v)) = _
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← hS]
  exact Module.Finite.equiv_iff
    (Submodule.equivMapOfInjective _ (evaluateFunctions_injective F G) S)

private theorem finiteVector_taylorCoefficient {M : Type*} [Monoid M]
    (a : Representation ℂ M A)
    (hEval : ∀ m x, ∃ test : V →L[ℂ] ℂ,
      ∀ v, test v = evaluateFunctions F G (a m (underlying F G rho hsmooth hcalc hN hrho R L v)) x)
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G))) {U W : Set ℂ}
    (hU : IsPreconnected U) (hUo : IsOpen U) (hW : IsOpen W) (hWU : W ⊆ U) (hne : W.Nonempty)
    (f : ℂ → V) (hf : ∀ test : V →L[ℂ] ℂ, DifferentiableOn ℂ (fun t => test (f t)) U)
    (hfin : ∀ t ∈ W, FiniteVectors.IsFiniteVector a
      (underlying F G rho hsmooth hcalc hN hrho R L (f t))) (z : U) (k : ℕ) :
    FiniteVectors.IsFiniteVector a (underlying F G rho hsmooth hcalc hN hrho R L
      (taylorCoefficient F G rho hsmooth hcalc hN hrho R L hL hUo f hf k z)) := by
  choose test htest using hEval
  let profile (m : M) (t : ℂ) :=
    evaluateFunctions F G (a m (underlying F G rho hsmooth hcalc hN hrho R L (f t)))
  have hprofile (m : M) (x : P) : (fun t => profile m t x) = fun t => test m x (f t) :=
    funext fun t => (htest m x (f t)).symm
  have ha (m : M) (x : P) : AnalyticOnNhd ℂ (fun t => profile m t x) U :=
    hprofile m x ▸ (hf (test m x)).analyticOnNhd hUo
  have hbound (t : ℂ) (ht : t ∈ W) :
      FiniteDimensional ℂ (Submodule.span ℂ (range fun m => profile m t)) :=
    (finiteVector_iff_finiteEvaluationSpan F G a _).mp (hfin t ht)
  have hrank := Langlands.Analysis.finiteDimensional_span_profileTaylor
    profile hU hUo hW hWU hne ha hbound z.property k
  apply (finiteVector_iff_finiteEvaluationSpan F G a _).mpr
  have heq : (fun m => evaluateFunctions F G (a m (underlying F G rho hsmooth hcalc hN hrho R L
      (taylorCoefficient F G rho hsmooth hcalc hN hrho R L hL hUo f hf k z)))) =
      fun m x => iteratedDeriv k (fun t => profile m t x) z.val / (k.factorial : ℂ) := by
    funext m x
    rw [← htest, apply_taylorCoefficient, hprofile]
  rw [heq]
  exact hrank

private theorem isCenterFinite_of_function {v : A}
    (h : IsCenterFiniteFunction F G hsmooth hcalc (evaluateFunctions F G v)) :
    IsAdelicCenterFinite F G hsmooth hcalc v := by
  obtain ⟨J, hJ, hvanish⟩ := h
  refine (isAdelicCenterFinite_iff_exists_ideal F G hsmooth hcalc v).mpr ⟨J, hJ, fun z hz => ?_⟩
  apply finitePlotSmoothSlice_injective F G
  funext b
  change finitePlotSmoothSlice F G b (finitePlotSmoothCenterAction F G hsmooth hcalc z v) =
    finitePlotSmoothSlice F G b 0
  rw [finitePlotSmoothSlice_centerAction, map_zero]
  exact hvanish z hz b (finitePlotSmoothSlice F G b v).property

/-- Actual Taylor coefficients of a weakly holomorphic growth-space curve
are automorphic when the values are automorphic on a nonempty open regular set. -/
theorem isAdelicAutomorphicForm_taylorCoefficient
    (K : Subgroup (InfiniteAdelicGroupPoints F G))
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G))) {U W : Set ℂ}
    (hU : IsPreconnected U) (hUo : IsOpen U) (hW : IsOpen W) (hWU : W ⊆ U) (hne : W.Nonempty)
    (f : ℂ → V) (hf : ∀ test : V →L[ℂ] ℂ, DifferentiableOn ℂ (fun t => test (f t)) U)
    (hform : ∀ t ∈ W, IsAutomorphicFunctionOn F G hsmooth hcalc
      (AdelicGroupPoints.rationalSubgroup F G) K rho
      (toFun F G rho hsmooth hcalc hN hrho R L (f t))) (z : U) (k : ℕ) :
    IsAdelicAutomorphicForm F G K rho hsmooth hcalc
      (underlying F G rho hsmooth hcalc hN hrho R L
        (taylorCoefficient F G rho hsmooth hcalc hN hrho R L hL hUo f hf k z)) := by
  refine ⟨?_, ?_, ?_⟩
  · apply finiteVector_taylorCoefficient F G rho hsmooth hcalc hN hrho R L
      (finitePlotSmoothInfiniteSubgroupAction F G K) ?_ hL hU hUo hW hWU hne f hf ?_ z k
    · intro m x
      use differentialEvaluation F G rho hsmooth hcalc hN hrho R L 1
        (x * AdelicGroupPoints.ofInfinite F G m.val)
      intro v
      rw [differentialEvaluation_apply, map_one, Module.End.one_apply]
      rfl
    · intro t ht
      apply (finiteVector_iff_finiteEvaluationSpan F G _ _).mpr
      exact (hform t ht).2.2.1
  · apply finiteVector_taylorCoefficient F G rho hsmooth hcalc hN hrho R L
      (adelicCenterAction F G hsmooth hcalc).toMonoidHom ?_ hL hU hUo hW hWU hne f hf ?_ z k
    · intro m x
      exact ⟨differentialEvaluation F G rho hsmooth hcalc hN hrho R L m.val x,
        differentialEvaluation_apply F G rho hsmooth hcalc hN hrho R L m.val x⟩
    · intro t ht
      exact isCenterFinite_of_function F G hsmooth hcalc (hform t ht).2.2.2.1
  · let v : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L :=
      taylorCoefficient F G rho hsmooth hcalc hN hrho R L hL hUo f hf k z
    obtain ⟨C, hC⟩ := v.property.2 1
    rw [map_one, Module.End.one_apply] at hC
    exact ⟨max C 1, zero_lt_one.trans_le (le_max_right _ _), R, fun x =>
      (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (RepresentationGrowth.adelicSourceNorm_pos F G rho hN x).le _))⟩

/-- Realize a Taylor coefficient in the actual adelic automorphic subrepresentation. -/
def adelicAutomorphicTaylorCoefficient
    (K : Subgroup (InfiniteAdelicGroupPoints F G))
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G))) {U W : Set ℂ}
    (hU : IsPreconnected U) (hUo : IsOpen U) (hW : IsOpen W) (hWU : W ⊆ U) (hne : W.Nonempty)
    (f : ℂ → V) (hf : ∀ test : V →L[ℂ] ℂ, DifferentiableOn ℂ (fun t => test (f t)) U)
    (hG : Langlands.GroupScheme.IsConnectedReductive G) (hK : Langlands.CompactIwasawa.IsMaximalCompact K)
    (hform : ∀ t ∈ W, IsAutomorphicFunctionOn F G hsmooth hcalc
      (AdelicGroupPoints.rationalSubgroup F G) K rho
      (toFun F G rho hsmooth hcalc hN hrho R L (f t))) (z : U) (k : ℕ) :
    AdelicAutomorphicForms F G K rho hsmooth hcalc hG hrho hK hN :=
  ⟨underlying F G rho hsmooth hcalc hN hrho R L
      (taylorCoefficient F G rho hsmooth hcalc hN hrho R L hL hUo f hf k z),
    (mem_adelicAutomorphicSubrepresentation F G K rho hsmooth hcalc hG hrho hK hN _).mpr
      (isAdelicAutomorphicForm_taylorCoefficient F G rho hsmooth hcalc hN hrho R L
        K hL hU hUo hW hWU hne f hf hform z k)⟩

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

namespace Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GL[" F "," n "]" =>
  Langlands.GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance : IsAffine (GL[F, n] : GroupScheme (Spec (CommRingCat.of F))).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

variable {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation GL[F, n] (Fin N))
  (hsmooth : SmoothOfRelativeDimension d (GL[F, n] : GroupScheme (Spec (CommRingCat.of F))).X.hom)
  (hcalc : AdelicDifferentialCommutator F GL[F, n] hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  (hG : Langlands.GroupScheme.IsConnectedReductive GL[F, n])
  (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F GL[F, n]))

local notation "V" => UniformGrowthFrechetSpace F GL[F, n] rho hsmooth hcalc hN hrho R L
local notation "K" => generalLinearStandardInfiniteCompact F n

/-- Transport an actual Taylor form to the original matrix operator module of `GL_n`. -/
def stableGeneralLinearTaylorCoefficient
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F GL[F, n]))) {U W : Set ℂ}
    (hU : IsPreconnected U) (hUo : IsOpen U) (hW : IsOpen W) (hWU : W ⊆ U) (hne : W.Nonempty)
    (f : ℂ → V) (hf : ∀ test : V →L[ℂ] ℂ, DifferentiableOn ℂ (fun t => test (f t)) U)
    (hform : ∀ t ∈ W, IsAutomorphicFunctionOn F GL[F, n] hsmooth hcalc
      (AdelicGroupPoints.rationalSubgroup F GL[F, n]) K rho
      (toFun F GL[F, n] rho hsmooth hcalc hN hrho R L (f t))) (z : U) (k : ℕ) :
    Langlands.Automorphic.StableAutomorphicFunctions F n :=
  (Langlands.Automorphic.stableAutomorphicEquiv F n).symm
    (adelicAutomorphicGeneralLinearMap F n rho hsmooth hcalc hrho hN hG
      (adelicAutomorphicTaylorCoefficient F GL[F, n] rho hsmooth hcalc hN hrho R L K hL
        hU hUo hW hWU hne f hf hG (generalLinearStandardInfiniteCompact_isMaximalCompact F n)
        hform z k))

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace
