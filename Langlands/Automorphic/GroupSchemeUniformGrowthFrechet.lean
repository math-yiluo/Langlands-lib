import Langlands.Automorphic.GroupSchemeAdelicUniformGrowth
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! # The Fréchet spaces of smooth functions of uniform moderate growth

Bernstein–Lapid §7.1: for `R > 0` and an open subgroup `L` of `G(𝔸_f)`, the smooth,
right `L`-invariant functions on `G(F) \ G(𝔸)` all of whose derivatives are bounded by a
multiple of the same weight form a Fréchet space, with one seminorm for every element of
the enveloping algebra. The weight here is the `R`-th power of the existing adelic norm
of a matrix representation; the growth predicate and the submodule are defined for every
representation, and the space carrying the topology requires a closed embedding. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

local instance uniformFrechetAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

local notation "UEA" => AdelicEnvelopingAlgebra F G hsmooth

/-- Every derivative is bounded by a multiple of the `R`-th power of the adelic norm, for
one fixed real exponent `R`. -/
def HasUniformGrowthExponent (R : ℝ) (f : FinitePlotSmoothRationalFunctions F G) : Prop :=
  ∀ a : UEA, ∃ C : ℝ, ∀ g : AdelicGroupPoints F G,
    ‖evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a f).val g‖ ≤
      C * RepresentationGrowth.adelicSourceNorm F G rho g ^ R

/-- Right invariance under every element of a subgroup of the finite adelic points. -/
def IsFixedByFiniteSubgroup (L : Subgroup (FiniteAdelicGroupPoints F G))
    (f : FinitePlotSmoothRationalFunctions F G) : Prop :=
  ∀ l ∈ L, finitePlotSmoothRightAction F G (AdelicGroupPoints.ofFinite F G l) f = f

/-- Right `L`-invariant functions whose derivatives all have growth exponent `R`. -/
def uniformGrowthLevelSubmodule (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G)) :
    Submodule ℂ (FinitePlotSmoothRationalFunctions F G) where
  carrier := {f | IsFixedByFiniteSubgroup F G L f ∧
    HasUniformGrowthExponent F G rho hsmooth hcalc R f}
  zero_mem' := by
    refine ⟨fun l _ => map_zero _, fun a => ⟨0, fun g => ?_⟩⟩
    simp [evaluate]
  add_mem' := by
    rintro f h ⟨hfL, hf⟩ ⟨hhL, hh⟩
    refine ⟨fun l hl => by rw [map_add, hfL l hl, hhL l hl], fun a => ?_⟩
    obtain ⟨C, hC⟩ := hf a
    obtain ⟨D, hD⟩ := hh a
    refine ⟨C + D, fun g => ?_⟩
    rw [map_add]
    calc
      _ ≤ ‖evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a f).val g‖ +
          ‖evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a h).val g‖ :=
        norm_add_le _ _
      _ ≤ C * RepresentationGrowth.adelicSourceNorm F G rho g ^ R +
          D * RepresentationGrowth.adelicSourceNorm F G rho g ^ R := add_le_add (hC g) (hD g)
      _ = (C + D) * RepresentationGrowth.adelicSourceNorm F G rho g ^ R := (add_mul _ _ _).symm
  smul_mem' := by
    rintro z f ⟨hfL, hf⟩
    refine ⟨fun l hl => by rw [map_smul, hfL l hl], fun a => ?_⟩
    obtain ⟨C, hC⟩ := hf a
    refine ⟨‖z‖ * C, fun g => ?_⟩
    rw [map_smul]
    calc
      _ = ‖z‖ * ‖evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a f).val g‖ :=
        norm_mul _ _
      _ ≤ ‖z‖ * (C * RepresentationGrowth.adelicSourceNorm F G rho g ^ R) :=
        mul_le_mul_of_nonneg_left (hC g) (norm_nonneg _)
      _ = (‖z‖ * C) * RepresentationGrowth.adelicSourceNorm F G rho g ^ R :=
        (mul_assoc _ _ _).symm

/-- The space of right `L`-invariant functions of uniform moderate growth with exponent `R`
for the height of a closed matrix embedding, as a type carrying the seminorm topology below. -/
def UniformGrowthFrechetSpace (_hN : 0 < N) (_hrho : GroupScheme.IsClosedSubgroup rho) (R : ℝ)
    (L : Subgroup (FiniteAdelicGroupPoints F G)) : Type u :=
  uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L

variable (hN : 0 < N) (hrho : GroupScheme.IsClosedSubgroup rho) (R : ℝ)
  (L : Subgroup (FiniteAdelicGroupPoints F G))

instance : AddCommGroup (UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L) :=
  inferInstanceAs (AddCommGroup (uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L))

instance : Module ℂ (UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L) :=
  inferInstanceAs (Module ℂ (uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L))

/-- The underlying function on the actual adelic points. -/
def UniformGrowthFrechetSpace.toFun
    (f : UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L) :
    AdelicGroupPoints F G → ℂ :=
  evaluate F G (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val.val

/-- The weighted derivative `g ↦ (a f)(g) ‖g‖^{-R}`, a bounded function on `G(𝔸)`. -/
def weightedDerivative (a : UEA)
    (f : UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L) :
    lp (fun _ : AdelicGroupPoints F G => ℂ) ∞ :=
  ⟨fun g => evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a
      (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val).val g *
      ((RepresentationGrowth.adelicSourceNorm F G rho g ^ R : ℝ) : ℂ)⁻¹,
    by
      obtain ⟨C, hC⟩ :=
        (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).property.2 a
      refine memℓp_infty ⟨C, ?_⟩
      rintro _ ⟨g, rfl⟩
      have hpos : 0 < RepresentationGrowth.adelicSourceNorm F G rho g ^ R :=
        Real.rpow_pos_of_pos (RepresentationGrowth.adelicSourceNorm_pos F G rho hN g) R
      simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      rw [← div_eq_mul_inv, div_le_iff₀ hpos]
      exact hC g⟩

/-- The Fréchet topology: the coarsest topology making every weighted derivative continuous
into the bounded functions with the supremum norm. -/
instance : TopologicalSpace (UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L) :=
  ⨅ a : UEA, TopologicalSpace.induced (weightedDerivative F G rho hsmooth hcalc hN hrho R L a)
    inferInstance

end Langlands.Automorphic.GroupSchemeFunctions
