import Langlands.Automorphic.GroupSchemeAdelicGrowth
import Langlands.Automorphic.GroupSchemeEnvelopingAction

/-! # One full adelic exponent for every actual enveloping derivative -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.Geometry.Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)

/-- The actual tangent enveloping algebra, with the original chosen smooth atlas. -/
abbrev AdelicEnvelopingAlgebra :=
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  UniversalEnvelopingAlgebra ℂ
    (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)))

/-- The unchanged exact scalar-commutator prerequisite for this chosen atlas. -/
abbrev AdelicDifferentialCommutator : Prop :=
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)

local instance uniformFiniteSmoothAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

local notation "UEA" => AdelicEnvelopingAlgebra F G hsmooth

variable (hcalc : AdelicDifferentialCommutator F G hsmooth)

/-- Definitional abbreviation for the original actual enveloping action. -/
abbrev adelicEnvelopingAction :
    UEA →ₐ[ℂ] Module.End ℂ (FinitePlotSmoothRationalFunctions F G) :=
  finitePlotSmoothEnvelopingAction F G hsmooth hcalc

/-- The source one-exponent bound extended to the original finite plot-smooth carrier.
The algebraic tensor condition of GH (6.1) is not imposed here. -/
def HasAdelicUniformModerateGrowth (f : FinitePlotSmoothRationalFunctions F G) : Prop :=
  ∃ r : ℝ, ∀ a : UEA, ∃ C : ℝ, 0 < C ∧ ∀ g : AdelicGroupPoints F G,
    ‖evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a f).val g‖ ≤
      C * RepresentationGrowth.adelicSourceNorm F G rho g ^ r

/-- One natural exponent for the dimension-scaled height, shared by all derivatives. -/
def HasAdelicUniformPolynomialGrowth (f : FinitePlotSmoothRationalFunctions F G) : Prop :=
  ∃ e : ℕ, ∀ a : UEA, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : AdelicGroupPoints F G,
    ‖evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a f).val g‖ ≤
      C * RepresentationGrowth.adelicHeight F G rho g ^ e

/-- Conversion chooses the exponent before the enveloping element, in both directions. -/
theorem hasAdelicUniformModerateGrowth_iff (hN : 0 < N)
    (f : FinitePlotSmoothRationalFunctions F G) :
    HasAdelicUniformModerateGrowth F G rho hsmooth hcalc f ↔
      HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc f := by
  let K : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
  have hK : 0 < K := pow_pos (by exact_mod_cast hN) _
  have hn0 (g) : 0 ≤ RepresentationGrowth.adelicHeight F G rho g :=
    zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN g)
  have hscale (g) : RepresentationGrowth.adelicHeight F G rho g =
      K * RepresentationGrowth.adelicSourceNorm F G rho g :=
    RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho g
  have hsource (g) : RepresentationGrowth.adelicSourceNorm F G rho g =
      K⁻¹ * RepresentationGrowth.adelicHeight F G rho g := by
    rw [hscale, ← mul_assoc, inv_mul_cancel₀ hK.ne', one_mul]
  constructor
  · rintro ⟨r, hf⟩
    obtain ⟨e, he⟩ := exists_nat_ge r
    refine ⟨e, fun a => ?_⟩
    obtain ⟨C, hC, hbound⟩ := hf a
    have hcoef : 0 ≤ C * (K⁻¹) ^ r :=
      mul_nonneg hC.le (Real.rpow_nonneg (inv_nonneg.mpr hK.le) r)
    refine ⟨C * (K⁻¹) ^ r, hcoef, fun g => ?_⟩
    calc
      _ ≤ C * RepresentationGrowth.adelicSourceNorm F G rho g ^ r := hbound g
      _ = (C * (K⁻¹) ^ r) * RepresentationGrowth.adelicHeight F G rho g ^ r := by
        rw [hsource, Real.mul_rpow (inv_nonneg.mpr hK.le) (hn0 g)]
        ring
      _ ≤ (C * (K⁻¹) ^ r) * RepresentationGrowth.adelicHeight F G rho g ^ e := by
        apply mul_le_mul_of_nonneg_left _ hcoef
        simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le
          (RepresentationGrowth.one_le_adelicHeight F G rho hN g) he
  · rintro ⟨e, hf⟩
    refine ⟨(e : ℝ), fun a => ?_⟩
    obtain ⟨C, hC, hbound⟩ := hf a
    refine ⟨(C + 1) * K ^ e, mul_pos (by linarith) (pow_pos hK e), fun g => ?_⟩
    rw [Real.rpow_natCast]
    calc
      _ ≤ C * RepresentationGrowth.adelicHeight F G rho g ^ e := hbound g
      _ ≤ (C + 1) * RepresentationGrowth.adelicHeight F G rho g ^ e :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (hn0 g) e)
      _ = ((C + 1) * K ^ e) * RepresentationGrowth.adelicSourceNorm F G rho g ^ e := by
        rw [hscale, mul_pow]
        ring

variable {F G rho hsmooth hcalc}

theorem HasAdelicUniformPolynomialGrowth.zero :
    HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc 0 := by
  refine ⟨0, fun a => ⟨0, le_refl 0, fun g => ?_⟩⟩
  simp only [map_zero]
  simp [evaluate]

theorem HasAdelicUniformPolynomialGrowth.add (hN : 0 < N)
    {f h : FinitePlotSmoothRationalFunctions F G}
    (hf : HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc f)
    (hh : HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc h) :
    HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc (f + h) := by
  obtain ⟨e, hf⟩ := hf
  obtain ⟨k, hh⟩ := hh
  refine ⟨max e k, fun a => ?_⟩
  obtain ⟨C, hC, hf⟩ := hf a
  obtain ⟨D, hD, hh⟩ := hh a
  refine ⟨C + D, add_nonneg hC hD, fun g => ?_⟩
  have h1 := RepresentationGrowth.one_le_adelicHeight F G rho hN g
  rw [map_add]
  calc
    _ ≤ ‖evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a f).val g‖ +
        ‖evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a h).val g‖ :=
      norm_add_le _ _
    _ ≤ C * RepresentationGrowth.adelicHeight F G rho g ^ e +
        D * RepresentationGrowth.adelicHeight F G rho g ^ k := add_le_add (hf g) (hh g)
    _ ≤ C * RepresentationGrowth.adelicHeight F G rho g ^ max e k +
        D * RepresentationGrowth.adelicHeight F G rho g ^ max e k :=
      add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (le_max_left e k)) hC)
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (le_max_right e k)) hD)
    _ = (C + D) * RepresentationGrowth.adelicHeight F G rho g ^ max e k :=
      (add_mul _ _ _).symm

theorem HasAdelicUniformPolynomialGrowth.smul
    {f : FinitePlotSmoothRationalFunctions F G}
    (hf : HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc f) (z : ℂ) :
    HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc (z • f) := by
  obtain ⟨e, hf⟩ := hf
  refine ⟨e, fun a => ?_⟩
  obtain ⟨C, hC, hf⟩ := hf a
  refine ⟨‖z‖ * C, mul_nonneg (norm_nonneg _) hC, fun g => ?_⟩
  rw [map_smul]
  calc
    _ = ‖z‖ * ‖evaluate F G
        (adelicEnvelopingAction F G hsmooth hcalc a f).val g‖ := norm_mul _ _
    _ ≤ ‖z‖ * (C * RepresentationGrowth.adelicHeight F G rho g ^ e) :=
      mul_le_mul_of_nonneg_left (hf g) (norm_nonneg _)
    _ = (‖z‖ * C) * RepresentationGrowth.adelicHeight F G rho g ^ e :=
      (mul_assoc _ _ _).symm

/-- Acting by another enveloping element preserves the same shared exponent. -/
theorem HasAdelicUniformPolynomialGrowth.envelopingAction
    {f : FinitePlotSmoothRationalFunctions F G}
    (hf : HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc f) (b : UEA) :
    HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc
      (adelicEnvelopingAction F G hsmooth hcalc b f) := by
  obtain ⟨e, hf⟩ := hf
  refine ⟨e, fun a => ?_⟩
  simpa only [map_mul, Module.End.mul_apply] using hf (a * b)

/-- The original full-growth condition follows by taking the identity differential. -/
theorem HasAdelicUniformPolynomialGrowth.polynomialGrowth
    {f : FinitePlotSmoothRationalFunctions F G}
    (hf : HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc f) :
    HasAdelicPolynomialGrowth F G rho f.val := by
  obtain ⟨e, hf⟩ := hf
  obtain ⟨C, hC, hf⟩ := hf (1 : UEA)
  refine ⟨C, hC, e, ?_⟩
  simpa only [map_one, Module.End.one_apply] using hf

/-- Every finite right translate preserves a common exponent for all derivatives. -/
theorem HasAdelicUniformPolynomialGrowth.finiteRightAction (hN : 0 < N)
    {f : FinitePlotSmoothRationalFunctions F G}
    (hf : HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc f)
    (c : FiniteAdelicGroupPoints F G) :
    HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc
      (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofFinite F G c) f) := by
  obtain ⟨e, hf⟩ := hf
  refine ⟨e, fun a => ?_⟩
  obtain ⟨C, hC, hf⟩ := hf a
  have hn0 (g) : 0 ≤ RepresentationGrowth.adelicHeight F G rho g :=
    zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN g)
  refine ⟨C * RepresentationGrowth.adelicHeight F G rho
      (AdelicGroupPoints.ofFinite F G c) ^ e,
    mul_nonneg hC (pow_nonneg (hn0 _) e), fun g => ?_⟩
  rw [finitePlotSmoothEnvelopingAction_finiteRightAction]
  calc
    _ ≤ C * RepresentationGrowth.adelicHeight F G rho
        (g * AdelicGroupPoints.ofFinite F G c) ^ e := hf _
    _ ≤ C * (RepresentationGrowth.adelicHeight F G rho g *
        RepresentationGrowth.adelicHeight F G rho (AdelicGroupPoints.ofFinite F G c)) ^ e :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hn0 _) (RepresentationGrowth.adelicHeight_mul_le
          F G rho hN g (AdelicGroupPoints.ofFinite F G c)) e) hC
    _ = (C * RepresentationGrowth.adelicHeight F G rho
        (AdelicGroupPoints.ofFinite F G c) ^ e) *
        RepresentationGrowth.adelicHeight F G rho g ^ e := by rw [mul_pow]; ring

variable (F G rho hsmooth hcalc)

/-- Uniform full adelic growth on the unchanged finite-smooth rational carrier. -/
def adelicUniformGrowthSubmodule (hN : 0 < N) :
    Submodule ℂ (FinitePlotSmoothRationalFunctions F G) where
  carrier := {f | HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc f}
  zero_mem' := HasAdelicUniformPolynomialGrowth.zero
  add_mem' := HasAdelicUniformPolynomialGrowth.add hN
  smul_mem' z _ hf := hf.smul z

@[simp]
theorem mem_adelicUniformGrowthSubmodule (hN : 0 < N)
    (f : FinitePlotSmoothRationalFunctions F G) :
    f ∈ adelicUniformGrowthSubmodule F G rho hsmooth hcalc hN ↔
      HasAdelicUniformModerateGrowth F G rho hsmooth hcalc f :=
  (hasAdelicUniformModerateGrowth_iff F G rho hsmooth hcalc hN f).symm

/-- Finite right translation gives a genuine subrepresentation of the original carrier. -/
def adelicUniformGrowthFiniteSubrepresentation (hN : 0 < N) :
    Subrepresentation ((finitePlotSmoothRightAction F G).comp
      (AdelicGroupPoints.ofFinite F G).toMonoidHom) where
  toSubmodule := adelicUniformGrowthSubmodule F G rho hsmooth hcalc hN
  apply_mem_toSubmodule c _f hf := hf.finiteRightAction hN c

/-- Restricting the actual enveloping action retains its algebra homomorphism laws. -/
def adelicUniformGrowthEnvelopingAction (hN : 0 < N) :
    UEA →ₐ[ℂ] Module.End ℂ (adelicUniformGrowthSubmodule F G rho hsmooth hcalc hN) :=
  { toFun := fun a =>
      { toFun := fun f => ⟨adelicEnvelopingAction F G hsmooth hcalc a f.val,
          f.property.envelopingAction a⟩
        map_add' := fun f h => Subtype.ext (map_add _ _ _)
        map_smul' := fun z f => Subtype.ext (map_smul _ _ _) }
    map_zero' := by ext f; simp only [map_zero, LinearMap.zero_apply]; rfl
    map_one' := by ext f; simp only [map_one, Module.End.one_apply]; rfl
    map_add' := by intros; ext f; simp only [map_add, LinearMap.add_apply]; rfl
    map_mul' := by intros; ext f; simp only [map_mul, Module.End.mul_apply]; rfl
    commutes' := by intro z; ext f; simp only [AlgHom.commutes, Module.algebraMap_end_apply]; rfl }

end Langlands.Automorphic.GroupSchemeFunctions
