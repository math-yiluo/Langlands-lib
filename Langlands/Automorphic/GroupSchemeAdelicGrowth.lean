import Langlands.Global.AdelicRepresentationHeight
import Langlands.Automorphic.GroupSchemePlotSmooth
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Full adelic moderate growth for actual rational-invariant functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N : ℕ} (rho : GroupScheme.MatrixRepresentation G (Fin N))

/-- One bound on all actual adelic arguments, for the dimension-scaled full height. -/
def HasAdelicPolynomialGrowth (f : ContinuousRationalFunctions F G) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ g : AdelicGroupPoints F G,
    ‖evaluate F G f g‖ ≤ C * RepresentationGrowth.adelicHeight F G rho g ^ d

/-- The real-exponent full adelic condition of GH 6.3.1 for the exact local-product norm.
The specified representation is a parameter; embedding independence is separate. -/
def HasAdelicModerateGrowth (f : ContinuousRationalFunctions F G) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, ∀ g : AdelicGroupPoints F G,
    ‖evaluate F G f g‖ ≤ C * RepresentationGrowth.adelicSourceNorm F G rho g ^ r

variable {F G rho}

theorem HasAdelicPolynomialGrowth.zero :
    HasAdelicPolynomialGrowth F G rho (0 : ContinuousRationalFunctions F G) :=
  ⟨0, le_refl 0, 0, by intro g; simp [evaluate]⟩

theorem HasAdelicPolynomialGrowth.add (hN : 0 < N)
    {f h : ContinuousRationalFunctions F G}
    (hf : HasAdelicPolynomialGrowth F G rho f) (hh : HasAdelicPolynomialGrowth F G rho h) :
    HasAdelicPolynomialGrowth F G rho (f + h) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  obtain ⟨D, hD, e, hh⟩ := hh
  refine ⟨C + D, add_nonneg hC hD, max d e, fun g => ?_⟩
  have h1 := RepresentationGrowth.one_le_adelicHeight F G rho hN g
  calc
    ‖evaluate F G (f + h) g‖ ≤ ‖evaluate F G f g‖ + ‖evaluate F G h g‖ := norm_add_le _ _
    _ ≤ C * RepresentationGrowth.adelicHeight F G rho g ^ d +
        D * RepresentationGrowth.adelicHeight F G rho g ^ e := add_le_add (hf g) (hh g)
    _ ≤ C * RepresentationGrowth.adelicHeight F G rho g ^ max d e +
        D * RepresentationGrowth.adelicHeight F G rho g ^ max d e :=
      add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (le_max_left d e)) hC)
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (le_max_right d e)) hD)
    _ = (C + D) * RepresentationGrowth.adelicHeight F G rho g ^ max d e :=
      (add_mul _ _ _).symm

theorem HasAdelicPolynomialGrowth.smul {f : ContinuousRationalFunctions F G}
    (hf : HasAdelicPolynomialGrowth F G rho f) (c : ℂ) :
    HasAdelicPolynomialGrowth F G rho (c • f) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, d, fun g => ?_⟩
  calc
    ‖evaluate F G (c • f) g‖ = ‖c‖ * ‖evaluate F G f g‖ := norm_mul _ _
    _ ≤ ‖c‖ * (C * RepresentationGrowth.adelicHeight F G rho g ^ d) :=
      mul_le_mul_of_nonneg_left (hf g) (norm_nonneg _)
    _ = (‖c‖ * C) * RepresentationGrowth.adelicHeight F G rho g ^ d :=
      (mul_assoc _ _ _).symm

theorem HasAdelicPolynomialGrowth.rightAction (hN : 0 < N)
    {f : ContinuousRationalFunctions F G} (hf : HasAdelicPolynomialGrowth F G rho f)
    (h : AdelicGroupPoints F G) :
    HasAdelicPolynomialGrowth F G rho (continuousRightAction F G h f) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  have hn0 (g) : 0 ≤ RepresentationGrowth.adelicHeight F G rho g :=
    zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN g)
  refine ⟨C * RepresentationGrowth.adelicHeight F G rho h ^ d,
    mul_nonneg hC (pow_nonneg (hn0 h) d), d, fun g => ?_⟩
  calc
    ‖evaluate F G (continuousRightAction F G h f) g‖ ≤
        C * RepresentationGrowth.adelicHeight F G rho (g * h) ^ d := hf (g * h)
    _ ≤ C * (RepresentationGrowth.adelicHeight F G rho g *
        RepresentationGrowth.adelicHeight F G rho h) ^ d :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hn0 _) (RepresentationGrowth.adelicHeight_mul_le F G rho hN g h) d)
        hC
    _ = (C * RepresentationGrowth.adelicHeight F G rho h ^ d) *
        RepresentationGrowth.adelicHeight F G rho g ^ d := by rw [mul_pow]; ring

variable (F G rho)

/-- Natural exponents for the scaled height give exactly real exponents for the exact norm. -/
theorem hasAdelicModerateGrowth_iff (hN : 0 < N) (f : ContinuousRationalFunctions F G) :
    HasAdelicModerateGrowth F G rho f ↔ HasAdelicPolynomialGrowth F G rho f := by
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
  · rintro ⟨C, hC, r, hf⟩
    obtain ⟨d, hd⟩ := exists_nat_ge r
    have hcoef : 0 ≤ C * (K⁻¹) ^ r :=
      mul_nonneg hC.le (Real.rpow_nonneg (inv_nonneg.mpr hK.le) r)
    refine ⟨C * (K⁻¹) ^ r, hcoef, d, fun g => ?_⟩
    calc
      ‖evaluate F G f g‖ ≤ C * RepresentationGrowth.adelicSourceNorm F G rho g ^ r :=
        hf g
      _ = (C * (K⁻¹) ^ r) * RepresentationGrowth.adelicHeight F G rho g ^ r := by
        rw [hsource, Real.mul_rpow (inv_nonneg.mpr hK.le) (hn0 g)]
        ring
      _ ≤ (C * (K⁻¹) ^ r) * RepresentationGrowth.adelicHeight F G rho g ^ d := by
        apply mul_le_mul_of_nonneg_left _ hcoef
        simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le
          (RepresentationGrowth.one_le_adelicHeight F G rho hN g) hd
  · rintro ⟨C, hC, d, hf⟩
    refine ⟨(C + 1) * K ^ d, mul_pos (by linarith) (pow_pos hK d), (d : ℝ), fun g => ?_⟩
    rw [Real.rpow_natCast]
    calc
      ‖evaluate F G f g‖ ≤ C * RepresentationGrowth.adelicHeight F G rho g ^ d := hf g
      _ ≤ (C + 1) * RepresentationGrowth.adelicHeight F G rho g ^ d :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (hn0 g) d)
      _ = ((C + 1) * K ^ d) * RepresentationGrowth.adelicSourceNorm F G rho g ^ d := by
        rw [hscale, mul_pow]
        ring

/-- The actual full adelic growth space is a subrepresentation of the existing ambient action. -/
def adelicGrowthSubrepresentation (hN : 0 < N) :
    Subrepresentation (continuousRightAction F G) where
  toSubmodule :=
    { carrier := {f | HasAdelicPolynomialGrowth F G rho f}
      zero_mem' := HasAdelicPolynomialGrowth.zero
      add_mem' := HasAdelicPolynomialGrowth.add hN
      smul_mem' c _ hf := hf.smul c }
  apply_mem_toSubmodule h _f hf := hf.rightAction hN h

@[simp]
theorem mem_adelicGrowthSubrepresentation (hN : 0 < N) (f : ContinuousRationalFunctions F G) :
    f ∈ adelicGrowthSubrepresentation F G rho hN ↔ HasAdelicModerateGrowth F G rho f :=
  (hasAdelicModerateGrowth_iff F G rho hN f).symm

/-- Existing smooth infinite slices and one common open finite stabilizer, with full growth. -/
def finitePlotSmoothAdelicGrowthSubrepresentation (hN : 0 < N) :
    Subrepresentation (continuousRightAction F G) :=
  finitePlotSmoothRationalSubrepresentation F G ⊓ adelicGrowthSubrepresentation F G rho hN

end Langlands.Automorphic.GroupSchemeFunctions
