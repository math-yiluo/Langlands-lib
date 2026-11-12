import Langlands.Automorphic.CuspidalAdmissible.EnergyBound
import Langlands.Automorphic.CuspidalAdmissible.CuspRealization

/-!
# From the energy to band integrals of derivatives

For the band unitary form `b` of a cuspidal realization, `b(f, f)` is the band integral of
`|f|²`, and each basis derivative `D_k = D_{X_k}` (for the fixed basis `X_k` of the real Lie
algebra) is a real combination of the operators `D_{Y_i}` of the normalized Cartan basis
`Y_i`. By Cauchy–Schwarz the band integrals of the `D_k e` are bounded by a constant times the
energy `∑ b(D_{Y_i} e, D_{Y_i} e)`.
-/

noncomputable section

universe uF

open MeasureTheory NumberField
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Automorphic.CuspidalAdmissible

open Langlands.Global Langlands.Automorphic Langlands.Automorphic.OperatorDeterminantSlice

section Core

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (c : InnerProductSpace.Core ℂ V)

/-- Cauchy–Schwarz for a real combination, for a form given as an inner product core. -/
theorem re_inner_sum_smul_le_core {ι : Type*} (s : Finset ι) (a : ι → ℝ) (v : ι → V) :
    (c.inner (∑ i ∈ s, (a i : ℂ) • v i) (∑ i ∈ s, (a i : ℂ) • v i)).re ≤
      (∑ i ∈ s, a i ^ 2) * ∑ i ∈ s, (c.inner (v i) (v i)).re := by
  let _ : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ c
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  have hn : ∀ x : V, (c.inner x x).re = ‖x‖ ^ 2 := fun x => by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    rfl
  rw [hn]
  simp only [hn]
  have h1 : ‖∑ i ∈ s, (a i : ℂ) • v i‖ ≤ ∑ i ∈ s, |a i| * ‖v i‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => |a i|) (fun i => ‖v i‖)
  simp only [sq_abs] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- A vector with nonpositive square norm is zero. -/
theorem eq_zero_of_re_inner_self_le_zero_core {x : V} (h : (c.inner x x).re ≤ 0) : x = 0 := by
  let _ : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ c
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  have hn : (c.inner x x).re = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    rfl
  rw [hn] at h
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h (sq_nonneg _)))

end Core

/-- The real part of the integral of `⟨φ, φ⟩` is the integral of `|φ|²`. -/
theorem ofReal_re_integral_inner_self {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {φ : X → ℂ} (hφ : MemLp φ 2 μ) :
    ENNReal.ofReal (∫ q, inner ℂ (φ q) (φ q) ∂μ).re = ∫⁻ q, ‖φ q‖ₑ ^ 2 ∂μ := by
  have h1 : ∀ q, inner ℂ (φ q) (φ q) = ((‖φ q‖ ^ 2 : ℝ) : ℂ) := fun q => by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp_rw [h1]
  have h2 : ∫ q, ((‖φ q‖ ^ 2 : ℝ) : ℂ) ∂μ = ((∫ q, ‖φ q‖ ^ 2 ∂μ : ℝ) : ℂ) :=
    integral_complex_ofReal
  rw [h2, Complex.ofReal_re, ofReal_integral_eq_lintegral_ofReal
    hφ.norm.integrable_sq (Filter.Eventually.of_forall fun q => sq_nonneg _)]
  refine lintegral_congr fun q => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance energyConvRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance energyConvContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance energyConvSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance energyConvFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance energyConvStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable (S : OperatorRealization F n)

local instance energyConvSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The coordinates of the basis direction `X_k` in the normalized Cartan basis. -/
abbrev cartanCoord (k : Fin (Module.finrank ℝ (ArchimedeanMatrix F n)))
    (i : ArchimedeanGL.CartanBasisIndex F n) : ℝ :=
  (ArchimedeanGL.cartanAdaptedBasis F n).repr (ArchimedeanGL.lieDirection F n k) i

/-- A basis derivative is a real combination of the Cartan basis operators. -/
theorem basisDerivative_eq_sum (k : Fin (Module.finrank ℝ (ArchimedeanMatrix F n)))
    (f : S.Space) :
    basisDerivative S k f =
      ∑ i, (cartanCoord k i : ℂ) • realOperator S (ArchimedeanGL.cartanAdaptedBasis F n i) f := by
  have h1 : ArchimedeanGL.realEnvelopingGenerator F n (ArchimedeanGL.lieDirection F n k) =
      ∑ i, (cartanCoord k i : ℂ) •
        ArchimedeanGL.realEnvelopingGenerator F n (ArchimedeanGL.cartanAdaptedBasis F n i) := by
    conv_lhs => rw [← (ArchimedeanGL.cartanAdaptedBasis F n).sum_repr
      (ArchimedeanGL.lieDirection F n k)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Complex.coe_smul]
  have h2 := congrArg (fun u => S.envelopingAction u f) h1
  refine h2.trans ?_
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

variable [CompactSpace (AdeleQuotient F)] (hn : n ≠ 0) (hS : S.IsCuspidal)
  (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1)
  (hSχ : S.HasCentralCharacter χ)
  (hL2 : ∀ f : S.Space,
    MemLp (toQuotient F n S f) 2 ((quotientHaarMeasure F n).restrict (band F n)))

/-- The band integral of `|f|²` is the square norm of `f` for the band unitary form. -/
theorem bandNorm_eq_ofReal_inner (f : S.Space) :
    bandNorm S f = ENNReal.ofReal ((unitaryForm F n S hn hS χ hχ hSχ hL2).inner f f).re := by
  rw [unitaryForm_inner]
  exact (ofReal_re_integral_inner_self (hL2 f)).symm

omit [CompactSpace (AdeleQuotient F)] in
theorem energy_nonneg (b : S.UnitaryForm) (e : S.Space) : 0 ≤ energy b e :=
  Finset.sum_nonneg fun _ _ => b.finiteForm.toInnerProductCore.re_inner_nonneg _

omit [CompactSpace (AdeleQuotient F)] in
/-- **Derivatives are controlled by the energy** (for any unitary form computing band
integrals). -/
theorem sum_bandNorm_basisDerivative_le_of (b : S.UnitaryForm)
    (hb : ∀ f, bandNorm S f = ENNReal.ofReal (b.inner f f).re) (e : S.Space) :
    ∑ k, bandNorm S (basisDerivative S k e) ≤
      ENNReal.ofReal ((∑ k, ∑ i, cartanCoord (F := F) (n := n) k i ^ 2) * energy b e) := by
  have hk : ∀ k, bandNorm S (basisDerivative S k e) ≤
      ENNReal.ofReal ((∑ i, cartanCoord (F := F) (n := n) k i ^ 2) * energy b e) := by
    intro k
    refine (le_of_eq (hb _)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h := re_inner_sum_smul_le_core b.finiteForm.toInnerProductCore Finset.univ
      (cartanCoord k) (fun i => realOperator S (ArchimedeanGL.cartanAdaptedBasis F n i) e)
    have heq := congrArg (fun v => (b.inner v v).re) (basisDerivative_eq_sum S k e)
    exact heq.trans_le h
  refine (Finset.sum_le_sum fun k _ => hk k).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ =>
    mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (energy_nonneg S b e), Finset.sum_mul]

/-- **Derivatives are controlled by the energy** for the band unitary form. -/
theorem sum_bandNorm_basisDerivative_le (e : S.Space) :
    ∑ k, bandNorm S (basisDerivative S k e) ≤
      ENNReal.ofReal ((∑ k, ∑ i, cartanCoord (F := F) (n := n) k i ^ 2) *
        energy (unitaryForm F n S hn hS χ hχ hSχ hL2) e) :=
  sum_bandNorm_basisDerivative_le_of S _ (bandNorm_eq_ofReal_inner S hn hS χ hχ hSχ hL2) e

end Langlands.Automorphic.CuspidalAdmissible
