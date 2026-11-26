import Langlands.Group.InternalPolarFactors
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic
import Langlands.Representation.Archimedean.GeneralLinear
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonReflectedHaar
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.Star

/-! # Commutativity of spherical convolution at archimedean places -/

noncomputable section

open scoped ComplexOrder Matrix.Norms.Operator

namespace Langlands.TraceFormula

open Langlands.Archimedean Langlands.HarishChandraSchwartz MeasureTheory
open Group.AlgebraicMatrixPowers Group.InternalPolarFactors

universe u

variable (F : Type u) [RCLike F] (n : ℕ)

local notation "G" => GeneralLinear n F
local notation "K" => unitaryCompact F n

/-- Taking the adjoint preserves each double coset of the standard compact subgroup. -/
theorem exists_unitary_star_doubleCoset (g : G) :
    ∃ k : G, k ∈ K ∧ star g = k * g * k := by
  have hpoly : IsPolynomiallyDefined (⊤ : Subgroup G) := ⟨∅, by simp⟩
  obtain ⟨k, a, _, _, hk, ha, hg⟩ :=
    exists_unitary_posDef_factors (⊤ : Subgroup G) hpoly (by simp) g (by simp)
  have hku : k ∈ unitary G := by
    rw [Units.unitary_eq]
    exact hk
  have hstar : star k = k⁻¹ := eq_inv_iff_mul_eq_one.mpr hku.1
  have ha' : star a = a := Units.ext ha.isHermitian.star_eq
  have hk' : k ∈ K := hk
  refine ⟨k⁻¹, (unitaryCompact F n).inv_mem hk', ?_⟩
  rw [hg, star_mul, ha', hstar, ← mul_assoc k⁻¹ k a, inv_mul_cancel, one_mul]

private def inverseAdjoint : G ≃ₜ* G where
  toFun g := (star g)⁻¹
  invFun g := (star g)⁻¹
  left_inv g := by simp [star_inv]
  right_inv g := by simp [star_inv]
  map_mul' g h := by simp [star_mul, mul_inv_rev]
  continuous_toFun := continuous_star.inv
  continuous_invFun := continuous_star.inv

private theorem inverseAdjoint_involutive : Function.Involutive (inverseAdjoint F n) :=
  (inverseAdjoint F n).left_inv

/-- Spherical convolution commutes for the actual real or complex general
linear group with a regular left Haar measure. -/
def ArchimedeanSphericalConvolutionStatement : Prop :=
  ∀ (F : Type u) [RCLike F] (n : ℕ) [MeasurableSpace (GeneralLinear n F)]
    [BorelSpace (GeneralLinear n F)] (μ : Measure (GeneralLinear n F))
    [μ.IsHaarMeasure] [μ.Regular] (f g : GeneralLinear n F → ℂ),
    IsBiInvariant (unitaryCompact F n) f → IsBiInvariant (unitaryCompact F n) g →
    ∀ x : GeneralLinear n F, (∫ y, f y * g (y⁻¹ * x) ∂μ) =
      ∫ y, g y * f (y⁻¹ * x) ∂μ

theorem archimedeanSphericalConvolution : ArchimedeanSphericalConvolutionStatement.{u} := by
  intro F _ n _ _ μ _ _ f g hf hg x
  let : LocallyCompactSpace (GeneralLinear n F) := Units.isOpenEmbedding_val.locallyCompactSpace
  let θ := inverseAdjoint F n
  have hθ := RankinSelberg.measurePreserving_involutive_automorphism θ
    (inverseAdjoint_involutive F n) μ
  have hsym (h : GeneralLinear n F → ℂ) (hh : IsBiInvariant (unitaryCompact F n) h)
      (z : GeneralLinear n F) : h (θ z) = h z⁻¹ := by
    obtain ⟨k, hk, heq⟩ := exists_unitary_star_doubleCoset F n z⁻¹
    have hθz : θ z = k * z⁻¹ * k := (star_inv z).symm.trans heq
    rw [hθz, hh k hk k hk]
  let convolution (x : GeneralLinear n F) := ∫ y, f y * g (y⁻¹ * x) ∂μ
  have hconv : IsBiInvariant (unitaryCompact F n) convolution := by
    intro a ha b hb z
    change (∫ y, f y * g (y⁻¹ * (a * z * b)) ∂μ) = convolution z
    calc
      _ = ∫ y, f (a * y) * g ((a * y)⁻¹ * (a * z * b)) ∂μ :=
        (integral_mul_left_eq_self (fun y => f y * g (y⁻¹ * (a * z * b))) a).symm
      _ = convolution z := by
        apply integral_congr_ae
        filter_upwards [] with y
        have hleft : f (a * y) = f y := by
          simpa only [mul_one] using hf a ha 1 (unitaryCompact F n).one_mem y
        have hright : g (y⁻¹ * z * b) = g (y⁻¹ * z) := by
          simpa only [one_mul] using hg 1 (unitaryCompact F n).one_mem b hb (y⁻¹ * z)
        have harg : (a * y)⁻¹ * (a * z * b) = y⁻¹ * z * b := by group
        change f (a * y) * g ((a * y)⁻¹ * (a * z * b)) = f y * g (y⁻¹ * z)
        rw [hleft, harg, hright]
  have hx : convolution x = convolution (θ x⁻¹) := by
    simpa only [inv_inv] using (hsym convolution hconv x⁻¹).symm
  calc
    convolution x = convolution (θ x⁻¹) := hx
    _ = ∫ u, f (θ u) * g ((θ u)⁻¹ * θ x⁻¹) ∂μ :=
      (hθ.integral_comp θ.toHomeomorph.measurableEmbedding
        (fun y => f y * g (y⁻¹ * θ x⁻¹))).symm
    _ = ∫ u, f u⁻¹ * g (x * u) ∂μ := by
      congr 1
      funext u
      rw [hsym f hf, ← map_inv, ← map_mul, hsym g hg, mul_inv_rev, inv_inv, inv_inv]
    _ = ∫ y, f (y⁻¹ * x) * g y ∂μ := by
      rw [← integral_mul_left_eq_self (fun u => f u⁻¹ * g (x * u)) x⁻¹]
      simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left]
    _ = ∫ y, g y * f (y⁻¹ * x) ∂μ := by simp_rw [mul_comm (f _)]

end Langlands.TraceFormula
