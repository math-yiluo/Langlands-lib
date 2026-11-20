import Langlands.Representation.Archimedean.RealStandardCompactAverage
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient
import Mathlib.LinearAlgebra.Trace

/-! # Invariance of compact polynomial traces on real standard modules -/

noncomputable section

open MeasureTheory
open Langlands.LocalFactor.Archimedean
open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealStandardCompactAverage

attribute [local instance 100] LieRing.ofAssociativeRing

open RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

local instance (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

local notation "G" => Langlands.GeneralLinear
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℝ
local notation "V" => fun n ds => kFiniteFunctions (realStandardModule n ds)
  (unitaryCompact ℝ n)

variable {n : ℕ}
variable (μ : Measure (K n)) [hμ : μ.IsHaarMeasure]

include hμ in
private theorem pairing_average {f v : G n ℝ → ℂ} (hf : Continuous f) (hv : Continuous v)
    (φ : C(K n, ℂ)) (g : G n ℝ) :
    ∫ x : unitaryCompact ℝ n, v x * average μ φ g f x ∂haarK n =
      ∫ k, φ k * (∫ x : unitaryCompact ℝ n,
        f ((x : G n ℝ) * (Unitary.toUnits k * g)) * v x ∂haarK n) ∂μ := by
  let F (x : unitaryCompact ℝ n) (k : K n) :=
    φ k * (f ((x : G n ℝ) * (Unitary.toUnits k * g)) * v x)
  have hx : Continuous (fun x : unitaryCompact ℝ n => (x : G n ℝ)) :=
    continuous_subtype_val
  have hF : Continuous (Function.uncurry F) :=
    (φ.continuous.comp continuous_snd).mul
      ((hf.comp ((hx.comp continuous_fst).mul
        ((continuous_unitary_toUnits.comp continuous_snd).mul continuous_const))).mul
        (hv.comp (hx.comp continuous_fst)))
  have hi : Integrable (Function.uncurry F) ((haarK n).prod μ) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ x, ∫ k, F x k ∂μ ∂haarK n := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      change v x * (∫ k, φ k * f ((x : G n ℝ) * Unitary.toUnits k * g) ∂μ) =
        ∫ k, F x k ∂μ
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun k => ?_)
      simp only [F, mul_assoc]
      ring
    _ = ∫ k, ∫ x, F x k ∂haarK n ∂μ := integral_integral_swap hi
    _ = _ := integral_congr_ae (ae_of_all _ fun k => integral_const_mul (φ k) _)

/-- Compact polynomial averaging after right translation commutes with a compact and Lie
intertwiner. -/
theorem intertwiner_averageMap {ds es : List RealBlock} (T : V n ds →ₗ[ℂ] V n es)
    (hT : IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T)
    (φ : OrthogonalFinitePolynomial.polynomialStar n) (g : G n ℝ) (f : V n ds) :
    T (averageMap μ ds φ g f) = averageMap μ es φ g (T f) := by
  apply sub_eq_zero.mp
  let w := T (averageMap μ ds φ g f) - averageMap μ es φ g (T f)
  change w = 0
  by_contra hw
  have hw0 : (w : G n ℝ → ℂ) ≠ 0 := fun h => hw (Subtype.ext h)
  have hχ := RealStrictCharacterLanglandsQuotient.isSignedPower ds
  have hψ := RealStrictCharacterLanglandsQuotient.isSignedPower es
  obtain ⟨v, hv, hv0⟩ := RealReverseTransfer.exists_integral_mul_ne_zero hψ
    (RealReverseTransfer.mem_kFiniteFunctions_principalSeries w.2) hw0
  obtain ⟨u, hu, huv⟩ := RealReverseTransfer.exists_pairing_transpose hχ T hT hv
  have huc := JacquetKernel.continuous_of_mem hu
  have hvc := JacquetKernel.continuous_of_mem hv
  have havg : ∫ x : unitaryCompact ℝ n, u x * (averageMap μ ds φ g f : G n ℝ → ℂ) x
        ∂haarK n =
      ∫ x : unitaryCompact ℝ n, v x * (averageMap μ es φ g (T f) : G n ℝ → ℂ) x
        ∂haarK n := by
    simp only [averageMap_apply_coe]
    rw [pairing_average μ (continuous_of_mem_kFiniteFunctions f.2) huc,
      pairing_average μ (continuous_of_mem_kFiniteFunctions (T f).2) hvc]
    exact integral_congr_ae (ae_of_all _ fun k =>
      congrArg (fun z : ℂ => (φ : C(K n, ℂ)) k * z)
        (RealReverseTransfer.integral_mul_transfer hχ hψ T hT hv hu huv f
          (Unitary.toUnits k * g)).symm)
  apply hv0
  simp only [w, Submodule.coe_sub, Pi.sub_apply, mul_sub]
  rw [integral_sub
    (integrable_mul_of_continuous hvc (continuous_of_mem_kFiniteFunctions (T _).2))
    (integrable_mul_of_continuous hvc (continuous_of_mem_kFiniteFunctions (averageMap _ _ _ _ _).2))]
  exact sub_eq_zero.mpr ((huv (averageMap μ ds φ g f)).symm.trans havg)

/-- Trace of the averaging operator on its finite-dimensional range. -/
def averageTrace (ds : List RealBlock) (φ : OrthogonalFinitePolynomial.polynomialStar n)
    (g : G n ℝ) : ℂ :=
  let A := averageMap μ ds φ g
  LinearMap.trace ℂ A.range (A.rangeRestrict.comp A.range.subtype)

/-- A compact and Lie isomorphism of actual real standard modules preserves every compact
polynomial average trace. -/
def RealStandardCompactTraceStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (K n)) [μ.IsHaarMeasure] (ds es : List RealBlock)
    (T : V n ds →ₗ[ℂ] V n es),
    IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T →
    Function.Bijective T →
    ∀ (φ : OrthogonalFinitePolynomial.polynomialStar n) (g : G n ℝ),
      averageTrace μ ds φ g = averageTrace μ es φ g

omit hμ in
theorem realStandardCompactTrace : RealStandardCompactTraceStatement := by
  intro n μ _ ds es T hT hbij φ g
  let A := averageMap μ ds φ g
  let B := averageMap μ es φ g
  have hcomm (f : V n ds) : T (A f) = B (T f) := intertwiner_averageMap μ T hT φ g f
  have hmem : ∀ f ∈ A.range, T f ∈ B.range := by
    rintro _ ⟨f, rfl⟩
    exact ⟨T f, (hcomm f).symm⟩
  let R := T.restrict hmem
  have hR : Function.Bijective R := by
    constructor
    · intro x y heq
      exact Subtype.ext (hbij.1 (congrArg Subtype.val heq))
    · rintro ⟨_, f, rfl⟩
      obtain ⟨x, rfl⟩ := hbij.2 f
      exact ⟨⟨A x, x, rfl⟩, Subtype.ext (hcomm x)⟩
  let E := LinearEquiv.ofBijective R hR
  have hconj : E.conj (A.rangeRestrict.comp A.range.subtype) =
      B.rangeRestrict.comp B.range.subtype := by
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    change T (A (E.symm x : A.range)) = B (x : B.range)
    rw [hcomm]
    exact congrArg B (congrArg Subtype.val (E.apply_symm_apply x))
  change LinearMap.trace ℂ A.range (A.rangeRestrict.comp A.range.subtype) =
    LinearMap.trace ℂ B.range (B.rangeRestrict.comp B.range.subtype)
  have : FiniteDimensional ℂ A.range := finiteDimensional_range_averageMap μ ds φ g
  have : FiniteDimensional ℂ B.range := finiteDimensional_range_averageMap μ es φ g
  rw [← hconj]
  exact (LinearMap.trace_conj' (R := ℂ) (M := A.range) (N := B.range)
    (A.rangeRestrict.comp A.range.subtype) E).symm

end Langlands.Archimedean.RealStandardCompactAverage
