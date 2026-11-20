import Langlands.Representation.Archimedean.ComplexDuality.UnitaryHaar
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # A compact Haar weight reproducing evaluation on finitely many types -/

noncomputable section

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

section Compact

variable {K : Type*} [Group K] [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-- Integration against the conjugate of one vector of a continuous finite-dimensional
function space can reproduce evaluation on that space. -/
theorem exists_compactWeight_reproducing_evaluation (μ : Measure K) [μ.IsHaarMeasure]
    (V : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ V] (hV : ∀ v : V, Continuous v.val)
    (x₀ : K) :
    ∃ f : V, ∀ v : V, ∫ k, star (f.val k) * v.val k ∂μ = v.val x₀ := by
  classical
  let I := Fin (Module.finrank ℂ V)
  let b : Module.Basis I ℂ V := Module.finBasis ℂ V
  let C (z : I → ℂ) (k : K) := ∑ i, z i * star ((b i).val k)
  have hC (z : I → ℂ) : Continuous (C z) :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (Complex.continuous_conj.comp (hV (b j)))
  have hInt (z : I → ℂ) (i : I) : Integrable (fun k => C z k * (b i).val k) μ :=
    ((hC z).mul (hV (b i))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let P : (I → ℂ) →ₗ[ℂ] (I → ℂ) :=
    { toFun := fun z i => ∫ k, C z k * (b i).val k ∂μ
      map_add' := by
        intro z w
        funext i
        simp only [C, Pi.add_apply, add_mul, Finset.sum_add_distrib]
        exact integral_add (hInt z i) (hInt w i)
      map_smul' := by
        intro t z
        funext i
        change (∫ k, C (t • z) k * (b i).val k ∂μ) =
          t * (∫ k, C z k * (b i).val k ∂μ)
        have h (k : K) : C (t • z) k = t * C z k := by
          simp only [C, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
        simp only [h, mul_assoc, integral_const_mul] }
  have hker : P.ker = ⊥ := LinearMap.ker_eq_bot'.mpr fun z hz => by
    have hz' (i : I) : (∫ k, C z k * (b i).val k ∂μ) = 0 :=
      congrFun hz i
    have hconj (k : K) : star (C z k) = ∑ i, star (z i) * (b i).val k := by
      simp only [C, star_sum, star_mul, star_star, mul_comm]
    have hzero : (∫ k, C z k * star (C z k) ∂μ) = 0 := by
      simp only [hconj, Finset.mul_sum]
      rw [integral_finsetSum]
      · have hi (i : I) : (∫ k, C z k * (star (z i) * (b i).val k) ∂μ) = 0 := by
          calc
            _ = ∫ k, star (z i) * (C z k * (b i).val k) ∂μ :=
              integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_left_comm _ _ _)
            _ = 0 := by rw [integral_const_mul, hz', mul_zero]
        simp only [hi, Finset.sum_const_zero]
      · intro i _
        exact ((hC z).mul (continuous_const.mul (hV (b i)))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    have hA (k : K) : C z k = 0 := by
      by_contra hn
      have hpos : 0 < ∫ y, ‖C z y‖ ^ 2 ∂μ :=
        ((hC z).norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
          (HasCompactSupport.of_compactSpace _) (fun _ => sq_nonneg _)
          (pow_ne_zero _ (norm_ne_zero_iff.mpr hn))
      have hsq (y : K) : C z y * star (C z y) = (‖C z y‖ ^ 2 : ℝ) := by
        simpa only [starRingEnd_apply, Complex.ofReal_pow] using Complex.mul_conj' (C z y)
      simp only [hsq, integral_complex_ofReal, Complex.ofReal_eq_zero] at hzero
      exact hpos.ne' hzero
    let v := ∑ i, star (z i) • b i
    have hv : v = 0 := by
      apply Subtype.ext
      funext k
      have hk : star (C z k) = 0 := by rw [hA, star_zero]
      simpa only [v, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, Finset.sum_apply,
        Pi.smul_apply, Pi.zero_apply, smul_eq_mul, hconj] using hk
    funext i
    have hzi := congrArg (fun u : V => b.repr u i) hv
    simpa only [v, Module.Basis.repr_sum_self, map_zero, Finsupp.zero_apply, star_eq_zero,
      Pi.zero_apply] using hzi
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hker))
    (fun i => (b i).val x₀)
  let f := ∑ i, star (z i) • b i
  have hf' (k : K) : star (f.val k) = C z k := by
    simp only [f, C, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, star_sum, star_mul, star_star, mul_comm]
  let L : Module.Dual ℂ V :=
    { toFun := fun v => ∫ k, C z k * v.val k ∂μ
      map_add' := by
        intro v w
        simp only [Submodule.coe_add, Pi.add_apply, mul_add]
        exact integral_add (((hC z).mul (hV v)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)) (((hC z).mul (hV w)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
      map_smul' := by
        intro t v
        change (∫ k, C z k * (t * v.val k) ∂μ) = t * ∫ k, C z k * v.val k ∂μ
        calc
          _ = ∫ k, t * (C z k * v.val k) ∂μ :=
            integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_left_comm _ _ _)
          _ = _ := integral_const_mul _ _ }
  have hL : L = (LinearMap.proj x₀).comp V.subtype := b.ext fun i => congrFun hz i
  refine ⟨f, fun v => ?_⟩
  simp only [hf']
  exact LinearMap.congr_fun hL v

/-- A left-invariant finite-dimensional space of continuous coefficient functions
has a reproducing weight with finite left-translate span. -/
theorem exists_compactWeight_of_finite_left_invariant_space (μ : Measure K) [μ.IsHaarMeasure]
    (V : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ V] (hV : ∀ v : V, Continuous v.val)
    (hshift : ∀ (h : K) (v : V), (fun k => v.val (h⁻¹ * k)) ∈ V) :
    ∃ κ : K → ℂ, Continuous κ ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun h : K => fun k => κ (h⁻¹ * k))) ∧
      ∀ v : V, ∫ k, κ k * v.val k ∂μ = v.val 1 := by
  let b := Module.finBasis ℂ V
  let γ (j : Fin (Module.finrank ℂ V)) (k : K) := star ((b j).val k)
  let S := Submodule.span ℂ (Set.range γ)
  let : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range γ)
  have hstar (v : V) : (fun k => star (v.val k)) ∈ S := by
    have hv : (fun k => star (v.val k)) = ∑ j, star (b.repr v j) • γ j := by
      funext k
      have hrepr := congrArg (fun x : V => x.val k) (b.sum_repr v)
      have hrepr' : ∑ j, b.repr v j * (b j).val k = v.val k := by
        simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul] using hrepr
      simp only [← hrepr', star_sum, star_mul, mul_comm, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, γ]
    rw [hv]
    exact S.sum_mem fun j _ => S.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨f, hf⟩ := exists_compactWeight_reproducing_evaluation μ V hV 1
  refine ⟨fun k => star (f.val k), Complex.continuous_conj.comp (hV f), ?_, hf⟩
  apply Submodule.finiteDimensional_of_le (S₂ := S)
  apply Submodule.span_le.mpr
  rintro _ ⟨h, rfl⟩
  exact hstar ⟨fun k => f.val (h⁻¹ * k), hshift h f⟩

/-- Obtain a reproducing compact weight from a finite-dimensional orbit and
scalar covariance of the coefficient functions under left translation. -/
theorem exists_compactWeight_of_finite_orbit {X : Type*} (μ : Measure K) [μ.IsHaarMeasure]
    (A : K → X → ℂ) (hcont : ∀ x, Continuous fun k => A k x)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range A)))
    (hshift : ∀ (h : K) (x : X), ∃ (c : ℂ) (y : X), ∀ k, A (h⁻¹ * k) x = c * A k y) :
    ∃ κ : K → ℂ, Continuous κ ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun h : K => fun k => κ (h⁻¹ * k))) ∧
      ∀ x, ∫ k, κ k * A k x ∂μ = A 1 x := by
  let U := Submodule.span ℂ (Set.range A)
  let : FiniteDimensional ℂ U := hfin
  let b := Module.finBasis ℂ U
  let e (k : K) : U := ⟨A k, Submodule.subset_span ⟨k, rfl⟩⟩
  let β (j : Fin (Module.finrank ℂ U)) (k : K) := b.repr (e k) j
  let v (x : X) (k : K) := A k x
  let V := Submodule.span ℂ (Set.range v)
  let S := Submodule.span ℂ (Set.range β)
  let : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range β)
  have hV : V ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    have hv : v x = ∑ j, (b j).val x • β j := by
      funext k
      have hb := congrArg (fun f : U => f.val x) (b.sum_repr (e k))
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, e, v, β, mul_comm] using hb.symm
    rw [hv]
    exact S.sum_mem fun j _ => S.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  let : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hV
  have hVc (f : V) : Continuous f.val := by
    refine Submodule.span_induction (p := fun F _ => Continuous F) ?_ continuous_const ?_ ?_ f.2
    · rintro _ ⟨x, rfl⟩
      exact hcont x
    · intro F G _ _ hF hG
      exact hF.add hG
    · intro c F _ hF
      exact continuous_const.smul hF
  have hVl (h : K) (f : V) : (fun k => f.val (h⁻¹ * k)) ∈ V := by
    refine Submodule.span_induction (p := fun F _ => (fun k => F (h⁻¹ * k)) ∈ V)
      ?_ (V.zero_mem) ?_ ?_ f.2
    · rintro _ ⟨x, rfl⟩
      obtain ⟨c, y, hc⟩ := hshift h x
      have hh : (fun k => v x (h⁻¹ * k)) = c • v y := funext hc
      rw [hh]
      exact V.smul_mem c (Submodule.subset_span ⟨y, rfl⟩)
    · intro F G _ _ hF hG
      exact V.add_mem hF hG
    · intro c F _ hF
      exact V.smul_mem c hF
  obtain ⟨κ, hκc, hκfin, hκ⟩ := exists_compactWeight_of_finite_left_invariant_space μ V hVc hVl
  exact ⟨κ, hκc, hκfin, fun x => hκ ⟨v x, Submodule.subset_span ⟨x, rfl⟩⟩⟩

end Compact

section MatrixTest

open Langlands.Archimedean
open scoped Langlands.Archimedean.ComplexDuality

variable {n : ℕ}

local notation "Kc" => unitaryCompact ℂ n
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- The compact left translate of a square test, with a determinant character. -/
def complexCompactMatrixTranslate (η : ℂˣ →* ℂˣ) (Φ : Mat → ℂ) (k : Kc) (X : Mat) : ℂ :=
  (η (GeneralLinear.determinant k.val) : ℂ) * Φ ((k.val⁻¹).val * X)

variable (n) in
/-- A continuous square test whose unitary left translates have finite span has
a continuous reproducing compact weight with finite left-translate span. -/
def ComplexLocalCompactMatrixWeightStatement : Prop :=
  ∀ (μ : Measure Kc), μ.IsHaarMeasure →
  ∀ (η : ℂˣ →* ℂˣ), Continuous η →
  ∀ (Φ : Mat → ℂ), Continuous Φ →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Kc => fun X => Φ ((k.val⁻¹).val * X))) →
    ∃ κ : Kc → ℂ, Continuous κ ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun h : Kc => fun k => κ (h⁻¹ * k))) ∧
      ∀ X, ∫ k, κ k * complexCompactMatrixTranslate η Φ k X ∂μ = Φ X

theorem complexLocalCompactMatrixWeight : ComplexLocalCompactMatrixWeightStatement n := by
  intro μ hμ η hη Φ hΦ hfin
  let : μ.IsHaarMeasure := hμ
  let A := complexCompactMatrixTranslate η Φ
  have hcont (X : Mat) : Continuous fun k => A k X :=
    (Units.continuous_val.comp (hη.comp (GeneralLinear.determinantContinuous.continuous.comp
      continuous_subtype_val))).mul (hΦ.comp
        ((Units.continuous_val.comp continuous_subtype_val.inv).mul continuous_const))
  have hA : FiniteDimensional ℂ (Submodule.span ℂ (Set.range A)) := by
    let T := Submodule.span ℂ (Set.range fun k : Kc => fun X => Φ ((k.val⁻¹).val * X))
    let : FiniteDimensional ℂ T := hfin
    apply Submodule.finiteDimensional_of_le (S₂ := T)
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact T.smul_mem (η (GeneralLinear.determinant k.val) : ℂ) (Submodule.subset_span ⟨k, rfl⟩)
  have hshift (h : Kc) (X : Mat) :
      ∃ (c : ℂ) (Y : Mat), ∀ k, A (h⁻¹ * k) X = c * A k Y := by
    refine ⟨(η (GeneralLinear.determinant (h.val⁻¹)) : ℂ), h.val.val * X, fun k => ?_⟩
    simp only [A, complexCompactMatrixTranslate, Subgroup.coe_mul, Subgroup.coe_inv, map_mul,
      Units.val_mul, mul_inv_rev, inv_inv, mul_assoc]
  obtain ⟨κ, hκc, hκfin, hκ⟩ := exists_compactWeight_of_finite_orbit μ A hcont hA hshift
  refine ⟨κ, hκc, hκfin, fun X => (hκ X).trans ?_⟩
  simp only [A, complexCompactMatrixTranslate, OneMemClass.coe_one, map_one, Units.val_one,
    inv_one, one_mul]

end MatrixTest

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
