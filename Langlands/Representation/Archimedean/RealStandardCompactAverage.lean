import Langlands.Representation.Archimedean.RealInductionStagesFamily
import Langlands.Representation.Archimedean.RealReverseTransfer

/-! # Compact polynomial averages on real standard modules -/

noncomputable section

open MeasureTheory
open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealStandardCompactAverage

open GramFormula OrthogonalFinitePolynomial PrincipalSeriesExtension

local notation "G" => Langlands.GeneralLinear
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℝ
local notation "V" => fun n ds => kFiniteFunctions (realStandardModule n ds)
  (unitaryCompact ℝ n)

variable {n : ℕ}
variable (μ : Measure (K n)) [hμ : μ.IsHaarMeasure]

/-- Right translation by `g` followed by convolution against `φ` on the compact group. -/
def average (φ : C(K n, ℂ)) (g : G n ℝ) (f : G n ℝ → ℂ) : G n ℝ → ℂ :=
  fun x => ∫ k, φ k * f (x * Unitary.toUnits k * g) ∂μ

private theorem continuous_integrand {f : G n ℝ → ℂ} (hf : Continuous f)
    (φ : C(K n, ℂ)) (g x : G n ℝ) :
    Continuous fun k => φ k * f (x * Unitary.toUnits k * g) :=
  φ.continuous.mul (hf.comp ((continuous_const.mul continuous_unitary_toUnits).mul
    continuous_const))

private theorem compact_average_eq (φ : C(K n, ℂ)) (g : G n ℝ) (f : G n ℝ → ℂ) (x : K n) :
    average μ φ g f (Unitary.toUnits x) =
      ∫ y, φ (x⁻¹ * y) * f (Unitary.toUnits y * g) ∂μ := by
  rw [average, ← integral_mul_left_eq_self (μ := μ) (fun y : K n =>
    φ (x⁻¹ * y) * f (Unitary.toUnits y * g)) x]
  simp only [inv_mul_cancel_left, map_mul]

private theorem exists_column_span {h : K n → K n → ℂ} (hh : h ∈ separated n) :
    ∃ S : Submodule ℂ (K n → ℂ), FiniteDimensional ℂ S ∧ ∀ y, (fun x => h x y) ∈ S := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨a, _, b, rfl⟩ := hh
    refine ⟨ℂ ∙ a, inferInstance, fun y => ?_⟩
    have ha : a ∈ ℂ ∙ a := Submodule.mem_span_singleton_self a
    convert (ℂ ∙ a).smul_mem (b y) ha using 1
    ext x
    exact mul_comm _ _
  | zero =>
    exact ⟨⊥, inferInstance, fun _ => zero_mem _⟩
  | add h h' _ _ ih ih' =>
    obtain ⟨S, hS, hh⟩ := ih
    obtain ⟨T, hT, hh'⟩ := ih'
    let := hS
    let := hT
    exact ⟨S ⊔ T, inferInstance, fun y => Submodule.add_mem_sup (hh y) (hh' y)⟩
  | smul c h _ ih =>
    obtain ⟨S, hS, hh⟩ := ih
    exact ⟨S, hS, fun y => S.smul_mem c (hh y)⟩

include hμ in
private theorem exists_compact_average_span {φ : C(K n, ℂ)} (hφ : φ ∈ polynomialStar n) :
    ∃ S : Submodule ℂ (K n → ℂ), FiniteDimensional ℂ S ∧
      ∀ (g : G n ℝ) (f : G n ℝ → ℂ), Continuous f →
        (fun x => average μ φ g f (Unitary.toUnits x)) ∈ S := by
  have hφ' : φ ∈ (polynomialStar n).toSubalgebra := hφ
  rw [polynomialStar_toSubalgebra] at hφ'
  obtain ⟨S, hS, hcol⟩ := exists_column_span (inv_mul_mem_separated hφ')
  let := hS
  refine ⟨S, hS, fun g f hf => ?_⟩
  simp_rw [compact_average_eq]
  apply InductionStages.integral_mem μ S
  · intro y
    convert S.smul_mem (f (Unitary.toUnits y * g)) (hcol y) using 1
    ext x
    exact mul_comm _ _
  · intro x
    exact integrable_of_continuous μ
      ((φ.continuous.comp (continuous_const.mul continuous_id)).mul
        (hf.comp (continuous_unitary_toUnits.mul continuous_const)))

omit hμ in
private theorem average_equivariance {ds : List RealBlock}
    {f : G n ℝ → ℂ} (hf : f ∈ principalSeries ℝ n (realPositionCharacter ds))
    (φ : C(K n, ℂ)) (g x : G n ℝ) (a : Fin n → ℝˣ)
    (u : Langlands.GeneralLinear.upperUnipotent n ℝ) :
    average μ φ g f (Iwasawa.diagonalUnits a * u * x) =
      principalSeriesCharacter ℝ n (realPositionCharacter ds) a * average μ φ g f x := by
  rw [average, average, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  change φ k * f ((Iwasawa.diagonalUnits a * u * x) * Unitary.toUnits k * g) = _
  rw [show (Iwasawa.diagonalUnits a * u * x) * Unitary.toUnits k * g =
    Iwasawa.diagonalUnits a * u * (x * Unitary.toUnits k * g) by simp only [mul_assoc], hf.2]
  ring

private theorem average_blockFourierCoefficient {ds : List RealBlock}
    {f : G n ℝ → ℂ} (hf : f ∈ realStandardModule n ds)
    (φ : C(K n, ℂ)) (g : G n ℝ) (p : ℕ) (d : ComplexCharacterData)
    (hd : realInducedBlockAt ds p = some d) (j : ℤ) (hj : |j| < |d.weight|) (x : G n ℝ) :
    blockFourierCoefficient n p j (average μ φ g f) x = 0 := by
  let e (θ : ℝ) : ℂ := Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I))
  let F (θ : ℝ) (k : K n) :=
    φ k * f (blockRotation n p θ * (x * Unitary.toUnits k * g)) * e θ
  have hF : Continuous (Function.uncurry F) := by
    have he : Continuous e := by
      unfold e
      exact Complex.continuous_exp.comp (by fun_prop)
    have hu : Continuous (Unitary.toUnits : K n → G n ℝ) := continuous_unitary_toUnits
    have hrot := continuous_blockRotation n p
    have hfc := hf.1.1.continuous
    exact ((φ.continuous.comp continuous_snd).mul
      (hfc.comp ((hrot.comp continuous_fst).mul
        ((continuous_const.mul (hu.comp continuous_snd)).mul continuous_const)))).mul
      (he.comp continuous_fst)
  have hi : Integrable (Function.uncurry F)
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod μ) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact (hF.continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_univ)).mono_set
        (Set.prod_mono Set.uIoc_subset_uIcc le_rfl)
  have hswap := intervalIntegral_integral_swap hi
  unfold blockFourierCoefficient
  simp only [average, ← integral_mul_const, mul_assoc (blockRotation n p _)]
  change (∫ θ in (0 : ℝ)..2 * Real.pi, ∫ k, F θ k ∂μ) = 0
  rw [hswap]
  refine (integral_congr_ae (ae_of_all _ fun k => ?_)).trans (integral_zero _ _)
  change (∫ θ in (0 : ℝ)..2 * Real.pi,
    φ k * f (blockRotation n p θ * (x * Unitary.toUnits k * g)) * e θ) = 0
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
  change φ k * blockFourierCoefficient n p j f (x * (Unitary.toUnits k * g)) = 0
  rw [hf.2 p d hd j hj, mul_zero]

include hμ in
theorem average_mem {ds : List RealBlock} {φ : C(K n, ℂ)} (hφ : φ ∈ polynomialStar n)
    (g : G n ℝ) {f : G n ℝ → ℂ} (hf : f ∈ realStandardModule n ds) :
    average μ φ g f ∈ V n ds := by
  let q (x : K n) := average μ φ g f (Unitary.toUnits x)
  have hfg : Continuous fun y : K n => f (Unitary.toUnits y * g) :=
    hf.1.1.continuous.comp (continuous_unitary_toUnits.mul continuous_const)
  have hq : q ∈ polynomialFunctions n := by
    convert convolution_mem_polynomialFunctions μ hfg hφ using 1
    funext x
    change (∫ y, φ y * f (Unitary.toUnits x * Unitary.toUnits y * g) ∂μ) =
      ∫ y, φ y * f (Unitary.toUnits (x * y) * g) ∂μ
    simp only [map_mul]
  obtain ⟨P, hP⟩ := exists_mvPolynomial_of_mem_polynomialFunctions hq
  have hqcont : Continuous q := by
    have h := funext hP
    rw [h]
    exact P.continuous_eval.comp (continuous_pi fun ij =>
      Complex.continuous_ofReal.comp (continuous_subtype_val.matrix_elem ij.1 ij.2))
  have hqfin : FiniteDimensional ℂ (translateSpan q) := by
    have h := funext hP
    rw [h]
    exact TranslateFinite.finiteDimensional_span_eval P
  have hcov := average_equivariance (μ := μ) hf.1 φ g
  have hqsign (a : Fin n → ℝˣ) (k : K n) :
      q (signDiagonal (fun i => (a i : ℝ)) * k) =
        principalSeriesCharacter ℝ n (realPositionCharacter ds)
          (fun i => signUnit (a i)) * q k := by
    change average μ φ g f (Unitary.toUnits (signDiagonal _ * k)) = _
    rw [PartialJacquet.signDiagonal_toUnits]
    have hk := hcov (Unitary.toUnits k) (fun i => signUnit (a i)) 1
    simpa only [OneMemClass.coe_one, mul_one] using hk
  let e := realPositionExponent ds
  have hExt := extension_mem_kFiniteFunctions e (realPositionCharacter_eq_signUnit_mul ds)
    hqcont hqfin hqsign
  have heq : average μ φ g f = extension (shiftedExponent n e) q := by
    funext x
    obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact x
    rw [hcov, hExt.1.2]
    rw [← RealReverseTransfer.toUnits_mk hk, extension_unitary]
  exact ⟨⟨heq.symm ▸ hExt.1, average_blockFourierCoefficient μ hf φ g⟩,
    heq.symm ▸ hExt.2⟩

/-- The average acts by a finite-rank endomorphism of the compact-finite standard module. -/
def averageMap (ds : List RealBlock) (φ : polynomialStar n) (g : G n ℝ) :
    Module.End ℂ (V n ds) where
  toFun := fun f => ⟨average μ φ g f, average_mem μ φ.2 g f.2.1⟩
  map_add' := by
    intro f h
    apply Subtype.ext
    funext x
    simp only [average, Submodule.coe_add, Pi.add_apply, mul_add]
    exact integral_add
      (integrable_of_continuous μ (continuous_integrand f.2.1.1.1.continuous φ g x))
      (integrable_of_continuous μ (continuous_integrand h.2.1.1.1.continuous φ g x))
  map_smul' := by
    intro a f
    apply Subtype.ext
    funext x
    simp only [average, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun _ => by ring)

@[simp]
theorem averageMap_apply_coe (ds : List RealBlock) (φ : polynomialStar n) (g : G n ℝ)
    (f : V n ds) : (averageMap μ ds φ g f : G n ℝ → ℂ) = average μ φ g f := rfl

instance finiteDimensional_range_averageMap (ds : List RealBlock) (φ : polynomialStar n)
    (g : G n ℝ) : FiniteDimensional ℂ (LinearMap.range (averageMap μ ds φ g)) := by
  obtain ⟨S, hS, hmem⟩ := exists_compact_average_span μ φ.2
  let := hS
  let U := LinearMap.range (averageMap μ ds φ g)
  let R : U →ₗ[ℂ] (K n → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Unitary.toUnits : K n → G n ℝ)).comp
      ((V n ds).subtype.comp U.subtype)
  have hR : ∀ f : U, R f ∈ S := by
    rintro ⟨_, f, rfl⟩
    exact hmem g f f.2.1.1.1.continuous
  refine FiniteDimensional.of_injective (R.codRestrict S hR) ?_
  intro f h hh
  have heq := congrArg Subtype.val hh
  apply Subtype.ext
  apply Subtype.ext
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries f.1.2.1.1 h.1.2.1.1 ?_
  intro k hk
  rw [← RealReverseTransfer.toUnits_mk hk]
  exact congrFun heq _

/-- Compact polynomial averages of all right translates have finite-dimensional range. -/
def RealStandardCompactAverageStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (K n)) [μ.IsHaarMeasure] (ds : List RealBlock)
    (φ : polynomialStar n) (g : G n ℝ),
    FiniteDimensional ℂ (LinearMap.range (averageMap μ ds φ g))

omit hμ in
theorem realStandardCompactAverage : RealStandardCompactAverageStatement :=
  fun _ μ _ ds φ g => finiteDimensional_range_averageMap μ ds φ g

end Langlands.Archimedean.RealStandardCompactAverage
