import Langlands.Representation.Archimedean.RealCoordinatePolynomials
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! # Nonzero smooth compact sections from polynomial averages -/

noncomputable section

open MeasureTheory
open scoped ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace Langlands.Archimedean

universe u v w

variable (A : Type u) [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
variable (V : Type v) [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Vector-valued combinations of real coordinate polynomials. -/
def vectorCoordinatePolynomials : Submodule ℂ (A → V) :=
  Submodule.span ℂ (Set.range fun p : (realCoordinatePolynomials A) × V => fun a => p.1.val a • p.2)

variable {A V}

omit [FiniteDimensional ℝ A] in
private theorem polynomial_smul_mem (p : A → ℂ) (hp : p ∈ realCoordinatePolynomials A) (v : V) :
    (fun a => p a • v) ∈ vectorCoordinatePolynomials A V :=
  Submodule.subset_span ⟨(⟨p, hp⟩, v), rfl⟩

/-- A vector-valued coordinate polynomial is smooth on the whole matrix algebra. -/
theorem contDiff_of_mem_vectorCoordinatePolynomials {f : A → V}
    (hf : f ∈ vectorCoordinatePolynomials A V) : ContDiff ℝ ∞ f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨p, v⟩, rfl⟩ := hf
    exact (contDiff_of_mem_realCoordinatePolynomials p.property).smul contDiff_const
  | zero => exact contDiff_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact contDiff_const.smul hf

private abbrev rightTranslateSpan (f : A → V) :=
  Submodule.span ℂ (Set.range fun b : A => fun a : A => f (a * b))

/-- A vector-valued coordinate polynomial has finitely many linearly
independent right translates, even before restricting to a compact subgroup. -/
theorem finiteDimensional_rightTranslateSpan_of_mem_vectorCoordinatePolynomials
    {f : A → V} (hf : f ∈ vectorCoordinatePolynomials A V) :
    FiniteDimensional ℂ (rightTranslateSpan f) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨p, v⟩, rfl⟩ := hf
    exact finiteDimensional_span_rightTranslate_smul_polynomial p.property v
  | zero =>
    have h : rightTranslateSpan (0 : A → V) = ⊥ := by
      apply bot_unique
      exact Submodule.span_le.mpr (fun f ⟨a, ha⟩ => ha ▸ Submodule.zero_mem _)
    rw [h]
    infer_instance
  | add f g _ _ hf hg =>
    let := hf
    let := hg
    apply Submodule.finiteDimensional_of_le (S₂ := rightTranslateSpan f ⊔ rightTranslateSpan g)
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact Submodule.mem_sup.mpr ⟨fun x => f (x * a), Submodule.subset_span ⟨a, rfl⟩,
      fun x => g (x * a), Submodule.subset_span ⟨a, rfl⟩, rfl⟩
  | smul c f _ hf =>
    let := hf
    apply Submodule.finiteDimensional_of_le (S₂ := rightTranslateSpan f)
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact (rightTranslateSpan f).smul_mem c (Submodule.subset_span ⟨a, rfl⟩)

section PolynomialDensity

variable {H : Type w} [TopologicalSpace H] [CompactSpace H] [T2Space H]
  [MeasurableSpace H] [BorelSpace H] (l : H → A)

private def restrictPolynomials : StarSubalgebra ℂ C(H, ℂ) where
  carrier := {g | ∃ p ∈ realCoordinatePolynomials A, ∀ h, g h = p (l h)}
  zero_mem' := ⟨0, (realCoordinatePolynomials A).zero_mem, fun _ => rfl⟩
  one_mem' := ⟨1, (realCoordinatePolynomials A).one_mem, fun _ => rfl⟩
  add_mem' := by
    rintro g g' ⟨p, hp, he⟩ ⟨q, hq, he'⟩
    exact ⟨p + q, (realCoordinatePolynomials A).add_mem hp hq, fun h => by
      rw [ContinuousMap.add_apply, he, he', Pi.add_apply]⟩
  mul_mem' := by
    rintro g g' ⟨p, hp, he⟩ ⟨q, hq, he'⟩
    exact ⟨p * q, (realCoordinatePolynomials A).mul_mem hp hq, fun h => by
      rw [ContinuousMap.mul_apply, he, he', Pi.mul_apply]⟩
  algebraMap_mem' c := ⟨algebraMap ℂ (A → ℂ) c, (realCoordinatePolynomials A).algebraMap_mem c,
    fun _ => rfl⟩
  star_mem' := by
    rintro g ⟨p, hp, he⟩
    exact ⟨star p, star_mem_realCoordinatePolynomials hp, fun h => by
      rw [ContinuousMap.star_apply, he, Pi.star_apply]⟩

omit [CompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] in
private theorem restrictPolynomials_separates (hl : Continuous l) (hl' : Function.Injective l) :
    (restrictPolynomials l).SeparatesPoints := by
  intro a b hab
  obtain ⟨L, hL⟩ := Module.Projective.exists_dual_ne_zero ℝ (sub_ne_zero.mpr (hl'.ne hab))
  let p : A → ℂ := fun x => (L x : ℂ)
  let f : C(H, ℂ) := ⟨p ∘ l, (contDiff_of_mem_realCoordinatePolynomials
    (realLinear_mem_realCoordinatePolynomials L)).continuous.comp hl⟩
  refine ⟨f, ⟨f, ⟨p, realLinear_mem_realCoordinatePolynomials L, fun _ => rfl⟩, rfl⟩, ?_⟩
  intro h
  apply hL
  rw [map_sub, sub_eq_zero]
  exact Complex.ofReal_injective h

variable [Group H] [IsTopologicalGroup H] (μ : Measure H) [μ.IsHaarMeasure]

omit [IsTopologicalGroup H] in
private theorem exists_polynomial_integral_ne_zero (hl : Continuous l) (hl' : Function.Injective l)
    (g : C(H, ℂ)) (hg : g ≠ 0) :
    ∃ p ∈ realCoordinatePolynomials A, (∫ h, p (l h) * g h ∂μ) ≠ 0 := by
  classical
  by_contra! hzero
  let Φ : C(H, ℂ) → ℂ := fun f => ∫ h, (f * g) h ∂μ
  have hΦ : Continuous Φ := by
    have hm : Continuous fun f : C(H, ℂ) => f * g := continuous_id.mul continuous_const
    have hi : Continuous fun f : Lp ℂ 1 μ => ∫ h, f h ∂μ := continuous_integral
    have hf := (ContinuousMap.toLp (E := ℂ) 1 μ ℂ).continuous
    have he : Φ = (fun f : Lp ℂ 1 μ => ∫ h, f h ∂μ) ∘
        (ContinuousMap.toLp (E := ℂ) 1 μ ℂ) ∘ (fun f => f * g) := by
      funext f
      exact (integral_congr_ae (ContinuousMap.coeFn_toLp (E := ℂ) (p := 1) (𝕜 := ℂ) μ
        (f * g))).symm
    rw [he]
    exact hi.comp (hf.comp hm)
  have hz : (restrictPolynomials l : Set C(H, ℂ)) ⊆ {f | Φ f = 0} := by
    rintro f ⟨p, hp, h⟩
    change (∫ y, (f * g) y ∂μ) = 0
    simp only [ContinuousMap.mul_apply, h, hzero p hp]
  have hd := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (restrictPolynomials l) (restrictPolynomials_separates l hl hl')
  have hcos : star g ∈ closure (restrictPolynomials l : Set C(H, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, hd]
    exact StarSubalgebra.mem_top
  have hInt : Φ (star g) = 0 := closure_minimal hz (isClosed_eq hΦ continuous_const) hcos
  have hpoint (h : H) : (star g * g) h = ((‖g h‖ ^ 2 : ℝ) : ℂ) := by
    simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply]
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hInt' : (∫ h, ‖g h‖ ^ 2 ∂μ) = 0 := by
    have hc : (∫ h, ((‖g h‖ ^ 2 : ℝ) : ℂ) ∂μ) = 0 := by
      simpa only [Φ, hpoint] using hInt
    rw [integral_complex_ofReal] at hc
    exact_mod_cast hc
  have hcont : Continuous fun h : H => ‖g h‖ ^ 2 := g.continuous.norm.pow 2
  have hae : (fun h => ‖g h‖ ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun h => sq_nonneg ‖g h‖)
      (integrableOn_univ.mp (hcont.continuousOn.integrableOn_compact isCompact_univ))).mp hInt'
  have hall : (fun h : H => ‖g h‖ ^ 2) = fun _ => (0 : ℝ) :=
    (Continuous.ae_eq_iff_eq μ hcont continuous_const).mp hae
  apply hg
  ext h
  change g h = 0
  have hh : ‖g h‖ ^ 2 = 0 := congrFun hall h
  exact norm_eq_zero.mp ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hh)

end PolynomialDensity

section Averaging

variable {H : Type w} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
  [FiniteDimensional ℂ V]

variable (ι : H →* Aˣ) (μ : Measure H) [μ.IsHaarMeasure] (ρ : Representation ℂ H V)
variable (hι : Continuous fun h => (ι h).val) (hρ : ∀ v : V, Continuous fun h => ρ h v)

/-- Average a scalar polynomial against one orbit of the compact inducing action. -/
def averagedPolynomialSection (p : A → ℂ) (v : V) (a : A) : V :=
  ∫ h, p ((ι h⁻¹).val * a) • ρ h v ∂μ

include hι hρ in
omit [FiniteDimensional ℂ V] in
private theorem averagedPolynomialSection_mem (p : A → ℂ) (hp : p ∈ realCoordinatePolynomials A)
    (v : V) : averagedPolynomialSection ι μ ρ p v ∈ vectorCoordinatePolynomials A V := by
  obtain ⟨I, _, f, g, hf, hg, h⟩ := exists_realCoordinatePolynomials_product_expansion hp
  let c (i : I) := ∫ y, f i (ι y⁻¹).val • ρ y v ∂μ
  have he : averagedPolynomialSection ι μ ρ p v = ∑ i, (fun a => g i a • c i) := by
    funext a
    rw [averagedPolynomialSection, Finset.sum_apply]
    have hsum (y : H) : p ((ι y⁻¹).val * a) • ρ y v =
        ∑ i, g i a • (f i (ι y⁻¹).val • ρ y v) := by
      rw [h, Finset.sum_smul]
      simp only [smul_smul, mul_comm]
    simp only [hsum]
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => integral_smul _ _
    · intro i _
      have hi := (contDiff_of_mem_realCoordinatePolynomials (hf i)).continuous.comp
        (hι.comp continuous_inv)
      exact integrableOn_univ.mp ((continuous_const.smul (hi.smul (hρ v))).continuousOn.integrableOn_compact
        isCompact_univ)
  rw [he]
  exact (vectorCoordinatePolynomials A V).sum_mem fun i _ => polynomial_smul_mem _ (hg i) (c i)

include hι hρ in
omit [NormedAlgebra ℝ A] [FiniteDimensional ℝ A] in
private theorem averagedPolynomialSection_covariant (p : A → ℂ) (hc : Continuous p) (v : V)
    (h : H) (a : A) :
    averagedPolynomialSection ι μ ρ p v ((ι h).val * a) =
      ρ h (averagedPolynomialSection ι μ ρ p v a) := by
  let := FiniteDimensional.complete ℂ V
  let T : V →L[ℂ] V := ⟨ρ h, (ρ h).continuous_of_finiteDimensional⟩
  have fint : Integrable (fun y => p ((ι y⁻¹).val * a) • ρ y v) μ :=
    integrableOn_univ.mp (((hc.comp ((hι.comp continuous_inv).mul continuous_const)).smul
      (hρ v)).continuousOn.integrableOn_compact isCompact_univ)
  unfold averagedPolynomialSection
  rw [← integral_mul_left_eq_self (μ := μ) (fun y => p ((ι y⁻¹).val * ((ι h).val * a)) • ρ y v) h]
  change _ = T (∫ y, p ((ι y⁻¹).val * a) • ρ y v ∂μ)
  rw [← T.integral_comp_comm fint]
  apply integral_congr_ae
  filter_upwards with y
  have hy : (ι (h * y)⁻¹).val * ((ι h).val * a) = (ι y⁻¹).val * a := by
    rw [← mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  change p ((ι (h * y)⁻¹).val * ((ι h).val * a)) • ρ (h * y) v =
    ρ h (p ((ι y⁻¹).val * a) • ρ y v)
  rw [hy, map_smul, map_mul, Module.End.mul_apply]

include hι hρ μ in
/-- A compact matrix inducing group acting on a nonzero finite-dimensional
space admits a nonzero smooth covariant polynomial section. -/
theorem exists_covariantPolynomialSection (hι' : Function.Injective ι) (v : V) (hv : v ≠ 0) :
    ∃ f : A → V, f ∈ vectorCoordinatePolynomials A V ∧ f 1 ≠ 0 ∧
      ∀ h a, f ((ι h).val * a) = ρ h (f a) := by
  let := FiniteDimensional.complete ℂ V
  obtain ⟨L, hL⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  let T : V →L[ℂ] ℂ := ⟨L, L.continuous_of_finiteDimensional⟩
  let g : C(H, ℂ) := ⟨fun h => T (ρ h v), T.continuous.comp (hρ v)⟩
  have hg : g ≠ 0 := by
    intro hz
    have h := congrArg (fun f : C(H, ℂ) => f 1) hz
    change L (ρ 1 v) = 0 at h
    rw [map_one, Module.End.one_apply, hL] at h
    exact one_ne_zero h
  have hinj : Function.Injective (fun h : H => (ι h⁻¹).val) :=
    Units.val_injective.comp (hι'.comp inv_injective)
  obtain ⟨p, hp, hne⟩ := exists_polynomial_integral_ne_zero
    (fun h => (ι h⁻¹).val) μ (hι.comp continuous_inv) hinj g hg
  let hc := (contDiff_of_mem_realCoordinatePolynomials hp).continuous
  refine ⟨_, averagedPolynomialSection_mem ι μ ρ hι hρ p hp v, ?_,
    averagedPolynomialSection_covariant ι μ ρ hι hρ p hc v⟩
  intro hz
  have hi : Integrable (fun h => p (ι h⁻¹).val • ρ h v) μ :=
    integrableOn_univ.mp (((hc.comp (hι.comp continuous_inv)).smul
      (hρ v)).continuousOn.integrableOn_compact isCompact_univ)
  apply hne
  calc
    (∫ h, p (ι h⁻¹).val * g h ∂μ) = ∫ h, T (p (ι h⁻¹).val • ρ h v) ∂μ := by
      apply integral_congr_ae
      filter_upwards with h
      rw [map_smul, smul_eq_mul]
      rfl
    _ = T (averagedPolynomialSection ι μ ρ p v 1) := by
      rw [T.integral_comp_comm hi]
      simp only [averagedPolynomialSection, mul_one]
    _ = 0 := by rw [hz, map_zero]

end Averaging

end Langlands.Archimedean
