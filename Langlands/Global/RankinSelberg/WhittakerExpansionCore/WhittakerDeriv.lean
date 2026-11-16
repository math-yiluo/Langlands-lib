import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerBasic
import Langlands.Automorphic.CuspidalAdmissible.SquareZeroL2

/-! # Differentiating Whittaker functions along archimedean square-zero directions -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter Topology
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints

local instance derivSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance derivSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

section ArchPoint

variable {n : ℕ} {Z : ArchimedeanMatrix F n} (hZ : Z * Z = 0)

omit [NumberField F] in
/-- `(1 + sZ)(1 + tZ) = 1 + (s + t)Z` for square-zero `Z`. -/
theorem squareZeroElement_add_smul (s t : ℝ) :
    ArchimedeanGL.squareZeroElement ((s + t) • Z)
        (ArchimedeanGL.smul_mul_smul_eq_zero hZ (s + t)) =
      ArchimedeanGL.squareZeroElement (s • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ s) *
        ArchimedeanGL.squareZeroElement (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t) := by
  unfold ArchimedeanGL.squareZeroElement
  rw [← map_mul]
  congr 1
  apply Units.ext
  simp only [ArchimedeanGL.squareZeroUnit_val, Units.val_mul, add_mul, mul_add, one_mul,
    mul_one, smul_mul_smul_comm, hZ, smul_zero, add_zero, add_smul]
  abel

/-- The one-parameter subgroup `t ↦ 1 + tZ` is a homomorphism. -/
theorem archPoint_add_smul (s t : ℝ) :
    archPoint F n ((s + t) • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ (s + t)) =
      archPoint F n (s • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ s) *
        archPoint F n (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t) := by
  simp only [archPoint, squareZeroElement_add_smul F hZ, map_mul]

/-- `1 + 0 Z = 1`. -/
theorem archPoint_zero_smul :
    archPoint F n ((0 : ℝ) • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ 0) = 1 := by
  have h : ArchimedeanGL.squareZeroUnit ((0 : ℝ) • Z)
      (ArchimedeanGL.smul_mul_smul_eq_zero hZ 0) = 1 :=
    Units.ext (by simp)
  simp only [archPoint, ArchimedeanGL.squareZeroElement, h, map_one]

/-- The one-parameter subgroup `t ↦ 1 + tZ` is continuous. -/
theorem continuous_archPoint_smul :
    Continuous fun t : ℝ =>
      archPoint F n (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t) :=
  (GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous.comp
    ((AdelicGL.ofInfinite F n).continuous.comp (ArchimedeanGL.continuous_squareZeroElement_smul hZ))

end ArchPoint

local instance derivUnipotentLocallyCompact (n : ℕ) :
    LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

section Derivative

variable {r : ℕ} (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)

include hψ

/-- **Differentiation under the Whittaker integral.** If `f` and `f'` are continuous, left
invariant under rational points and bounded on determinant bands, and `f'` is the derivative of
`f` along the square-zero direction `Z` at every point, then `W_(f')` is the derivative of `W_f`
along `Z`. -/
theorem hasDerivAt_whittaker (f f' : Points F (r + 1) → ℂ) (hf : Continuous f)
    (hf' : Continuous f')
    (hfΓ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x, f (k * x) = f x)
    (hf'Γ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x,
      f' (k * x) = f' x)
    (hfb : ∀ lo hi : ℝ, 0 < lo → ∃ B : ℝ, ∀ x : Points F (r + 1),
      lo ≤ detNorm F (r + 1) x → detNorm F (r + 1) x ≤ hi → ‖f x‖ ≤ B)
    (hf'b : ∀ lo hi : ℝ, 0 < lo → ∃ B : ℝ, ∀ x : Points F (r + 1),
      lo ≤ detNorm F (r + 1) x → detNorm F (r + 1) x ≤ hi → ‖f' x‖ ≤ B)
    {Z : ArchimedeanMatrix F (r + 1)} (hZ : Z * Z = 0)
    (hd : ∀ x : Points F (r + 1), HasDerivAt (fun t : ℝ =>
      f (x * archPoint F (r + 1) (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t))) (f' x) 0)
    (g : Points F (r + 1)) :
    HasDerivAt (fun t : ℝ => whittaker F r ψ f
        (g * archPoint F (r + 1) (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t)))
      (whittaker F r ψ f' g) 0 := by
  set a : ℝ → Points F (r + 1) := fun t =>
    archPoint F (r + 1) (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t) with ha
  have ha0 : a 0 = 1 := archPoint_zero_smul F hZ
  have hadd : ∀ s t, a (s + t) = a s * a t := archPoint_add_smul F hZ
  have hac : Continuous a := continuous_archPoint_smul F hZ
  set d := detNorm F (r + 1) g with hdd
  have hd0 : 0 < d := detNorm_pos F (r + 1) g
  obtain ⟨B, hB⟩ := hfb (d / 2) (2 * d) (by positivity)
  obtain ⟨B', hB'⟩ := hf'b (d / 2) (2 * d) (by positivity)
  set s : Set ℝ := {t | detNorm F (r + 1) (g * a t) ∈ Set.Ioo (d / 2) (2 * d)} with hsdef
  have hs : s ∈ 𝓝 (0 : ℝ) := by
    have hc : Continuous fun t => detNorm F (r + 1) (g * a t) :=
      (continuous_detNorm F (r + 1)).comp (continuous_const.mul hac)
    refine hc.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
    simp only [ha0, mul_one, Set.mem_Ioo]
    constructor <;> linarith
  have hband : ∀ t ∈ s, ∀ u : unipotentAdelic F (r + 1),
      d / 2 ≤ detNorm F (r + 1) ((u : Points F (r + 1)) * (g * a t)) ∧
        detNorm F (r + 1) ((u : Points F (r + 1)) * (g * a t)) ≤ 2 * d := by
    intro t ht u
    rw [detNorm_mul, detNorm_unipotent, one_mul]
    exact ⟨ht.1.le, ht.2.le⟩
  set D := LeftCosetSpace.fundamentalDomain
    (rationalSubgroup F (Scheme F (r + 1)) (upperUnipotent F (r + 1)))
    (isDiscrete_rationalSubgroup F _ _) with hD
  set c := (quotientMassNormalizer F (Scheme F (r + 1)) (upperUnipotent F (r + 1))).toReal
  set χ := genericCharacter F r ψ (fun _ => 1) with hχ
  have hW : (fun t => whittaker F r ψ f (g * a t)) = fun t =>
      c • ∫ n in D, f ((n : Points F (r + 1)) * (g * a t)) * starRingEnd ℂ (χ n) ∂Measure.haar :=
    funext fun t => whittaker_eq_setIntegral F ψ hψ f hf hfΓ (g * a t)
  rw [hW, whittaker_eq_setIntegral F ψ hψ f' hf' hf'Γ g]
  refine HasDerivAt.const_smul c ?_
  have hχc : Continuous fun n : unipotentAdelic F (r + 1) => starRingEnd ℂ (χ n) :=
    Complex.continuous_conj.comp (continuous_genericCharacter F r ψ hψ.1 _)
  have hfin := haar_unipotentFundamentalDomain_lt_top F (r := r)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t (n : unipotentAdelic F (r + 1)) =>
      f ((n : Points F (r + 1)) * (g * a t)) * starRingEnd ℂ (χ n))
    (F' := fun t (n : unipotentAdelic F (r + 1)) =>
      f' ((n : Points F (r + 1)) * (g * a t)) * starRingEnd ℂ (χ n))
    (bound := fun _ => B') (x₀ := (0 : ℝ)) hs
    (Eventually.of_forall fun t =>
      ((hf.comp (continuous_subtype_val.mul continuous_const)).mul hχc).aestronglyMeasurable)
    (integrableOn_whittakerIntegrand F ψ hψ f hf (g * a 0) B fun u =>
      hB _ (hband 0 (mem_of_mem_nhds hs) u).1 (hband 0 (mem_of_mem_nhds hs) u).2)
    (((hf'.comp (continuous_subtype_val.mul continuous_const)).mul hχc).aestronglyMeasurable)
    (ae_of_all _ fun n t ht => by
      rw [norm_mul, Complex.norm_conj, norm_genericCharacter F r ψ hψ.2.2.2, mul_one]
      exact hB' _ (hband t ht n).1 (hband t ht n).2)
    (integrableOn_const hfin.ne)
    (ae_of_all _ fun n t _ => by
      have h1 : HasDerivAt (fun u : ℝ => f ((n : Points F (r + 1)) * (g * a t) * a u))
          (f' ((n : Points F (r + 1)) * (g * a t))) (t - t) := by
        rw [sub_self]
        exact hd ((n : Points F (r + 1)) * (g * a t))
      have h2 := h1.comp_sub_const t t
      refine HasDerivAt.mul_const ?_ _
      convert h2 using 1
      funext τ
      rw [mul_assoc, mul_assoc, ← hadd, add_sub_cancel])
  simpa only [ha0, mul_one] using hmain.2

end Derivative

end Langlands.Global.RankinSelbergGlobal.Unfolding
