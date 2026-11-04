import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralProjection

/-! # The kernel `α_χ` and its reproducing identity on `G` (Waldspurger VIII.4.1)

In the proof of Proposition VIII.4.1, Waldspurger sets, for a compact open subgroup `H` and the
cuspidal projection `°e` of the characteristic function of `H`,
`α(g₁, g₂) = mes(H)⁻² ∫_H °e(g₁⁻¹ h g₂) dh` and
`α_χ(g₁, g₂) = ∫_{A_G} α(g₁ a, g₂) χ⁻¹(a) da = ∫_{A_G} α(g₁, a g₂) χ(a) da`, and proves, for
`f = p_χ φ` with `φ ∈ °C_H`, the identity
`(α_χ(·, g), f)_{A_G\G} = ∫_G conj(α_χ(g', g)) φ(g') dg' = f(g)`.

This module proves the second equality for abstract data: a function `E` (for `°e`) with real
values, a function `φ` that is left invariant under `H` and satisfies `φ * E = mes(H) φ` (for
`φ ∈ °C_H` this is Lemma VIII.2.3), a central subgroup `A` with an inversion-invariant measure
and a unitary character `χ`, under the absolute convergence of the triple integral.
-/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Langlands.HarishChandraSchwartz

universe u

variable {G : Type u} [Group G] [MeasurableSpace G] {H : Subgroup G}

/-- Waldspurger's `α(g₁, g₂) = mes(H)⁻² ∫_H E(g₁⁻¹ h g₂) dh`, with `mes(H) = μ_H(H)`. -/
def kernelAlpha (μH : Measure H) (E : G → ℂ) (g₁ g₂ : G) : ℂ :=
  (((μH Set.univ).toReal : ℂ)⁻¹) ^ 2 * ∫ h, E (g₁⁻¹ * h * g₂) ∂μH

variable {A : Subgroup G} [MeasurableSpace A]

/-- Waldspurger's `α_χ(g₁, g₂) = ∫_A χ(a)⁻¹ α(a g₁, g₂) da`, i.e. `α_χ(·, g₂) = p_χ α(·, g₂)`. -/
def kernelAlphaChi (μA : Measure A) (χ : A →* ℂˣ) (μH : Measure H) (E : G → ℂ) (g₁ g₂ : G) :
    ℂ :=
  centralProjection μA χ (fun g => kernelAlpha μH E g g₂) g₁

variable {μH : Measure H} {E : G → ℂ}

/-- `α` is real when `E` is. -/
theorem conj_kernelAlpha (hE : ∀ x, conj (E x) = E x) (g₁ g₂ : G) :
    conj (kernelAlpha μH E g₁ g₂) = kernelAlpha μH E g₁ g₂ := by
  unfold kernelAlpha
  rw [map_mul, ← integral_conj, map_pow, map_inv₀, Complex.conj_ofReal]
  simp_rw [hE]

omit [MeasurableSpace A] in
/-- For central `a`, `α(a g₁, g₂) = α(g₁, a⁻¹ g₂)`. -/
theorem kernelAlpha_mul_left (hA : A ≤ Subgroup.center G) (a : A) (g₁ g₂ : G) :
    kernelAlpha μH E ((a : G) * g₁) g₂ = kernelAlpha μH E g₁ ((a : G)⁻¹ * g₂) := by
  unfold kernelAlpha
  congr 2
  funext h
  have hc : (h : G) * (a : G)⁻¹ = (a : G)⁻¹ * h :=
    Subgroup.mem_center_iff.mp (hA (A.inv_mem a.2)) h
  rw [mul_inv_rev]
  simp only [mul_assoc]
  rw [← mul_assoc ((a : G)⁻¹) (h : G) g₂, ← hc, mul_assoc]

variable {μA : Measure A} {χ : A →* ℂˣ}

/-- Waldspurger's second expression: `α_χ(g₁, g₂) = ∫_A α(g₁, a g₂) χ(a) da`. -/
theorem kernelAlphaChi_eq [MeasurableInv A] [μA.IsInvInvariant] (hA : A ≤ Subgroup.center G)
    (g₁ g₂ : G) :
    kernelAlphaChi μA χ μH E g₁ g₂ = ∫ a, (χ a : ℂ) * kernelAlpha μH E g₁ ((a : G) * g₂) ∂μA := by
  unfold kernelAlphaChi centralProjection
  simp_rw [kernelAlpha_mul_left hA]
  rw [← integral_inv_eq_self (fun a : A => (χ a : ℂ) * kernelAlpha μH E g₁ ((a : G) * g₂)) μA]
  simp only [map_inv, InvMemClass.coe_inv]

/-- `conj α_χ(g₁, g₂) = ∫_A χ(a)⁻¹ α(g₁, a g₂) da` for unitary `χ` and real `E`. -/
theorem conj_kernelAlphaChi [MeasurableInv A] [μA.IsInvInvariant] (hA : A ≤ Subgroup.center G)
    (hχ : IsUnitaryCharacter χ) (hE : ∀ x, conj (E x) = E x) (g₁ g₂ : G) :
    conj (kernelAlphaChi μA χ μH E g₁ g₂) =
      ∫ a, (((χ a)⁻¹ : ℂˣ) : ℂ) * kernelAlpha μH E g₁ ((a : G) * g₂) ∂μA := by
  rw [kernelAlphaChi_eq hA, ← integral_conj]
  congr 1
  funext a
  rw [map_mul, conj_kernelAlpha hE]
  congr 1
  rw [Units.val_inv_eq_inv_val, Complex.inv_eq_conj (hχ.norm_eq_one a)]

variable [SFinite μA] [SFinite μH]

/-- **Formula (1) of the proof of Proposition VIII.4.1, on `G`**: if `E` is real, `φ` is left
invariant under `H` and `φ * E = mes(H) φ`, and the triple integral converges absolutely, then
`∫_G conj(α_χ(g', g)) φ(g') dg' = (p_χ φ)(g)`. -/
theorem integral_conj_kernelAlphaChi_mul {μ : Measure G} [SFinite μ] [MeasurableInv A]
    [μA.IsInvInvariant] (hA : A ≤ Subgroup.center G) (hχ : IsUnitaryCharacter χ)
    (hE : ∀ x, conj (E x) = E x) {φ : G → ℂ} (hH : ∀ h ∈ H, ∀ x, φ (h * x) = φ x)
    (hconv : ∀ x, convolution μ φ E x = (μH Set.univ).toReal * φ x)
    (hmes : (μH Set.univ).toReal ≠ 0) (g : G)
    (hint : Integrable (fun p : G × A × H => E (p.1⁻¹ * p.2.2 * ((p.2.1 : G) * g)) * φ p.1)
      (μ.prod (μA.prod μH))) :
    ∫ g', conj (kernelAlphaChi μA χ μH E g' g) * φ g' ∂μ = centralProjection μA χ φ g := by
  set m : ℂ := ((μH Set.univ).toReal : ℂ) with hm
  have hm0 : m ≠ 0 := Complex.ofReal_ne_zero.mpr hmes
  set F : G → A × H → ℂ := fun g' q =>
    (((χ q.1)⁻¹ : ℂˣ) : ℂ) * (m⁻¹ ^ 2 * (E (g'⁻¹ * q.2 * ((q.1 : G) * g)) * φ g')) with hF
  have hFint : Integrable (Function.uncurry F) (μ.prod (μA.prod μH)) := by
    have h1 := hint.const_mul (m⁻¹ ^ 2)
    refine h1.bdd_mul (c := 1)
      ((hχ.measurable_inv.comp (measurable_fst.comp measurable_snd)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => (hχ.norm_inv p.2.1).le)
  -- the integrand at `g'` is the iterated integral of `F g'`
  have hstep : ∀ g', conj (kernelAlphaChi μA χ μH E g' g) * φ g' =
      ∫ a, ∫ h, F g' (a, h) ∂μH ∂μA := by
    intro g'
    rw [conj_kernelAlphaChi hA hχ hE, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [hF, kernelAlpha]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only [hm]
    ring
  -- the inner integral over `G`
  have hinner : ∀ q : A × H, ∫ g', F g' q ∂μ =
      (((χ q.1)⁻¹ : ℂˣ) : ℂ) * m⁻¹ * φ ((q.1 : G) * g) * 1 := by
    intro q
    simp only [hF]
    rw [integral_const_mul, integral_const_mul]
    have hc : ∫ g', E (g'⁻¹ * q.2 * ((q.1 : G) * g)) * φ g' ∂μ =
        m * φ ((q.1 : G) * g) := by
      have := hconv ((q.2 : G) * ((q.1 : G) * g))
      rw [convolution_apply, hH q.2 q.2.2] at this
      rw [← this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
      simp only [mul_assoc, mul_comm (φ g')]
    rw [hc]
    field_simp
  calc ∫ g', conj (kernelAlphaChi μA χ μH E g' g) * φ g' ∂μ
      = ∫ g', ∫ q, F g' q ∂(μA.prod μH) ∂μ := by
        refine integral_congr_ae (hFint.prod_right_ae.mono fun g' hg' => ?_)
        dsimp only
        rw [hstep]
        exact (integral_prod (F g') hg').symm
    _ = ∫ q, ∫ g', F g' q ∂μ ∂(μA.prod μH) := integral_integral_swap hFint
    _ = ∫ q : A × H, (((χ q.1)⁻¹ : ℂˣ) : ℂ) * m⁻¹ * φ ((q.1 : G) * g) * 1 ∂(μA.prod μH) :=
        integral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = (∫ a, (((χ a)⁻¹ : ℂˣ) : ℂ) * m⁻¹ * φ ((a : G) * g) ∂μA) * ∫ _h, (1 : ℂ) ∂μH :=
        integral_prod_mul (fun a : A => (((χ a)⁻¹ : ℂˣ) : ℂ) * m⁻¹ * φ ((a : G) * g))
          (fun _ : H => (1 : ℂ))
    _ = centralProjection μA χ φ g := by
        rw [integral_const, Complex.real_smul, mul_one, measureReal_def, ← hm,
          ← integral_mul_const]
        unfold centralProjection
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        field_simp

end Langlands.HarishChandraSchwartz
