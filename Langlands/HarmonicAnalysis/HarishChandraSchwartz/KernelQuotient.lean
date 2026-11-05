import Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelReproduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SectionReproducingKernel
import Langlands.Analysis.Local.QuotientWeilKernel
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # The reproducing kernel `α_χ` on `A \ G` (Waldspurger VIII.4.1)

Waldspurger's hermitian product on `p_χ(°C_H)` is `(f₁, f₂)_{A_G\G} = ∫_{A_G\G} conj(f₁) f₂`,
and his formula (1) states `(α_χ(·, g), f)_{A_G\G} = f(g)`. This module proves the first
equality of (1), `(α_χ(·, g), p_χ φ)_{A_G\G} = ∫_G conj(α_χ(g', g)) φ(g') dg'`, through the Weil
formula for a compatible quotient measure on `A \ G`, and combines it with
`KernelReproduction` and `SectionReproducingKernel`: under explicit hypotheses on a space `V`
of functions `p_χ φ`, the kernel `y ↦ α_χ(·, y)` is a reproducing kernel for `V` read through
the representatives `Quotient.out`, and `V` is finite dimensional when `q ↦ Re α_χ(q, q)` is
integrable on `A \ G`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Langlands.QuotientIntegration
open scoped ComplexConjugate

namespace Langlands.HarishChandraSchwartz

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {A : Subgroup G} (hA : IsClosed (A : Set G))
  [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  {μA : Measure A} [SFinite μA] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
  {μG : Measure G} [IsFiniteMeasureOnCompacts μG] {ν : Measure (LeftQuotient A)}

include hA in
/-- **Weil formula** for integrable complex functions, read through representatives:
`∫_{A\G} ∫_A F(a q̇) dμ_A(a) dν(q) = ∫_G F dμ_G`, where `q̇ = Quotient.out q`. -/
theorem integral_integral_out_eq [MeasurableMul A] (hν : IsCompatible A μG μA ν) {F : G → ℂ}
    (hF : Integrable F μG) :
    ∫ q, ∫ a, F ((a : G) * q.out) ∂μA ∂ν = ∫ g, F g ∂μG := by
  have hcomp := orbitKernel_comp A hA μA μG ν hν
  rw [← hcomp] at hF ⊢
  have hF' := hF
  rw [Measure.comp_eq_comp_const_apply] at hF'
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp hF', Kernel.const_apply]
  have hae := Measure.ae_integrable_of_integrable_comp hF
  refine integral_congr_ae (hae.mono fun q hq => ?_)
  have hq' : orbitKernel A hA μA q = Measure.map (fun a : A => (a : G) * q.out) μA := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  dsimp only
  rw [hq'] at hq ⊢
  exact (integral_map ((continuous_subtype_val.mul continuous_const).measurable.aemeasurable)
    hq.aestronglyMeasurable).symm

variable {χ : A →* ℂˣ}

include hA in
/-- For `χ`-covariant `K` and unitary `χ`, the quotient product of `p_χ φ` against `K` is the
integral over `G` of `conj(K) φ`: `∫_{A\G} (p_χ φ)(q̇) conj(K(q̇)) dν(q) = ∫_G conj(K) φ dμ_G`. -/
theorem integral_centralProjection_mul_conj [MeasurableMul A] (hν : IsCompatible A μG μA ν)
    (hχ : IsUnitaryCharacter χ) {K φ : G → ℂ} (hK : ∀ (a : A) (g : G), K ((a : G) * g) = χ a * K g)
    (hint : Integrable (fun g => conj (K g) * φ g) μG) :
    ∫ q, centralProjection μA χ φ q.out * conj (K q.out) ∂ν = ∫ g, conj (K g) * φ g ∂μG := by
  rw [← integral_integral_out_eq hA hν hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  dsimp only
  unfold centralProjection
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [hK, map_mul]
  rw [Units.val_inv_eq_inv_val, Complex.inv_eq_conj (hχ.norm_eq_one a)]
  ring

variable {H : Subgroup G} {μH : Measure H} {E : G → ℂ}

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] [BorelSpace A] [MeasurableSpace (LeftQuotient A)]
  [BorelSpace (LeftQuotient A)] [SFinite μA] [IsFiniteMeasureOnCompacts μA] in
/-- `α_χ(·, g₂)` is `χ`-covariant: `α_χ(b g₁, g₂) = χ(b) α_χ(g₁, g₂)` for `b ∈ A`. -/
theorem kernelAlphaChi_mul_left [MeasurableMul A] (b : A) (g₁ g₂ : G) :
    kernelAlphaChi μA χ μH E ((b : G) * g₁) g₂ = χ b * kernelAlphaChi μA χ μH E g₁ g₂ :=
  centralProjection_mul_left _ b g₁

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] [BorelSpace A] [MeasurableSpace (LeftQuotient A)]
  [BorelSpace (LeftQuotient A)] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
  [IsFiniteMeasureOnCompacts μG] in
/-- Under the absolute convergence of the triple integral, `g' ↦ conj(α_χ(g', g)) φ(g')` is
integrable on `G`. -/
theorem integrable_conj_kernelAlphaChi_mul [SFinite μG] [SFinite μH] [MeasurableInv A]
    [μA.IsInvInvariant] (hAc : A ≤ Subgroup.center G) (hχ : IsUnitaryCharacter χ)
    (hE : ∀ x, conj (E x) = E x) {φ : G → ℂ} (g : G)
    (hint : Integrable (fun p : G × A × H => E (p.1⁻¹ * p.2.2 * ((p.2.1 : G) * g)) * φ p.1)
      (μG.prod (μA.prod μH))) :
    Integrable (fun g' => conj (kernelAlphaChi μA χ μH E g' g) * φ g') μG := by
  set m : ℂ := ((μH Set.univ).toReal : ℂ) with hm
  set F : G × (A × H) → ℂ := fun p =>
    (((χ p.2.1)⁻¹ : ℂˣ) : ℂ) * (m⁻¹ ^ 2 * (E (p.1⁻¹ * p.2.2 * ((p.2.1 : G) * g)) * φ p.1))
    with hF
  have hFint : Integrable F (μG.prod (μA.prod μH)) := by
    have h1 := hint.const_mul (m⁻¹ ^ 2)
    refine h1.bdd_mul (c := 1)
      ((hχ.measurable_inv.comp (measurable_fst.comp measurable_snd)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => (hχ.norm_inv p.2.1).le)
  refine hFint.integral_prod_left.congr (hFint.prod_right_ae.mono fun g' hg' => ?_)
  dsimp only
  rw [integral_prod _ hg', conj_kernelAlphaChi hAc hχ hE, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [hF, kernelAlpha]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [hm]
  ring

include hA in
/-- **Formula (1) of the proof of Proposition VIII.4.1** on `A \ G`:
`(α_χ(·, g), p_χ φ)_{A\G} = ∫_{A\G} (p_χ φ)(q̇) conj(α_χ(q̇, g)) dν(q) = (p_χ φ)(g)`. -/
theorem integral_centralProjection_mul_conj_kernelAlphaChi [MeasurableMul A] [SFinite μG]
    [SFinite μH] [MeasurableInv A] [μA.IsInvInvariant] (hν : IsCompatible A μG μA ν)
    (hAc : A ≤ Subgroup.center G) (hχ : IsUnitaryCharacter χ) (hE : ∀ x, conj (E x) = E x)
    {φ : G → ℂ} (hH : ∀ h ∈ H, ∀ x, φ (h * x) = φ x)
    (hconv : ∀ x, convolution μG φ E x = (μH Set.univ).toReal * φ x)
    (hmes : (μH Set.univ).toReal ≠ 0) (g : G)
    (hint : Integrable (fun p : G × A × H => E (p.1⁻¹ * p.2.2 * ((p.2.1 : G) * g)) * φ p.1)
      (μG.prod (μA.prod μH))) :
    ∫ q, centralProjection μA χ φ q.out * conj (kernelAlphaChi μA χ μH E q.out g) ∂ν =
      centralProjection μA χ φ g := by
  rw [integral_centralProjection_mul_conj hA hν hχ
    (K := fun g' => kernelAlphaChi μA χ μH E g' g) (fun b g₁ => kernelAlphaChi_mul_left b g₁ g)
    (integrable_conj_kernelAlphaChi_mul hAc hχ hE g hint)]
  exact integral_conj_kernelAlphaChi_mul hAc hχ hE hH hconv hmes g hint

/-- The hypotheses on a space `V` of functions on `G` (for Waldspurger's `p_χ(°C_H)`): every
`f ∈ V` is `p_χ φ` for some `φ` that is left invariant under `H`, satisfies
`φ * E = mes(H) φ`, and has absolutely convergent triple integrals at every `g`. -/
def IsKernelAlphaChiSpace (μG : Measure G) (μA : Measure A) (χ : A →* ℂˣ) (μH : Measure H)
    (E : G → ℂ) (V : Submodule ℂ (G → ℂ)) : Prop :=
  ∀ f ∈ V, ∃ φ : G → ℂ, f = centralProjection μA χ φ ∧ (∀ h ∈ H, ∀ x, φ (h * x) = φ x) ∧
    (∀ x, convolution μG φ E x = (μH Set.univ).toReal * φ x) ∧
    ∀ g, Integrable (fun p : G × A × H => E (p.1⁻¹ * p.2.2 * ((p.2.1 : G) * g)) * φ p.1)
      (μG.prod (μA.prod μH))

include hA in
/-- Under these hypotheses, if every `α_χ(·, y)` lies in `V` and the products
`f(q̇) conj(f'(q̇))` are integrable on `A \ G`, then `y ↦ α_χ(·, y)` is a reproducing kernel
for `V` read through `Quotient.out`. -/
theorem isSectionReproducingKernel_kernelAlphaChi [MeasurableMul A] [SFinite μG] [SFinite μH]
    [MeasurableInv A] [μA.IsInvInvariant] (hν : IsCompatible A μG μA ν)
    (hAc : A ≤ Subgroup.center G) (hχ : IsUnitaryCharacter χ) (hE : ∀ x, conj (E x) = E x)
    (hmes : (μH Set.univ).toReal ≠ 0) {V : Submodule ℂ (G → ℂ)}
    (hV : IsKernelAlphaChiSpace μG μA χ μH E V)
    (hKV : ∀ y, (fun g => kernelAlphaChi μA χ μH E g y) ∈ V)
    (hprod : ∀ f ∈ V, ∀ f' ∈ V,
      Integrable (fun q : LeftQuotient A => f q.out * conj (f' q.out)) ν) :
    IsSectionReproducingKernel ν Quotient.out V (fun y => ⟨_, hKV y⟩) where
  integrable := hprod
  reproduce f hf y := by
    obtain ⟨φ, rfl, hH, hconv, hint⟩ := hV f hf
    exact integral_centralProjection_mul_conj_kernelAlphaChi hA hν hAc hχ hE hH hconv hmes y
      (hint y)

include hA in
/-- **Proposition VIII.4.1 in abstract form**: under the hypotheses of
`isSectionReproducingKernel_kernelAlphaChi`, if `q ↦ Re α_χ(q̇, q̇)` is integrable on `A \ G`,
then `V` is finite dimensional. -/
theorem finiteDimensional_of_kernelAlphaChi [MeasurableMul A] [SFinite μG] [SFinite μH]
    [MeasurableInv A] [μA.IsInvInvariant] (hν : IsCompatible A μG μA ν)
    (hAc : A ≤ Subgroup.center G) (hχ : IsUnitaryCharacter χ) (hE : ∀ x, conj (E x) = E x)
    (hmes : (μH Set.univ).toReal ≠ 0) {V : Submodule ℂ (G → ℂ)}
    (hV : IsKernelAlphaChiSpace μG μA χ μH E V)
    (hKV : ∀ y, (fun g => kernelAlphaChi μA χ μH E g y) ∈ V)
    (hprod : ∀ f ∈ V, ∀ f' ∈ V,
      Integrable (fun q : LeftQuotient A => f q.out * conj (f' q.out)) ν)
    (hdiag : Integrable (fun q : LeftQuotient A => (kernelAlphaChi μA χ μH E q.out q.out).re) ν) :
    FiniteDimensional ℂ V :=
  (isSectionReproducingKernel_kernelAlphaChi hA hν hAc hχ hE hmes hV hKV hprod).finiteDimensional
    hdiag

end Langlands.HarishChandraSchwartz
