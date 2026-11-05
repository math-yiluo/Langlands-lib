import Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelQuotient

/-! # Coefficients of `p_χ`-images (Waldspurger, proof of Theorem VIII.4.2)

In the proof of Theorem VIII.4.2 (printed pp. 330–331), Waldspurger computes the coefficients
of the representation `ρ` of `G` by right translations on `V = p_χ(°C(H \ G))`: for
`f₁ = p_χ φ₁` and `f₂ = p_χ φ₂`,
`(f₁, ρ(g) f₂)_{A_G\G} = ∫_{A_G\G} conj(f₁(g')) f₂(g' g) dg' = (p_χ(ˇφ̄₁ ∗ φ₂))(g)`
(formula (2)), and, for `f₁ = p_χ °e` with `conj(ˇ°e) = °e` (Remark VIII.2.2), and
`°e ∗ φ₂ = e ∗ φ₂ = mes(H) φ₂` (Lemma VIII.2.3), the reproducing identity
`f(g) = mes(H)⁻¹ (p_χ °e, ρ(g) f)_{A_G\G}`.

This module proves these computations for abstract data: the correlation
`x ↦ ∫_G conj(φ₁(g')) φ₂(g' x) dg'` (equal to `ˇφ̄₁ ∗ φ₂` for an inversion-invariant measure),
formula (2) on `G` and on `A \ G` (through the Weil formula of `KernelQuotient`), the identity
`e ∗ φ = mes(H) φ` for the characteristic function `e` of `H` and `φ` left invariant under `H`,
and the reproducing identity. The absolute convergence of the double integral is a hypothesis.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Langlands.QuotientIntegration
open scoped ComplexConjugate

namespace Langlands.HarishChandraSchwartz

universe u

section Correlation

variable {G : Type u} [Group G] [MeasurableSpace G]

/-- Waldspurger's `ˇφ̄₁ ∗ φ₂` written as a correlation:
`x ↦ ∫_G conj(φ₁(g')) φ₂(g' x) dμ_G(g')`. -/
def coefficientCorrelation (μG : Measure G) (φ₁ φ₂ : G → ℂ) (x : G) : ℂ :=
  ∫ g', conj (φ₁ g') * φ₂ (g' * x) ∂μG

/-- For an inversion-invariant measure the correlation is the convolution `ˇφ̄₁ ∗ φ₂`, where
`ˇφ̄₁(h) = conj(φ₁(h⁻¹))`. -/
theorem coefficientCorrelation_eq_convolution [MeasurableInv G] (μG : Measure G)
    [μG.IsInvInvariant] (φ₁ φ₂ : G → ℂ) (x : G) :
    coefficientCorrelation μG φ₁ φ₂ x = convolution μG (fun h => conj (φ₁ h⁻¹)) φ₂ x := by
  rw [convolution_apply, coefficientCorrelation]
  exact (integral_inv_eq_self (fun h => conj (φ₁ h) * φ₂ (h * x)) μG).symm

/-- For `E` with `ˇĒ = E` (that is, `conj(E(x⁻¹)) = E(x)`) and an inversion-invariant measure,
the correlation of `E` and `φ` is the convolution `E ∗ φ`. -/
theorem coefficientCorrelation_eq_convolution_self [MeasurableInv G] (μG : Measure G)
    [μG.IsInvInvariant] {E : G → ℂ} (hEc : ∀ x, conj (E x⁻¹) = E x)
    (φ : G → ℂ) (x : G) : coefficientCorrelation μG E φ x = convolution μG E φ x := by
  rw [coefficientCorrelation_eq_convolution]
  congr 1
  funext h
  exact hEc h

/-- **`e ∗ φ = mes(H) φ`** for the characteristic function `e` of `H` and `φ` left invariant
under `H` (the second equality in Waldspurger's `°e ∗ φ₂ = e ∗ φ₂ = mes(H) φ₂`, proof of
Theorem VIII.4.2, printed p. 331). -/
theorem indicator_convolution_eq (μG : Measure G) {H : Subgroup G}
    (hH : MeasurableSet (H : Set G)) {φ : G → ℂ} (hφ : ∀ h ∈ H, ∀ x, φ (h * x) = φ x) (x : G) :
    convolution μG ((H : Set G).indicator fun _ => (1 : ℂ)) φ x = (μG H).toReal * φ x := by
  rw [convolution_apply]
  have hpt : (fun h => (H : Set G).indicator (fun _ => (1 : ℂ)) h * φ (h⁻¹ * x)) =
      (H : Set G).indicator fun _ => φ x := by
    funext h
    by_cases hh : h ∈ H
    · rw [Set.indicator_of_mem (show h ∈ (H : Set G) from hh),
        Set.indicator_of_mem (show h ∈ (H : Set G) from hh), one_mul, hφ _ (H.inv_mem hh)]
    · rw [Set.indicator_of_notMem (show h ∉ (H : Set G) from hh),
        Set.indicator_of_notMem (show h ∉ (H : Set G) from hh), zero_mul]
  rw [hpt, integral_indicator_const _ hH, measureReal_def, Complex.real_smul]

/-- Waldspurger's `°e ∗ φ = mes(H) φ` from `°e ∗ φ = e ∗ φ` (Lemma VIII.2.3) and left
invariance of `φ`, when `μ_H` is the restriction of `μ_G`. -/
theorem convolution_eq_of_convolution_eq_indicator_left (μG : Measure G) {H : Subgroup G}
    (hH : MeasurableSet (H : Set G)) {μH : Measure H} (hμH : μH.map Subtype.val = μG.restrict H)
    {φ E : G → ℂ} (hφ : ∀ h ∈ H, ∀ x, φ (h * x) = φ x)
    (hE : ∀ x, convolution μG E φ x = convolution μG ((H : Set G).indicator fun _ => 1) φ x)
    (x : G) : convolution μG E φ x = (μH Set.univ).toReal * φ x := by
  have hmes : μH Set.univ = μG H := by
    have := Measure.map_apply (μ := μH) measurable_subtype_coe (MeasurableSet.univ (α := G))
    rw [Set.preimage_univ] at this
    rw [← this, hμH, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [hE, indicator_convolution_eq μG hH hφ, hmes]

end Correlation

section OnG

variable {G : Type u} [Group G] [MeasurableSpace G] [MeasurableMul G]
  {A : Subgroup G} [MeasurableSpace A] [MeasurableInv A]
  {μA : Measure A} [SFinite μA] [μA.IsInvInvariant]
  {μG : Measure G} [SFinite μG] [μG.IsMulLeftInvariant] {χ : A →* ℂˣ}

/-- The integrand `(g', a) ↦ χ(a) conj(φ₁(a g')) φ₂(g' g)` of the double integral behind
formula (2). -/
def coefficientIntegrand (χ : A →* ℂˣ) (φ₁ φ₂ : G → ℂ) (g : G) (p : G × A) : ℂ :=
  (χ p.2 : ℂ) * (conj (φ₁ ((p.2 : G) * p.1)) * φ₂ (p.1 * g))

omit [MeasurableMul G] [MeasurableInv A] [SFinite μA] [μA.IsInvInvariant] [SFinite μG]
  [μG.IsMulLeftInvariant] in
/-- The integrand is integrable when `(g', a) ↦ conj(φ₁(a g')) φ₂(g' g)` is (`|χ| = 1`). -/
theorem integrable_coefficientIntegrand (hχ : IsUnitaryCharacter χ) {φ₁ φ₂ : G → ℂ} (g : G)
    (hint : Integrable (fun p : G × A => conj (φ₁ ((p.2 : G) * p.1)) * φ₂ (p.1 * g))
      (μG.prod μA)) :
    Integrable (coefficientIntegrand χ φ₁ φ₂ g) (μG.prod μA) :=
  hint.bdd_mul (c := 1) ((hχ.measurable.comp measurable_snd).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => (hχ.norm_eq_one p.2).le)

omit [MeasurableSpace G] [MeasurableMul G] [MeasurableInv A] [SFinite μA] [μA.IsInvInvariant]
  [SFinite μG] [μG.IsMulLeftInvariant] in
/-- `conj((p_χ φ₁)(g')) φ₂(g' g) = ∫_A χ(a) conj(φ₁(a g')) φ₂(g' g) dμ_A(a)` for unitary `χ`. -/
theorem conj_centralProjection_mul_eq (hχ : IsUnitaryCharacter χ) (φ₁ φ₂ : G → ℂ)
    (g g' : G) :
    conj (centralProjection μA χ φ₁ g') * φ₂ (g' * g) =
      ∫ a, coefficientIntegrand χ φ₁ φ₂ g (g', a) ∂μA := by
  unfold centralProjection
  rw [← integral_conj, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [coefficientIntegrand, map_mul]
  rw [Units.val_inv_eq_inv_val, map_inv₀, ← Complex.inv_eq_conj (hχ.norm_eq_one a), inv_inv]
  ring

omit [MeasurableMul G] [MeasurableInv A] [μA.IsInvInvariant] [SFinite μG]
  [μG.IsMulLeftInvariant] in
/-- Under the absolute convergence of the double integral, `g' ↦ conj((p_χ φ₁)(g')) φ₂(g' g)` is
integrable on `G`. -/
theorem integrable_conj_centralProjection_mul (hχ : IsUnitaryCharacter χ) {φ₁ φ₂ : G → ℂ}
    (g : G)
    (hint : Integrable (fun p : G × A => conj (φ₁ ((p.2 : G) * p.1)) * φ₂ (p.1 * g))
      (μG.prod μA)) :
    Integrable (fun g' => conj (centralProjection μA χ φ₁ g') * φ₂ (g' * g)) μG := by
  refine (integrable_coefficientIntegrand hχ g hint).integral_prod_left.congr
    (Filter.Eventually.of_forall fun g' => ?_)
  exact (conj_centralProjection_mul_eq hχ φ₁ φ₂ g g').symm

/-- **Formula (2) of the proof of Theorem VIII.4.2, on `G`**:
`∫_G conj((p_χ φ₁)(g')) φ₂(g' g) dμ_G(g') = (p_χ(ˇφ̄₁ ∗ φ₂))(g)`, with `ˇφ̄₁ ∗ φ₂` written as
`coefficientCorrelation μ_G φ₁ φ₂`. -/
theorem integral_conj_centralProjection_mul (hAc : A ≤ Subgroup.center G)
    (hχ : IsUnitaryCharacter χ) {φ₁ φ₂ : G → ℂ} (g : G)
    (hint : Integrable (fun p : G × A => conj (φ₁ ((p.2 : G) * p.1)) * φ₂ (p.1 * g))
      (μG.prod μA)) :
    ∫ g', conj (centralProjection μA χ φ₁ g') * φ₂ (g' * g) ∂μG =
      centralProjection μA χ (coefficientCorrelation μG φ₁ φ₂) g := by
  have hF := integrable_coefficientIntegrand hχ g hint
  have hinner : ∀ a : A, ∫ g', coefficientIntegrand χ φ₁ φ₂ g (g', a) ∂μG =
      (χ a : ℂ) * coefficientCorrelation μG φ₁ φ₂ ((a : G)⁻¹ * g) := by
    intro a
    have hcomm : ∀ y : G, (a : G)⁻¹ * y = y * (a : G)⁻¹ := fun y =>
      ((Subgroup.mem_center_iff.mp (hAc (A.inv_mem a.2))) y).symm
    have := integral_mul_left_eq_self (μ := μG)
      (fun y => (χ a : ℂ) * (conj (φ₁ y) * φ₂ ((a : G)⁻¹ * y * g))) (a : G)
    simp only [inv_mul_cancel_left] at this
    simp only [coefficientIntegrand]
    rw [this, integral_const_mul, coefficientCorrelation]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hcomm y, mul_assoc]
  calc ∫ g', conj (centralProjection μA χ φ₁ g') * φ₂ (g' * g) ∂μG
      = ∫ g', ∫ a, coefficientIntegrand χ φ₁ φ₂ g (g', a) ∂μA ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall fun g' =>
          conj_centralProjection_mul_eq hχ φ₁ φ₂ g g')
    _ = ∫ a, ∫ g', coefficientIntegrand χ φ₁ φ₂ g (g', a) ∂μG ∂μA :=
        integral_integral_swap hF
    _ = ∫ a, (χ a : ℂ) * coefficientCorrelation μG φ₁ φ₂ ((a : G)⁻¹ * g) ∂μA := by
        simp only [hinner]
    _ = ∫ a, (((χ a)⁻¹ : ℂˣ) : ℂ) * coefficientCorrelation μG φ₁ φ₂ ((a : G) * g) ∂μA := by
        rw [← integral_inv_eq_self
          (fun a : A => (((χ a)⁻¹ : ℂˣ) : ℂ) * coefficientCorrelation μG φ₁ φ₂ ((a : G) * g))]
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        simp only [map_inv, inv_inv, InvMemClass.coe_inv]
    _ = centralProjection μA χ (coefficientCorrelation μG φ₁ φ₂) g := rfl

omit [MeasurableSpace G] [MeasurableMul G] [MeasurableInv A] [SFinite μA] [μA.IsInvInvariant]
  [SFinite μG] [μG.IsMulLeftInvariant] in
/-- `p_χ` is linear for scalar multiples: `p_χ(c φ) = c p_χ φ`. -/
theorem centralProjection_const_mul (c : ℂ) (φ : G → ℂ) (g : G) :
    centralProjection μA χ (fun x => c * φ x) g = c * centralProjection μA χ φ g := by
  unfold centralProjection
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  ring

end OnG

section Quotient

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {A : Subgroup G} (hA : IsClosed (A : Set G))
  [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  {μA : Measure A} [SFinite μA] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
  [MeasurableInv A] [μA.IsInvInvariant]
  {μG : Measure G} [IsFiniteMeasureOnCompacts μG] [SFinite μG] [μG.IsMulLeftInvariant]
  {ν : Measure (LeftQuotient A)} {χ : A →* ℂˣ}

include hA in
/-- **Formula (2) of the proof of Theorem VIII.4.2**:
`(p_χ φ₁, ρ(g) p_χ φ₂)_{A\G} = ∫_{A\G} conj((p_χ φ₁)(q̇)) (p_χ φ₂)(q̇ g) dν(q)
= (p_χ(ˇφ̄₁ ∗ φ₂))(g)`, where `q̇ = Quotient.out q`, `ν` is compatible with `μ_G` and `μ_A`, and
`ˇφ̄₁ ∗ φ₂` is written as `coefficientCorrelation μ_G φ₁ φ₂`. -/
theorem integral_conj_centralProjection_mul_centralProjection [MeasurableMul A]
    (hν : IsCompatible A μG μA ν) (hAc : A ≤ Subgroup.center G) (hχ : IsUnitaryCharacter χ)
    {φ₁ φ₂ : G → ℂ} (g : G)
    (hint : Integrable (fun p : G × A => conj (φ₁ ((p.2 : G) * p.1)) * φ₂ (p.1 * g))
      (μG.prod μA)) :
    ∫ q, conj (centralProjection μA χ φ₁ q.out) * centralProjection μA χ φ₂ (q.out * g) ∂ν =
      centralProjection μA χ (coefficientCorrelation μG φ₁ φ₂) g := by
  have h := integral_centralProjection_mul_conj hA hν hχ (K := centralProjection μA χ φ₁)
    (φ := fun x => φ₂ (x * g)) (fun b g₁ => centralProjection_mul_left φ₁ b g₁)
    (integrable_conj_centralProjection_mul hχ g hint)
  rw [← integral_conj_centralProjection_mul hAc hχ g hint, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [centralProjection, mul_assoc]
  ring

include hA in
/-- **Reproducing identity** (proof of Theorem VIII.4.2, printed p. 331): for `E` with `ˇĒ = E`
(Waldspurger's `°e`, by Remark VIII.2.2), an inversion-invariant `μ_G` and `E ∗ φ = c φ`
(Waldspurger's `°e ∗ φ₂ = mes(H) φ₂`, by Lemma VIII.2.3),
`(p_χ E, ρ(g) p_χ φ)_{A\G} = c (p_χ φ)(g)`. -/
theorem integral_conj_centralProjection_mul_centralProjection_eq_mul [MeasurableMul A]
    [MeasurableInv G] [μG.IsInvInvariant]
    (hν : IsCompatible A μG μA ν) (hAc : A ≤ Subgroup.center G) (hχ : IsUnitaryCharacter χ)
    {E φ : G → ℂ} (hEc : ∀ x, conj (E x⁻¹) = E x) {c : ℂ}
    (hconv : ∀ x, convolution μG E φ x = c * φ x) (g : G)
    (hint : Integrable (fun p : G × A => conj (E ((p.2 : G) * p.1)) * φ (p.1 * g))
      (μG.prod μA)) :
    ∫ q, conj (centralProjection μA χ E q.out) * centralProjection μA χ φ (q.out * g) ∂ν =
      c * centralProjection μA χ φ g := by
  rw [integral_conj_centralProjection_mul_centralProjection hA hν hAc hχ g hint,
    ← centralProjection_const_mul]
  congr 1
  funext x
  rw [coefficientCorrelation_eq_convolution_self μG hEc, hconv]

include hA in
/-- **`f(g) = mes(H)⁻¹ (p_χ °e, ρ(g) f)_{A\G}`** (proof of Theorem VIII.4.2, printed p. 331) for
`f = p_χ φ`, `φ` left invariant under `H`, `E` with `ˇĒ = E` and
`E ∗ φ = e ∗ φ` for the characteristic function `e` of `H` (Lemma VIII.2.3), when `μ_H` is the
restriction of `μ_G` to `H` and `mes(H) ≠ 0`. -/
theorem centralProjection_eq_inv_mul_integral [MeasurableMul A] [MeasurableInv G]
    [μG.IsInvInvariant] (hν : IsCompatible A μG μA ν) (hAc : A ≤ Subgroup.center G)
    (hχ : IsUnitaryCharacter χ) {H : Subgroup G} (hH : MeasurableSet (H : Set G))
    {μH : Measure H} (hμH : μH.map Subtype.val = μG.restrict H)
    (hmes : (μH Set.univ).toReal ≠ 0) {E φ : G → ℂ} (hEc : ∀ x, conj (E x⁻¹) = E x)
    (hφ : ∀ h ∈ H, ∀ x, φ (h * x) = φ x)
    (hE : ∀ x, convolution μG E φ x = convolution μG ((H : Set G).indicator fun _ => 1) φ x)
    (g : G)
    (hint : Integrable (fun p : G × A => conj (E ((p.2 : G) * p.1)) * φ (p.1 * g))
      (μG.prod μA)) :
    centralProjection μA χ φ g = ((μH Set.univ).toReal : ℂ)⁻¹ *
      ∫ q, conj (centralProjection μA χ E q.out) * centralProjection μA χ φ (q.out * g) ∂ν := by
  rw [integral_conj_centralProjection_mul_centralProjection_eq_mul hA hν hAc hχ hEc
    (convolution_eq_of_convolution_eq_indicator_left μG hH hμH hφ hE) g hint, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hmes), one_mul]

end Quotient

end Langlands.HarishChandraSchwartz
