import Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelReproduction

/-! # The diagonal of `α_χ` (Waldspurger VIII.4.1)

In the proof of Proposition VIII.4.1 (printed p.329), Waldspurger rewrites the diagonal of the
reproducing kernel as `α_χ(g, g) = ∫_G °e(g⁻¹ g' g) ψ(g') dg'`, where `ψ(a h) =
χ(a) mes(A_G ∩ H) mes(H)⁻²` on `A_G H` and `ψ = 0` outside, and then replaces `ψ` by its
product with the characteristic function of `G¹`, since `°e` is supported in `G¹`. This module
proves these steps for abstract data. The measure-theoretic input is the formula
`∫_{A × H} f(a h) = μ_A(A ∩ H) ∫_{A H} f dμ_G` for an open subgroup `H` with `μ_H` the
restriction of `μ_G`, proved here by Tonelli's theorem. A final lemma turns the integrability of
`|∫_G E(g⁻¹ g' g) ψ(g') dg'|` over a measure space read through a map into `G` (the conclusion
of Corollary VIII.3.2 in the application) into the diagonal hypothesis of
`IsSectionReproducingKernel.finiteDimensional`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace Langlands.HarishChandraSchwartz

universe u

section Product

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {A : Subgroup G} [MeasurableSpace A] [OpensMeasurableSpace A] {H : Subgroup G}

variable (A H) in
/-- The product set `A H = {a h | a ∈ A, h ∈ H}`. -/
def productSet : Set G := {g | ∃ a : A, (a : G)⁻¹ * g ∈ H}

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace A]
  [OpensMeasurableSpace A] in
theorem isOpen_productSet (hH : IsOpen (H : Set G)) : IsOpen (productSet A H) := by
  have : productSet A H = ⋃ a : A, (fun g => (a : G)⁻¹ * g) ⁻¹' (H : Set G) := by
    ext g
    simp [productSet]
  rw [this]
  exact isOpen_iUnion fun a => hH.preimage (continuous_const.mul continuous_id)

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableSpace A] [OpensMeasurableSpace A] in
theorem mul_mem_productSet (a : A) (h : H) : (a : G) * h ∈ productSet A H :=
  ⟨a, by simp⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] [OpensMeasurableSpace A] in
theorem measure_inv_mul_mem_eq (μA : Measure A) [MeasurableMul A] [μA.IsMulLeftInvariant]
    {g : G} (hg : g ∈ productSet A H) :
    μA {a : A | (a : G)⁻¹ * g ∈ H} = μA {a : A | (a : G) ∈ H} := by
  obtain ⟨a₀, ha₀⟩ := hg
  have hset : {a : A | (a : G)⁻¹ * g ∈ H} = (fun a => a₀⁻¹ * a) ⁻¹' {a : A | (a : G) ∈ H} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Subgroup.coe_mul, InvMemClass.coe_inv]
    constructor
    · intro h
      have := H.mul_mem ha₀ (H.inv_mem h)
      simpa [mul_assoc] using this
    · intro h
      have := H.mul_mem (H.inv_mem h) ha₀
      simpa [mul_assoc] using this
  rw [hset, measure_preimage_mul]

/-- **Integration over `A × H` and over `A H`**: for a left-invariant measure `μ_G`, a
left-invariant measure `μ_A` on `A` and a measure `μ_H` on the open subgroup `H` whose image
in `G` is the restriction of `μ_G` to `H`, `∫_{A × H} f(a h) = μ_A(A ∩ H) ∫_{A H} f dμ_G` for
every measurable `f ≥ 0`. -/
theorem lintegral_prod_mul_eq [MeasurableMul A] (hH : IsOpen (H : Set G)) (μG : Measure G)
    [μG.IsMulLeftInvariant] [SFinite μG] (μA : Measure A) [μA.IsMulLeftInvariant] [SFinite μA]
    (μH : Measure H) [SFinite μH] (hμH : μH.map Subtype.val = μG.restrict H)
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ p : A × H, f ((p.1 : G) * p.2) ∂(μA.prod μH) =
      μA {a : A | (a : G) ∈ H} * ∫⁻ g in productSet A H, f g ∂μG := by
  have hHm : MeasurableSet (H : Set G) := hH.measurableSet
  have hmA : Measurable (fun a : A => (a : G)) := continuous_subtype_val.measurable
  have hm : Measurable (fun p : A × H => f ((p.1 : G) * p.2)) :=
    hf.comp ((hmA.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd))
  rw [lintegral_prod _ hm.aemeasurable]
  have hinner : ∀ a : A, ∫⁻ h : H, f ((a : G) * h) ∂μH =
      ∫⁻ y, {y : G | (a : G)⁻¹ * y ∈ H}.indicator f y ∂μG := by
    intro a
    calc ∫⁻ h : H, f ((a : G) * h) ∂μH
        = ∫⁻ x in (H : Set G), f ((a : G) * x) ∂μG := by
          rw [← hμH]
          exact (lintegral_map (f := fun x => f ((a : G) * x))
            (hf.comp (measurable_const_mul _)) measurable_subtype_coe).symm
      _ = ∫⁻ x, {y : G | (a : G)⁻¹ * y ∈ H}.indicator f ((a : G) * x) ∂μG := by
          rw [← lintegral_indicator hHm]
          congr 1
          funext x
          by_cases hx : x ∈ H <;> simp [Set.indicator, hx]
      _ = ∫⁻ y, {y : G | (a : G)⁻¹ * y ∈ H}.indicator f y ∂μG :=
          lintegral_mul_left_eq_self _ _
  simp_rw [hinner]
  have hS : MeasurableSet {p : A × G | (p.1 : G)⁻¹ * p.2 ∈ H} :=
    ((hmA.comp measurable_fst).inv.mul measurable_snd) hHm
  have hmeas : AEMeasurable (Function.uncurry fun (a : A) (y : G) =>
      {y : G | (a : G)⁻¹ * y ∈ H}.indicator f y) (μA.prod μG) := by
    have : (Function.uncurry fun (a : A) (y : G) => {y : G | (a : G)⁻¹ * y ∈ H}.indicator f y) =
        {p : A × G | (p.1 : G)⁻¹ * p.2 ∈ H}.indicator (fun p => f p.2) := by
      funext p
      rcases p with ⟨a, y⟩
      rfl
    rw [this]
    exact ((hf.comp measurable_snd).indicator hS).aemeasurable
  rw [lintegral_lintegral_swap hmeas]
  have hpt : ∀ y : G, ∫⁻ a, {y : G | (a : G)⁻¹ * y ∈ H}.indicator f y ∂μA =
      (productSet A H).indicator (fun y => f y * μA {a : A | (a : G) ∈ H}) y := by
    intro y
    have hset : MeasurableSet {a : A | (a : G)⁻¹ * y ∈ H} :=
      (hmA.inv.mul measurable_const) hHm
    have : (fun a : A => {y : G | (a : G)⁻¹ * y ∈ H}.indicator f y) =
        {a : A | (a : G)⁻¹ * y ∈ H}.indicator (fun _ => f y) := by
      funext a
      simp [Set.indicator]
    rw [this, lintegral_indicator_const hset]
    by_cases hy : y ∈ productSet A H
    · rw [Set.indicator_of_mem hy, measure_inv_mul_mem_eq μA hy]
    · rw [Set.indicator_of_notMem hy]
      have hempty : {a : A | (a : G)⁻¹ * y ∈ H} = ∅ := by
        ext a
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hy ⟨a, h⟩
      rw [hempty, measure_empty, mul_zero]
  simp_rw [hpt]
  rw [lintegral_indicator (isOpen_productSet hH).measurableSet,
    lintegral_mul_const _ hf, mul_comm]

/-- The image of `μ_A × μ_H` under `(a, h) ↦ a h` is `μ_A(A ∩ H) · μ_G|_{A H}`. -/
theorem map_prod_mul_eq [MeasurableMul A] (hH : IsOpen (H : Set G)) (μG : Measure G)
    [μG.IsMulLeftInvariant] [SFinite μG] (μA : Measure A) [μA.IsMulLeftInvariant] [SFinite μA]
    (μH : Measure H) [SFinite μH] (hμH : μH.map Subtype.val = μG.restrict H) :
    (μA.prod μH).map (fun p : A × H => (p.1 : G) * p.2) =
      μA {a : A | (a : G) ∈ H} • μG.restrict (productSet A H) := by
  have hmA : Measurable (fun a : A => (a : G)) := continuous_subtype_val.measurable
  have hm : Measurable (fun p : A × H => (p.1 : G) * p.2) :=
    (hmA.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  ext s hs
  rw [Measure.map_apply hm hs, Measure.smul_apply, smul_eq_mul,
    ← lintegral_indicator_one (hm hs)]
  have h1 := lintegral_prod_mul_eq hH μG μA μH hμH (s.indicator 1)
    (measurable_one.indicator hs)
  have h2 : ∫⁻ p : A × H, ((fun p : A × H => (p.1 : G) * p.2) ⁻¹' s).indicator 1 p
      ∂(μA.prod μH) = ∫⁻ p : A × H, s.indicator 1 ((p.1 : G) * p.2) ∂(μA.prod μH) := by
    congr 1
  rw [h2, h1, lintegral_indicator_one hs]

/-- The integral form: `∫_{A × H} F(a h) = μ_A(A ∩ H) ∫_{A H} F dμ_G`. -/
theorem integral_prod_mul_eq [MeasurableMul A] (hH : IsOpen (H : Set G)) (μG : Measure G)
    [μG.IsMulLeftInvariant] [SFinite μG] (μA : Measure A) [μA.IsMulLeftInvariant] [SFinite μA]
    (μH : Measure H) [SFinite μH] (hμH : μH.map Subtype.val = μG.restrict H) {F : G → ℂ}
    (hF : AEStronglyMeasurable F (μG.restrict (productSet A H))) :
    ∫ p : A × H, F ((p.1 : G) * p.2) ∂(μA.prod μH) =
      (μA {a : A | (a : G) ∈ H}).toReal * ∫ g in productSet A H, F g ∂μG := by
  have hmA : Measurable (fun a : A => (a : G)) := continuous_subtype_val.measurable
  have hm : Measurable (fun p : A × H => (p.1 : G) * p.2) :=
    (hmA.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  have hmap := map_prod_mul_eq hH μG μA μH hμH
  have hF' : AEStronglyMeasurable F ((μA.prod μH).map (fun p : A × H => (p.1 : G) * p.2)) := by
    rw [hmap]
    exact hF.smul_measure _
  rw [← integral_map hm.aemeasurable hF', hmap, integral_smul_measure, Complex.real_smul]

/-- Integrability transfers from `μ_G|_{A H}` to `μ_A × μ_H` when `μ_A(A ∩ H) < ∞`. -/
theorem integrable_prod_mul [MeasurableMul A] (hH : IsOpen (H : Set G)) (μG : Measure G)
    [μG.IsMulLeftInvariant] [SFinite μG] (μA : Measure A) [μA.IsMulLeftInvariant] [SFinite μA]
    (μH : Measure H) [SFinite μH] (hμH : μH.map Subtype.val = μG.restrict H)
    (hfin : μA {a : A | (a : G) ∈ H} ≠ ⊤) {F : G → ℂ}
    (hF : Integrable F (μG.restrict (productSet A H))) :
    Integrable (fun p : A × H => F ((p.1 : G) * p.2)) (μA.prod μH) := by
  have hmA : Measurable (fun a : A => (a : G)) := continuous_subtype_val.measurable
  have hm : Measurable (fun p : A × H => (p.1 : G) * p.2) :=
    (hmA.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  have hmap := map_prod_mul_eq hH μG μA μH hμH
  have hF' : Integrable F ((μA.prod μH).map (fun p : A × H => (p.1 : G) * p.2)) := by
    rw [hmap]
    exact hF.smul_measure hfin
  exact (integrable_map_measure hF'.aestronglyMeasurable hm.aemeasurable).mp hF'

omit [SecondCountableTopology G] in
/-- **`φ * e = mes(H) φ`** for the characteristic function `e` of `H` and `φ` right invariant
under `H` (the second equality in Waldspurger's `φ * °e = φ * e = mes(H) φ`, proof of
Proposition VIII.4.1, printed p. 329). -/
theorem convolution_indicator_eq (μG : Measure G) [μG.IsMulLeftInvariant]
    (hH : MeasurableSet (H : Set G)) {φ : G → ℂ} (hφ : ∀ x, ∀ h ∈ H, φ (x * h) = φ x) (x : G) :
    convolution μG φ ((H : Set G).indicator fun _ => (1 : ℂ)) x = (μG H).toReal * φ x := by
  rw [convolution_apply]
  have hset : {h : G | h⁻¹ * x ∈ H} = (fun h => x⁻¹ * h) ⁻¹' (H : Set G) := by
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hh
      simpa using H.inv_mem hh
    · intro hh
      simpa using H.inv_mem hh
  have hmeas : MeasurableSet {h : G | h⁻¹ * x ∈ H} := by
    rw [hset]
    exact (measurable_const_mul _) hH
  have hpt : (fun h => φ h * (H : Set G).indicator (fun _ => (1 : ℂ)) (h⁻¹ * x)) =
      {h : G | h⁻¹ * x ∈ H}.indicator fun _ => φ x := by
    funext h
    by_cases hh : h⁻¹ * x ∈ H
    · rw [Set.indicator_of_mem (show h⁻¹ * x ∈ (H : Set G) from hh),
        Set.indicator_of_mem (show h ∈ {h : G | h⁻¹ * x ∈ H} from hh), mul_one]
      have := hφ x _ (H.inv_mem hh)
      simpa [mul_assoc] using this
    · rw [Set.indicator_of_notMem (show h⁻¹ * x ∉ (H : Set G) from hh),
        Set.indicator_of_notMem (show h ∉ {h : G | h⁻¹ * x ∈ H} from hh), mul_zero]
  rw [hpt, integral_indicator_const _ hmeas, measureReal_def, hset, measure_preimage_mul,
    Complex.real_smul]

omit [SecondCountableTopology G] in
/-- The hypothesis `hconv` of `KernelReproduction` from Waldspurger's identity `φ * °e = φ * e`
(Lemma VIII.2.3) and right invariance of `φ`, when `μ_H` is the restriction of `μ_G`. -/
theorem convolution_eq_of_convolution_eq_indicator (μG : Measure G) [μG.IsMulLeftInvariant]
    (hH : MeasurableSet (H : Set G)) {μH : Measure H} (hμH : μH.map Subtype.val = μG.restrict H)
    {φ E : G → ℂ} (hφ : ∀ x, ∀ h ∈ H, φ (x * h) = φ x)
    (hE : ∀ x, convolution μG φ E x = convolution μG φ ((H : Set G).indicator fun _ => 1) x)
    (x : G) : convolution μG φ E x = (μH Set.univ).toReal * φ x := by
  have hmes : μH Set.univ = μG H := by
    have := Measure.map_apply (μ := μH) measurable_subtype_coe (MeasurableSet.univ (α := G))
    rw [Set.preimage_univ] at this
    rw [← this, hμH, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [hE, convolution_indicator_eq μG hH hφ, hmes]

end Product

section Diagonal

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {A : Subgroup G} [MeasurableSpace A] [OpensMeasurableSpace A] {H : Subgroup G}

variable (A H) in
open Classical in
/-- The extension of `χ` to `A H`: `ψ̃(x) = χ(a)` for a chosen `a ∈ A` with `a⁻¹ x ∈ H`, and
`ψ̃(x) = 0` for `x ∉ A H`. If `χ` is trivial on `A ∩ H`, then `ψ̃(a h) = χ(a)`. -/
def centralCharacterExtension (χ : A →* ℂˣ) (x : G) : ℂ :=
  if hx : x ∈ productSet A H then (χ (Classical.choose hx) : ℂ) else 0

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableSpace A] [OpensMeasurableSpace A] in
theorem centralCharacterExtension_mul {χ : A →* ℂˣ} (hχH : ∀ a : A, (a : G) ∈ H → χ a = 1)
    (a : A) (h : H) : centralCharacterExtension A H χ ((a : G) * h) = χ a := by
  unfold centralCharacterExtension
  split_ifs with hx
  · have ha' : ((Classical.choose hx : A) : G)⁻¹ * ((a : G) * h) ∈ H := Classical.choose_spec hx
    have hmem : (((Classical.choose hx)⁻¹ * a : A) : G) ∈ H := by
      have := H.mul_mem ha' (H.inv_mem h.2)
      simpa [mul_assoc] using this
    have hone := hχH _ hmem
    rw [map_mul, map_inv, inv_mul_eq_one] at hone
    rw [hone]
  · exact absurd (mul_mem_productSet a h) hx

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableSpace A] [OpensMeasurableSpace A] in
theorem centralCharacterExtension_eq_zero {χ : A →* ℂˣ} {x : G} (hx : x ∉ productSet A H) :
    centralCharacterExtension A H χ x = 0 := by
  unfold centralCharacterExtension
  split_ifs
  rfl

variable (A) in
/-- Waldspurger's `ψ`: `ψ(a h) = χ(a) mes(A ∩ H) mes(H)⁻²` on `A H`, `0` outside, with
`mes(A ∩ H) = μ_A(A ∩ H)` and `mes(H) = μ_H(H)`. -/
def diagonalWeight (μA : Measure A) (χ : A →* ℂˣ) (μH : Measure H) (x : G) : ℂ :=
  ((μA {a : A | (a : G) ∈ H}).toReal : ℂ) * (((μH Set.univ).toReal : ℂ)⁻¹) ^ 2 *
    centralCharacterExtension A H χ x

variable {μA : Measure A} {χ : A →* ℂˣ} {μH : Measure H} {E : G → ℂ}

/-- **The diagonal of `α_χ`** (Waldspurger, proof of Proposition VIII.4.1, printed p.329):
`α_χ(g, g) = ∫_G E(g⁻¹ g' g) ψ(g') dg'`. -/
theorem kernelAlphaChi_diag_eq [MeasurableMul A] [MeasurableInv A] [μA.IsMulLeftInvariant]
    [μA.IsInvInvariant] [SFinite μA] [SFinite μH] (hH : IsOpen (H : Set G)) (μG : Measure G)
    [μG.IsMulLeftInvariant] [SFinite μG] (hμH : μH.map Subtype.val = μG.restrict H)
    (hAc : A ≤ Subgroup.center G) (hχH : ∀ a : A, (a : G) ∈ H → χ a = 1)
    (hfin : μA {a : A | (a : G) ∈ H} ≠ ⊤) (g : G)
    (hint : Integrable (fun x => E (g⁻¹ * x * g) * centralCharacterExtension A H χ x)
      (μG.restrict (productSet A H))) :
    kernelAlphaChi μA χ μH E g g = ∫ x, E (g⁻¹ * x * g) * diagonalWeight A μA χ μH x ∂μG := by
  set Φ : G → ℂ := fun x => E (g⁻¹ * x * g) * centralCharacterExtension A H χ x with hΦ
  set m : ℂ := (((μH Set.univ).toReal : ℂ)⁻¹) ^ 2 with hm
  have hpt : ∀ (a : A) (h : H), (χ a : ℂ) * E (g⁻¹ * h * ((a : G) * g)) = Φ ((a : G) * h) := by
    intro a h
    simp only [hΦ, centralCharacterExtension_mul hχH]
    have hc : (h : G) * a = a * h := Subgroup.mem_center_iff.mp (hAc a.2) h
    have : g⁻¹ * (h : G) * ((a : G) * g) = g⁻¹ * ((a : G) * h) * g := by
      simp only [mul_assoc]
      rw [← mul_assoc (h : G) (a : G) g, hc, mul_assoc]
    rw [this, mul_comm]
  have hprod := integrable_prod_mul hH μG μA μH hμH hfin hint
  rw [kernelAlphaChi_eq hAc]
  unfold kernelAlpha
  calc ∫ a, (χ a : ℂ) * (m * ∫ h, E (g⁻¹ * h * ((a : G) * g)) ∂μH) ∂μA
      = m * ∫ a, ∫ h, Φ ((a : G) * h) ∂μH ∂μA := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        dsimp only
        rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
        dsimp only
        rw [← hpt]
        ring
    _ = m * ∫ p : A × H, Φ ((p.1 : G) * p.2) ∂(μA.prod μH) := by
        rw [integral_prod _ hprod]
    _ = m * ((μA {a : A | (a : G) ∈ H}).toReal * ∫ x in productSet A H, Φ x ∂μG) := by
        rw [integral_prod_mul_eq hH μG μA μH hμH hint.aestronglyMeasurable]
    _ = ∫ x, E (g⁻¹ * x * g) * diagonalWeight A μA χ μH x ∂μG := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          simp only [hΦ, centralCharacterExtension_eq_zero hx, mul_zero]]
        rw [← integral_const_mul, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hΦ, hm, diagonalWeight]
        ring

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G]
  [MeasurableSpace A] [OpensMeasurableSpace A] in
/-- **Support in `G¹`**: if `E` vanishes outside a normal subgroup `N` (Waldspurger's `G¹`),
`ψ` can be replaced by its product with the characteristic function of `N`. -/
theorem integral_conj_mul_eq_indicator {N : Subgroup G} [N.Normal] (hE : ∀ x, x ∉ N → E x = 0)
    (μG : Measure G) (ψ : G → ℂ) (g : G) :
    ∫ x, E (g⁻¹ * x * g) * ψ x ∂μG = ∫ x, E (g⁻¹ * x * g) * (N : Set G).indicator ψ x ∂μG := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ N
  · simp only [Set.indicator_of_mem (show x ∈ (N : Set G) from hx)]
  · have hc : g⁻¹ * x * g ∉ N := fun h => hx (by
      have := ‹N.Normal›.conj_mem _ h g
      simpa [mul_assoc] using this)
    simp only [hE _ hc, zero_mul]

/-- **Integrability of the diagonal** on a measure space `X` read through `s : X → G`: if
`q ↦ α_χ(s q, s q)` is a.e. strongly measurable and
`∫⁻ |∫_G E((s q)⁻¹ g' (s q)) ψ(g') dg'| dν(q) < ∞`, then `q ↦ Re α_χ(s q, s q)` is integrable. -/
theorem integrable_re_kernelAlphaChi_diag [MeasurableMul A] [MeasurableInv A]
    [μA.IsMulLeftInvariant] [μA.IsInvInvariant] [SFinite μA] [SFinite μH]
    (hH : IsOpen (H : Set G)) (μG : Measure G) [μG.IsMulLeftInvariant] [SFinite μG]
    (hμH : μH.map Subtype.val = μG.restrict H) (hAc : A ≤ Subgroup.center G)
    (hχH : ∀ a : A, (a : G) ∈ H → χ a = 1) (hfin : μA {a : A | (a : G) ∈ H} ≠ ⊤)
    {X : Type*} [MeasurableSpace X] {ν : Measure X} {s : X → G}
    (hint : ∀ q, Integrable (fun x => E ((s q)⁻¹ * x * s q) * centralCharacterExtension A H χ x)
      (μG.restrict (productSet A H)))
    (hmeas : AEStronglyMeasurable (fun q => kernelAlphaChi μA χ μH E (s q) (s q)) ν)
    (hfinite : ∫⁻ q, ‖∫ x, E ((s q)⁻¹ * x * s q) * diagonalWeight A μA χ μH x ∂μG‖ₑ ∂ν < ⊤) :
    Integrable (fun q => (kernelAlphaChi μA χ μH E (s q) (s q)).re) ν := by
  have hI : Integrable (fun q => kernelAlphaChi μA χ μH E (s q) (s q)) ν := by
    refine ⟨hmeas, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [kernelAlphaChi_diag_eq hH μG hμH hAc hχH hfin _ (hint _)]
    exact hfinite
  exact hI.re

end Diagonal

end Langlands.HarishChandraSchwartz
