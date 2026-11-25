import Langlands.Representation.Archimedean.DixmierMalliavin
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# The Dixmier–Malliavin theorem on a product with a totally disconnected factor

For a Lie group `A` with a closed linear realization and a locally compact Hausdorff second
countable group `B`:

* `Langlands.Hecke.convolutionIntegral_prod_tensor`: the convolution of pure tensors on `A × B`
  for a product measure is the tensor product of the convolutions;
* `exists_eq_sum_slice_mul_cosetIndicator`: a compactly supported continuous function on `A × B`
  right invariant under an open subgroup `V` of `B` is a finite sum of its slices tensored with
  indicators of cosets of `V`;
* `exists_eq_sum_convolutionIntegral_prod`: such a function with smooth slices, for compact open
  `V`, is a finite sum of convolutions `φᵢ ⋆ ψᵢ` (left Haar measure on `A × B`) of functions of the
  same kind, with the invariance properties that the Library's adelic test functions ask for.

The proof decomposes `f` into slices, factors each slice on `A` with
`Langlands.Archimedean.exists_eq_sum_gardingKernelConvolution`, and uses
`1_{bV} ⋆ 1_V = μ_B(V) 1_{bV}` on `B` and the comparison of the Haar measure of `A × B` with the
product of Haar measures of the factors.
-/

noncomputable section

open MeasureTheory Measure Set Filter Topology Pointwise
open scoped Manifold ContDiff CompactlySupported

namespace Langlands.Hecke

/-- **Convolution of pure tensors on a product group.** For s-finite measures on `A` and `B`,
`(u ⊗ w) ⋆ (u' ⊗ w') = (u ⋆ u') ⊗ (w ⋆ w')` for the product measure (`integral_prod_mul`; no
integrability is needed). -/
theorem convolutionIntegral_prod_tensor {A B : Type*} [Group A] [Group B] [MeasurableSpace A]
    [MeasurableSpace B] (μA : Measure A) (μB : Measure B) [SFinite μA] [SFinite μB]
    (u u' : A → ℂ) (w w' : B → ℂ) (x : A × B) :
    convolutionIntegral (μA.prod μB) (fun p => u p.1 * w p.2) (fun p => u' p.1 * w' p.2) x =
      convolutionIntegral μA u u' x.1 * convolutionIntegral μB w w' x.2 := by
  simp only [convolutionIntegral]
  have h : ∀ p : A × B, (u p.1 * w p.2) * (u' (p⁻¹ * x).1 * w' (p⁻¹ * x).2) =
      (u p.1 * u' (p.1⁻¹ * x.1)) * (w p.2 * w' (p.2⁻¹ * x.2)) := by
    intro p
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
    ring
  simp_rw [h]
  exact integral_prod_mul (fun a : A => u a * u' (a⁻¹ * x.1)) (fun b : B => w b * w' (b⁻¹ * x.2))

end Langlands.Hecke

namespace Langlands.Analysis.DixmierMalliavin

section Cosets

variable {B : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] (V : Subgroup B)

/-- The indicator function of the left coset `b V`. -/
def cosetIndicator (b : B) : B → ℂ := (b • (V : Set B)).indicator 1

open scoped Classical in
omit [TopologicalSpace B] [IsTopologicalGroup B] in
/-- `cosetIndicator V b y` is `1` if `b⁻¹ y ∈ V` and `0` otherwise. -/
theorem cosetIndicator_apply (b y : B) :
    cosetIndicator V b y = if b⁻¹ * y ∈ V then 1 else 0 := by
  unfold cosetIndicator
  by_cases h : b⁻¹ * y ∈ V
  · rw [indicator_of_mem ((mem_leftCoset_iff b).2 h), ite_eq_left h]; rfl
  · rw [indicator_of_notMem (fun h' => h ((mem_leftCoset_iff b).1 h')), ite_eq_right h]

omit [TopologicalSpace B] [IsTopologicalGroup B] in
/-- The indicator of `b V` is right invariant under `V`. -/
theorem cosetIndicator_mul (b y : B) {v : B} (hv : v ∈ V) :
    cosetIndicator V b (y * v) = cosetIndicator V b y := by
  classical
  rw [cosetIndicator_apply, cosetIndicator_apply]
  have : b⁻¹ * (y * v) ∈ V ↔ b⁻¹ * y ∈ V := by
    rw [← mul_assoc]; exact Subgroup.mul_mem_cancel_right V hv
  by_cases h : b⁻¹ * y ∈ V
  · rw [ite_eq_left (this.2 h), ite_eq_left h]
  · rw [ite_eq_right (mt this.1 h), ite_eq_right h]

omit [TopologicalSpace B] [IsTopologicalGroup B] in
/-- The indicator of `b V` is left invariant under `b V b⁻¹`. -/
theorem cosetIndicator_mul_left (b y : B) {v : B} (hv : b⁻¹ * v * b ∈ V) :
    cosetIndicator V b (v * y) = cosetIndicator V b y := by
  classical
  rw [cosetIndicator_apply, cosetIndicator_apply]
  have e : b⁻¹ * (v * y) = (b⁻¹ * v * b) * (b⁻¹ * y) := by group
  have : b⁻¹ * (v * y) ∈ V ↔ b⁻¹ * y ∈ V := by
    rw [e]; exact Subgroup.mul_mem_cancel_left V hv
  by_cases h : b⁻¹ * y ∈ V
  · rw [ite_eq_left (this.2 h), ite_eq_left h]
  · rw [ite_eq_right (mt this.1 h), ite_eq_right h]

/-- Cosets of an open subgroup are open and closed. -/
theorem isClopen_coset (hVo : IsOpen (V : Set B)) (b : B) : IsClopen (b • (V : Set B)) :=
  ⟨(V.isClosed_of_isOpen hVo).smul b, hVo.smul b⟩

/-- The indicator of a coset of an open subgroup is continuous. -/
theorem continuous_cosetIndicator (hVo : IsOpen (V : Set B)) (b : B) :
    Continuous (cosetIndicator V b) :=
  (isClopen_coset V hVo b).continuous_indicator continuous_const

/-- The indicator of a coset of a compact subgroup has compact support. -/
theorem hasCompactSupport_cosetIndicator (hVc : IsCompact (V : Set B)) (b : B) :
    HasCompactSupport (cosetIndicator V b) :=
  HasCompactSupport.of_support_subset_isCompact (hVc.smul b) support_indicator_subset

/-- `1_{bV} ⋆ 1_V = μ(V) 1_{bV}` for a left invariant measure `μ` and an open subgroup `V`. -/
theorem convolutionIntegral_cosetIndicator [MeasurableSpace B] [BorelSpace B] (μB : Measure B)
    [μB.IsMulLeftInvariant] (hVo : IsOpen (V : Set B)) (b y : B) :
    Hecke.convolutionIntegral μB (cosetIndicator V b) (cosetIndicator V 1) y =
      (μB.real V : ℂ) * cosetIndicator V b y := by
  classical
  rw [Hecke.convolutionIntegral]
  by_cases hy : b⁻¹ * y ∈ V
  · have h : ∀ b', cosetIndicator V b b' * cosetIndicator V 1 (b'⁻¹ * y) =
        cosetIndicator V b b' := by
      intro b'
      rw [cosetIndicator_apply V 1, inv_one, one_mul]
      by_cases hb' : b⁻¹ * b' ∈ V
      · have : b'⁻¹ * y ∈ V := by
          have := V.mul_mem (V.inv_mem hb') hy
          simpa [mul_assoc] using this
        rw [ite_eq_left this, mul_one]
      · rw [cosetIndicator_apply V b, ite_eq_right hb', zero_mul]
    simp_rw [h]
    rw [cosetIndicator_apply V b, ite_eq_left hy, mul_one, cosetIndicator,
      integral_indicator ((hVo.smul b).measurableSet)]
    simp only [Pi.one_apply]
    rw [setIntegral_const, Complex.real_smul, mul_one, measureReal_def, measureReal_def,
      measure_smul]
  · have h : ∀ b', cosetIndicator V b b' * cosetIndicator V 1 (b'⁻¹ * y) = 0 := by
      intro b'
      rw [cosetIndicator_apply V 1, inv_one, one_mul, cosetIndicator_apply V b]
      by_cases hb' : b⁻¹ * b' ∈ V
      · have : b'⁻¹ * y ∉ V := by
          intro h'
          apply hy
          have := V.mul_mem hb' h'
          simpa [mul_assoc] using this
        rw [ite_eq_right this, mul_zero]
      · rw [ite_eq_right hb', zero_mul]
    simp_rw [h]
    rw [integral_zero, cosetIndicator_apply V b, ite_eq_right hy, mul_zero]

end Cosets

/-- **Slices and cosets.** A compactly supported continuous function `f` on `A × B` that is right
invariant under an open subgroup `V` of `B` is a finite sum
`f(x) = ∑_{b ∈ T} f(x₁, b) 1_{bV}(x₂)`, with `T` a finite set of representatives of distinct cosets
covering the projection of the support of `f`. -/
theorem exists_eq_sum_slice_mul_cosetIndicator {A B : Type*} [Group A] [TopologicalSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] (f : C_c(A × B, ℂ)) (V : Subgroup B)
    (hVo : IsOpen (V : Set B)) (hfV : ∀ x, ∀ v ∈ V, f (x * (1, v)) = f x) :
    ∃ T : Finset B, ∀ x : A × B,
      f x = ∑ b ∈ T, f (x.1, b) * (b • (V : Set B)).indicator 1 x.2 := by
  classical
  set S : Set B := Prod.snd '' tsupport f with hSdef
  have hS : IsCompact S := f.hasCompactSupport.image continuous_snd
  obtain ⟨t, -, hcov⟩ := hS.elim_nhds_subcover (fun b => b • (V : Set B))
    (fun b _ => (hVo.smul b).mem_nhds ((mem_leftCoset_iff b).2 (by simp)))
  let T' : Finset (B ⧸ V) := t.image (QuotientGroup.mk : B → B ⧸ V)
  let r : B ⧸ V → B := fun q => q.out
  have hr : ∀ (q : B ⧸ V) (y : B), (r q)⁻¹ * y ∈ V ↔ (y : B ⧸ V) = q := by
    intro q y
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', eq_comm]
  have hrinj : Set.InjOn r T' := fun q₁ _ q₂ _ h => by
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂]
    exact congrArg _ h
  refine ⟨T'.image r, fun x => ?_⟩
  rw [Finset.sum_image hrinj]
  have h1 : ∀ q, f (x.1, r q) * (r q • (V : Set B)).indicator 1 x.2 =
      if (x.2 : B ⧸ V) = q then f (x.1, r q) else 0 := by
    intro q
    have := cosetIndicator_apply V (r q) x.2
    rw [show (r q • (V : Set B)).indicator 1 x.2 = cosetIndicator V (r q) x.2 from rfl, this]
    by_cases hq : (x.2 : B ⧸ V) = q
    · rw [ite_eq_left ((hr q _).2 hq), ite_eq_left hq, mul_one]
    · rw [ite_eq_right (fun h' => hq ((hr q _).1 h')), ite_eq_right hq, mul_zero]
  simp_rw [h1]
  rw [Finset.sum_ite_eq]
  by_cases hT : (x.2 : B ⧸ V) ∈ T'
  · rw [ite_eq_left hT]
    set q : B ⧸ V := (x.2 : B ⧸ V)
    have hv : (r q)⁻¹ * x.2 ∈ V := (hr q _).2 rfl
    have hx : x = (x.1, r q) * (1, (r q)⁻¹ * x.2) := by
      rw [Prod.mk_mul_mk, mul_one, mul_inv_cancel_left]
    conv_lhs => rw [hx]
    exact hfV _ _ hv
  · rw [ite_eq_right hT]
    by_contra hfx
    have hxS : x.2 ∈ S := ⟨x, subset_tsupport _ hfx, rfl⟩
    obtain ⟨b, hbt, hb⟩ := mem_iUnion₂.1 (hcov hxS)
    apply hT
    exact Finset.mem_image.2 ⟨b, hbt, QuotientGroup.eq.2 ((mem_leftCoset_iff b).1 hb)⟩

section Product

variable {E A B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B]

/-- The tensor product `(a, b) ↦ u a * w b` of two continuous compactly supported functions, as a
compactly supported continuous function on `A × B`. -/
def tensorCc (u : A → ℂ) (w : B → ℂ) (hu : Continuous u) (hw : Continuous w)
    (huc : HasCompactSupport u) (hwc : HasCompactSupport w) : C_c(A × B, ℂ) where
  toFun p := u p.1 * w p.2
  continuous_toFun := (hu.comp continuous_fst).mul (hw.comp continuous_snd)
  hasCompactSupport' := by
    refine IsCompact.of_isClosed_subset (huc.isCompact.prod hwc.isCompact) (isClosed_tsupport _)
      (closure_minimal (fun p hp => ?_) ((isClosed_tsupport u).prod (isClosed_tsupport w)))
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul hp), subset_tsupport _ (right_ne_zero_of_mul hp)⟩

omit [Group A] [Group B] in
/-- The value of a tensor product. -/
theorem tensorCc_apply (u : A → ℂ) (w : B → ℂ) (hu : Continuous u) (hw : Continuous w)
    (huc : HasCompactSupport u) (hwc : HasCompactSupport w) (p : A × B) :
    tensorCc u w hu hw huc hwc p = u p.1 * w p.2 := rfl

variable [ChartedSpace E A]

omit [Group A] in
/-- `a ↦ f a * k` is smooth for smooth complex-valued `f`. -/
theorem contMDiff_mul_const {f : A → ℂ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f) (k : ℂ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (fun a => f a * k) := by
  have h := ((k • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp hf
  convert h using 1
  funext a
  simp [mul_comm]

omit [Group A] in
/-- `a ↦ k * f a` is smooth for smooth complex-valued `f`. -/
theorem contMDiff_const_mul {f : A → ℂ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f) (k : ℂ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (fun a => k * f a) := by
  simpa only [mul_comm] using contMDiff_mul_const hf k

/-- The conditions on a pair `(φ, ψ)` of factors in the product theorem: the slices `a ↦ φ (a, b)`,
`a ↦ ψ (a, b)` are smooth, `φ` and `ψ` are right invariant under `V`, `φ` is left invariant under
some open subgroup of `B`, and `ψ` is left invariant under `V`. -/
def IsFactorPair (V : Subgroup B) (φ ψ : C_c(A × B, ℂ)) : Prop :=
  (∀ b, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ fun a => φ (a, b)) ∧
    (∀ b, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ fun a => ψ (a, b)) ∧
    (∀ x, ∀ v ∈ V, φ (x * (1, v)) = φ x) ∧ (∀ x, ∀ v ∈ V, ψ (x * (1, v)) = ψ x) ∧
    (∃ V' : Subgroup B, IsOpen (V' : Set B) ∧ ∀ x, ∀ v ∈ V', φ ((1, v) * x) = φ x) ∧
    (∀ x, ∀ v ∈ V, ψ ((1, v) * x) = ψ x)

variable [MeasurableSpace A] [MeasurableSpace B]

/-- `F` is a finite sum `∑ φᵢ ⋆ ψᵢ` of convolutions (for `μ`) of factor pairs. -/
def IsSumConv (μ : Measure (A × B)) (V : Subgroup B) (F : A × B → ℂ) : Prop :=
  ∃ (n : ℕ) (φ ψ : Fin n → C_c(A × B, ℂ)), (∀ i, IsFactorPair (E := E) V (φ i) (ψ i)) ∧
    ∀ x, F x = ∑ i, Hecke.convolutionIntegral μ (φ i) (ψ i) x

variable (μ : Measure (A × B)) (V : Subgroup B)

/-- `0` is an empty sum of convolutions. -/
theorem isSumConv_zero : IsSumConv (E := E) μ V 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun x => by simp⟩

/-- Sums of convolutions are closed under addition (concatenation of the factor lists). -/
theorem IsSumConv.add {F₁ F₂ : A × B → ℂ} (h₁ : IsSumConv (E := E) μ V F₁)
    (h₂ : IsSumConv (E := E) μ V F₂) : IsSumConv (E := E) μ V (F₁ + F₂) := by
  obtain ⟨n₁, φ₁, ψ₁, hP₁, hF₁⟩ := h₁
  obtain ⟨n₂, φ₂, ψ₂, hP₂, hF₂⟩ := h₂
  refine ⟨n₁ + n₂, Fin.append φ₁ φ₂, Fin.append ψ₁ ψ₂, fun i => ?_, fun x => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.append_left] using hP₁ i
    · simpa only [Fin.append_right] using hP₂ i
  · rw [Fin.sum_univ_add, Pi.add_apply, hF₁ x, hF₂ x]
    simp only [Fin.append_left, Fin.append_right]

/-- Sums of convolutions are closed under finite sums. -/
theorem isSumConv_finsetSum {ι : Type*} (s : Finset ι) {F : ι → A × B → ℂ}
    (hF : ∀ i ∈ s, IsSumConv (E := E) μ V (F i)) : IsSumConv (E := E) μ V (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSumConv_zero (E := E) μ V
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add μ V
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

end Product

/-- **Dixmier–Malliavin on a product `A × B`.** Let `A` be a Lie group with a closed linear
realization and `B` a locally compact Hausdorff second countable group, and `μ` a left Haar measure
on `A × B`. A compactly supported continuous `f` on `A × B` whose slices `a ↦ f (a, b)` are smooth
and which is right invariant under a compact open subgroup `V` of `B` is a finite sum
`∑ φᵢ ⋆ ψᵢ` of convolutions of such functions, with `φᵢ` left invariant under an open subgroup of `B`
and `ψᵢ` left invariant under `V`. The factors are `φ = (μ(V) c)⁻¹ (φ₀ ⊗ 1_{bV})` and
`ψ = ψ₀ ⊗ 1_V`, where `f(·, b) = ∑ φ₀ ⋆ ψ₀` on `A` and `μ = c (μ_A × μ_B)`. -/
theorem exists_eq_sum_convolutionIntegral_prod
    {E A B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [ChartedSpace E A]
    [LieGroup 𝓘(ℝ, E) ∞ A] [T2Space A] [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B] [T2Space B]
    [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
    {ρ : A →* 𝔸ˣ} (hρ : LinearLieGroup.IsClosedLinearRealization 𝓘(ℝ, E) ρ)
    (μ : Measure (A × B)) [μ.IsHaarMeasure] (f : C_c(A × B, ℂ))
    (hf : ∀ b, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ fun a => f (a, b))
    (V : Subgroup B) (hVo : IsOpen (V : Set B)) (hVc : IsCompact (V : Set B))
    (hfV : ∀ x, ∀ v ∈ V, f (x * (1, v)) = f x) :
    ∃ (n : ℕ) (φ ψ : Fin n → C_c(A × B, ℂ)),
      (∀ i, (∀ b, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ fun a => φ i (a, b)) ∧
            (∀ b, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ fun a => ψ i (a, b)) ∧
            (∀ x, ∀ v ∈ V, φ i (x * (1, v)) = φ i x) ∧ (∀ x, ∀ v ∈ V, ψ i (x * (1, v)) = ψ i x) ∧
            (∃ V' : Subgroup B, IsOpen (V' : Set B) ∧ ∀ x, ∀ v ∈ V', φ i ((1, v) * x) = φ i x) ∧
            (∀ x, ∀ v ∈ V, ψ i ((1, v) * x) = ψ i x)) ∧
      ∀ x, f x = ∑ i, Hecke.convolutionIntegral μ (φ i) (ψ i) x := by
  classical
  have : SecondCountableTopology A := by
    have : SecondCountableTopology 𝔸ˣ :=
        Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
    exact hρ.isClosedEmbedding.isEmbedding.secondCountableTopology
  let μA : Measure A := Measure.haar
  let μB : Measure B := Measure.haar
  obtain ⟨c, hc0, hμ⟩ : ∃ c : NNReal, c ≠ 0 ∧ μ = c • μA.prod μB :=
    ⟨_, (haarScalarFactor_pos_of_isHaarMeasure _ _).ne', isMulLeftInvariant_eq_smul _ _⟩
  have hconv : ∀ (F G : A × B → ℂ) (x : A × B), Hecke.convolutionIntegral μ F G x =
      (c : ℂ) * Hecke.convolutionIntegral (μA.prod μB) F G x := by
    intro F G x
    rw [Hecke.convolutionIntegral, Hecke.convolutionIntegral, hμ, integral_smul_nnreal_measure,
      NNReal.smul_def, Complex.real_smul]
  set mB : ℝ := μB.real V with hmB_def
  have hmB : 0 < mB := by
    rw [hmB_def, measureReal_def]
    exact ENNReal.toReal_pos (hVo.measure_ne_zero μB ⟨1, V.one_mem⟩) hVc.measure_lt_top.ne
  obtain ⟨T, hT⟩ := exists_eq_sum_slice_mul_cosetIndicator f V hVo hfV
  have hslice : ∀ b, HasCompactSupport (fun a => f (a, b)) := by
    intro b
    refine HasCompactSupport.of_support_subset_isCompact
      (f.hasCompactSupport.image continuous_fst) ?_
    intro a ha
    exact ⟨(a, b), subset_tsupport _ ha, rfl⟩
  let fb : B → Archimedean.smoothCompactKernels E A := fun b => ⟨fun a => f (a, b), hf b, hslice b⟩
  choose n φ ψ hsupp hsum using fun b =>
    Archimedean.exists_eq_sum_gardingKernelConvolution hρ μA (univ_mem) (fb b)
  -- one tensor
  have single : ∀ (φ₀ ψ₀ : Archimedean.smoothCompactKernels E A) (b : B),
      IsSumConv (E := E) μ V
        (fun x => Hecke.convolutionIntegral μA φ₀.val ψ₀.val x.1 * cosetIndicator V b x.2) := by
    intro φ₀ ψ₀ b
    set k : ℂ := ((c : ℂ) * (mB : ℂ))⁻¹ with hk
    have hku : Continuous fun a => k * φ₀.val a := continuous_const.mul φ₀.property.1.continuous
    have hkuc : HasCompactSupport fun a => k * φ₀.val a := φ₀.property.2.mul_left
    let Φ := tensorCc (fun a => k * φ₀.val a) (cosetIndicator V b) hku
      (continuous_cosetIndicator V hVo b) hkuc (hasCompactSupport_cosetIndicator V hVc b)
    let Ψ := tensorCc ψ₀.val (cosetIndicator V 1) ψ₀.property.1.continuous
      (continuous_cosetIndicator V hVo 1) ψ₀.property.2 (hasCompactSupport_cosetIndicator V hVc 1)
    refine ⟨1, fun _ => Φ, fun _ => Ψ, fun _ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun x => ?_⟩
    · intro b'
      change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ fun a => k * φ₀.val a * cosetIndicator V b b'
      exact contMDiff_mul_const (contMDiff_const_mul φ₀.property.1 k) _
    · intro b'
      change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ fun a => ψ₀.val a * cosetIndicator V 1 b'
      exact contMDiff_mul_const ψ₀.property.1 _
    · intro x v hv
      change k * φ₀.val (x * (1, v)).1 * cosetIndicator V b (x * (1, v)).2 =
        k * φ₀.val x.1 * cosetIndicator V b x.2
      simp only [Prod.fst_mul, Prod.snd_mul, mul_one]
      rw [cosetIndicator_mul V b x.2 hv]
    · intro x v hv
      change ψ₀.val (x * (1, v)).1 * cosetIndicator V 1 (x * (1, v)).2 =
        ψ₀.val x.1 * cosetIndicator V 1 x.2
      simp only [Prod.fst_mul, Prod.snd_mul, mul_one]
      rw [cosetIndicator_mul V 1 x.2 hv]
    · refine ⟨V.comap (MulAut.conj b⁻¹).toMonoidHom, ?_, fun x v hv => ?_⟩
      · exact hVo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
      · change k * φ₀.val ((1, v) * x).1 * cosetIndicator V b ((1, v) * x).2 =
          k * φ₀.val x.1 * cosetIndicator V b x.2
        simp only [Prod.fst_mul, Prod.snd_mul, one_mul]
        have hv' : b⁻¹ * v * b ∈ V := by simpa using hv
        rw [cosetIndicator_mul_left V b x.2 hv']
    · intro x v hv
      change ψ₀.val ((1, v) * x).1 * cosetIndicator V 1 ((1, v) * x).2 =
        ψ₀.val x.1 * cosetIndicator V 1 x.2
      simp only [Prod.fst_mul, Prod.snd_mul, one_mul]
      rw [cosetIndicator_mul_left V 1 x.2 (by simpa using hv)]
    · rw [Fin.sum_univ_one, hconv]
      have ht := Hecke.convolutionIntegral_prod_tensor μA μB (fun a => k * φ₀.val a) ψ₀.val
        (cosetIndicator V b) (cosetIndicator V 1) x
      have hΦ : (⇑Φ : A × B → ℂ) =
          fun p => (fun a => k * φ₀.val a) p.1 * cosetIndicator V b p.2 := rfl
      have hΨ : (⇑Ψ : A × B → ℂ) = fun p => ψ₀.val p.1 * cosetIndicator V 1 p.2 := rfl
      rw [hΦ, hΨ, ht, convolutionIntegral_cosetIndicator V μB hVo, ← hmB_def]
      have hk' : Hecke.convolutionIntegral μA (fun a => k * φ₀.val a) ψ₀.val x.1 =
          k * Hecke.convolutionIntegral μA φ₀.val ψ₀.val x.1 := by
        simp only [Hecke.convolutionIntegral, mul_assoc]
        exact integral_const_mul _ _
      rw [hk', hk]
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
      have hm' : (mB : ℂ) ≠ 0 := by exact_mod_cast hmB.ne'
      field_simp
  have key : ∀ b, IsSumConv (E := E) μ V (fun x => f (x.1, b) * cosetIndicator V b x.2) := by
    intro b
    have e : (fun x : A × B => f (x.1, b) * cosetIndicator V b x.2) =
        ∑ i, fun x => Hecke.convolutionIntegral μA (φ b i).val (ψ b i).val x.1 *
          cosetIndicator V b x.2 := by
      funext x
      rw [Finset.sum_apply, ← Finset.sum_mul]
      congr 1
      have := congrArg (fun F : Archimedean.smoothCompactKernels E A => F.val x.1) (hsum b)
      simp only [Submodule.coe_sum, Finset.sum_apply, Archimedean.gardingKernelConvolution_apply]
        at this
      exact this
    rw [e]
    exact isSumConv_finsetSum μ V _ fun i _ => single (φ b i) (ψ b i) b
  obtain ⟨N, Φ, Ψ, hP, hF⟩ := isSumConv_finsetSum μ V T fun b _ => key b
  refine ⟨N, Φ, Ψ, hP, fun x => ?_⟩
  rw [hT x, ← hF x, Finset.sum_apply]
  rfl

end Langlands.Analysis.DixmierMalliavin
