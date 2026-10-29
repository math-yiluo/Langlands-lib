import Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorizationStatement
import Langlands.HarmonicAnalysis.Distribution.CharacterAverageCovarianceProof
import Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveProof

/-!
# Proof of unique factorization of twisted product distributions

Proves `CharacterAverageFactorizationStatement`. Fix a compact open subgroup `K₀` in the
kernel of `χ` and the section `S₀ f = c⁻¹1_{K₀} ⊗ f ⊗ c⁻¹1_{K₀}` with `c = μ K₀`, which
satisfies `characterAverage χ μ (S₀ f) = f`. The factor is `τ = D ∘ S₀`. Every test
function is invariant under a compact open `K ≤ K₀` acting on the right of the first
coordinate and on the left of the last one, and is then a finite sum of translates of
sections `S_K f`, one for each box `g K × K h` meeting the projected support. On such a
translate `D` and `D ∘ S_K ∘ characterAverage χ μ` agree by the hypothesis on `D` and the
published covariance of the average, so they agree everywhere, by finite linearity only.
See the paired Markdown.
-/

noncomputable section

open MeasureTheory Filter Topology Function

namespace Langlands.HarmonicAnalysis.Distribution

universe uG uY

namespace CharacterAverageFactorization

section Topological

variable {G : Type uG} {Y : Type uY} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace Y]

/-- Evaluation of a finite sum of test functions. -/
theorem sum_apply {X : Type*} [TopologicalSpace X] {ι : Type*} (s : Finset ι)
    (f : ι → SchwartzBruhat X) (x : X) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    rfl

variable (Y) in
/-- The homeomorphism `(g₁, (y, g₂)) ↦ (a * g₁, (y, g₂ * b))` of the hypothesis. -/
abbrev translation (a b : G) : G × (Y × G) ≃ₜ G × (Y × G) :=
  (Homeomorph.mulLeft a).prodCongr ((Homeomorph.refl Y).prodCongr (Homeomorph.mulRight b))

/-- `α` is invariant under right translation of the first coordinate and left translation
of the last coordinate by elements of `K`. -/
def IsSmooth (K : OpenSubgroup G) (α : SchwartzBruhat (G × (Y × G))) : Prop :=
  ∀ k ∈ K, ∀ k' ∈ K, ∀ (g₁ : G) (y : Y) (g₂ : G), α (g₁ * k, (y, k' * g₂)) = α (g₁, (y, g₂))

omit [IsTopologicalGroup G] in
/-- Every test function is smooth for a compact open subgroup inside a given identity
neighbourhood: a compact-tube argument over its compact support. -/
theorem exists_isSmooth [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
    (α : SchwartzBruhat (G × (Y × G))) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U ∧ IsSmooth K α := by
  have hC := Hecke.TestFunction.isCompact_support α
  have hev : ∀ᶠ w : G × G in 𝓝 ((1 : G), (1 : G)), ∀ q ∈ support (α : G × (Y × G) → ℂ),
      α (q.1 * w.1, (q.2.1, w.2 * q.2.2)) = α q := by
    refine hC.eventually_forall_of_forall_eventually fun q _ => ?_
    have h₁ : IsLocallyConstant fun z : (G × G) × (G × (Y × G)) =>
        α (z.2.1 * z.1.1, (z.2.2.1, z.1.2 * z.2.2.2)) :=
      α.locallyConstant.comp_continuous (by fun_prop)
    have h₂ : IsLocallyConstant fun z : (G × G) × (G × (Y × G)) => α z.2 :=
      α.locallyConstant.comp_continuous (by fun_prop)
    filter_upwards [h₁.eventually_eq ((1, 1), q), h₂.eventually_eq ((1, 1), q)] with z hz hz'
    exact hz.trans ((by simp : α (q.1 * 1, (q.2.1, 1 * q.2.2)) = α q).trans hz'.symm)
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hev
  obtain ⟨K, hK, hKU⟩ := Langlands.compactOpenSubgroupBasis G (U ∩ (u ∩ v))
    (inter_mem hU (inter_mem hu hv))
  refine ⟨K, hK, fun g hg => (hKU hg).1, ?_⟩
  have hgood : ∀ k ∈ K, ∀ k' ∈ K, ∀ q ∈ support (α : G × (Y × G) → ℂ),
      α (q.1 * k, (q.2.1, k' * q.2.2)) = α q :=
    fun k hk k' hk' q hq =>
      huv (show (k, k') ∈ u ×ˢ v from ⟨(hKU hk).2.1, (hKU hk').2.2⟩) q hq
  intro k hk k' hk' g₁ y g₂
  by_cases h : α (g₁, (y, g₂)) = 0
  · rw [h]
    by_contra hne
    have := hgood k⁻¹ (inv_mem hk) k'⁻¹ (inv_mem hk') (g₁ * k, (y, k' * g₂)) hne
    simp only [mul_inv_cancel_right, inv_mul_cancel_left] at this
    exact hne (this.symm.trans h)
  · exact hgood k hk k' hk' (g₁, (y, g₂)) h

/-- The middle slice `y ↦ α (x.1, (y, x.2))`. -/
def middle (α : SchwartzBruhat (G × (Y × G))) (x : G × G) : SchwartzBruhat Y :=
  ⟨fun y => α (x.1, (y, x.2)),
    α.locallyConstant.comp_continuous (by fun_prop),
    HasCompactSupport.intro'
      (((Hecke.TestFunction.isCompact_support α).image
          (by fun_prop : Continuous fun q : G × (Y × G) => q.2.1)).of_isClosed_subset
        ((Hecke.TestFunction.isClopen_support α).isClosed.preimage
          (by fun_prop : Continuous fun y : Y => (x.1, (y, x.2))))
        (fun y hy => ⟨(x.1, (y, x.2)), hy, rfl⟩))
      ((Hecke.TestFunction.isClopen_support α).isClosed.preimage
          (by fun_prop : Continuous fun y : Y => (x.1, (y, x.2))))
      (fun _ hy => Function.notMem_support.mp hy)⟩

omit [Group G] [IsTopologicalGroup G] in
@[simp]
theorem middle_apply (α : SchwartzBruhat (G × (Y × G))) (x : G × G) (y : Y) :
    middle α x y = α (x.1, (y, x.2)) := rfl

/-- The open box `x.1 K × K x.2`. -/
def box (K : OpenSubgroup G) (x : G × G) : Set (G × G) :=
  {p | x.1⁻¹ * p.1 ∈ K ∧ p.2 * x.2⁻¹ ∈ K}

theorem box_mem_nhds (K : OpenSubgroup G) (x : G × G) : box K x ∈ 𝓝 x := by
  refine IsOpen.mem_nhds ?_ ?_
  · exact (K.isOpen.preimage (continuous_const.mul continuous_fst)).inter
      (K.isOpen.preimage (continuous_snd.mul continuous_const))
  · exact ⟨by simp [one_mem], by simp [one_mem]⟩

omit [IsTopologicalGroup G] in
/-- Two boxes sharing a point coincide. -/
theorem box_eq_of_mem {K : OpenSubgroup G} {x x' p : G × G} (h : p ∈ box K x)
    (h' : p ∈ box K x') : box K x = box K x' := by
  have key : ∀ {x x' : G × G}, p ∈ box K x → p ∈ box K x' → box K x ⊆ box K x' := by
    intro x x' h h' z hz
    refine ⟨?_, ?_⟩
    · have e : x'.1⁻¹ * z.1 = (x'.1⁻¹ * p.1) * (x.1⁻¹ * p.1)⁻¹ * (x.1⁻¹ * z.1) := by group
      rw [e]
      exact mul_mem (mul_mem h'.1 (inv_mem h.1)) hz.1
    · have e : z.2 * x'.2⁻¹ = (z.2 * x.2⁻¹) * (p.2 * x.2⁻¹)⁻¹ * (p.2 * x'.2⁻¹) := by group
      rw [e]
      exact mul_mem (mul_mem hz.2 (inv_mem h.2)) h'.2
  exact (key h h').antisymm (key h' h)

end Topological

section Measure

variable {G : Type uG} {Y : Type uY} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [TopologicalSpace Y]

/-- The normalized section `f ↦ c⁻¹1_K ⊗ f ⊗ c⁻¹1_K`, `c = μ K`, as a linear map. -/
def normalizedSection (μ : Measure G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    SchwartzBruhat Y →ₗ[ℂ] SchwartzBruhat (G × (Y × G)) where
  toFun f := SchwartzBruhat.tripleTensor (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) f
    (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)
  map_add' f g := Hecke.TestFunction.ext fun q => by
    change _ * (f q.2.1 + g q.2.1) * _ = _ * f q.2.1 * _ + _ * g q.2.1 * _
    ring
  map_smul' c f := Hecke.TestFunction.ext fun q => by
    change _ * (c * f q.2.1) * _ = c * (_ * f q.2.1 * _)
    ring

omit [BorelSpace G] in
theorem normalizedSection_apply (μ : Measure G) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (f : SchwartzBruhat Y) (g₁ : G) (y : Y) (g₂ : G) :
    normalizedSection μ K hK f (g₁, (y, g₂)) =
      (K : Set G).indicator (fun _ => ((μ.real (K : Set G) : ℂ)⁻¹)) g₁ * f y *
        (K : Set G).indicator (fun _ => ((μ.real (K : Set G) : ℂ)⁻¹)) g₂ := by
  rw [← SchwartzBruhat.normalizedCharacteristic_apply μ K hK g₁,
    ← SchwartzBruhat.normalizedCharacteristic_apply μ K hK g₂]
  rfl

/-- The section is right inverse to the average when `χ` is trivial on `K`. -/
theorem characterAverage_normalizedSection (χ : ContinuousMonoidHom G ℂˣ) (μ : Measure G)
    [μ.IsHaarMeasure] [SFinite μ] (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hχ : ∀ g ∈ K, χ g = 1) (f : SchwartzBruhat Y) :
    SchwartzBruhat.characterAverage χ μ (normalizedSection μ K hK f) = f :=
  SchwartzBruhat.characterAverage_tripleTensor_normalizedCharacteristic χ μ K hK hχ f

omit [BorelSpace G] in
/-- A section for `K` is smooth for every smaller open subgroup. -/
theorem isSmooth_normalizedSection (μ : Measure G) {K L : OpenSubgroup G}
    (hK : IsCompact (K : Set G)) (hLK : L ≤ K) (f : SchwartzBruhat Y) :
    IsSmooth L (normalizedSection μ K hK f) := by
  intro k hk k' hk' g₁ y g₂
  rw [normalizedSection_apply, normalizedSection_apply]
  have h₁ : g₁ * k ∈ (K : Set G) ↔ g₁ ∈ (K : Set G) := mul_mem_cancel_right (hLK hk)
  have h₂ : k' * g₂ ∈ (K : Set G) ↔ g₂ ∈ (K : Set G) := mul_mem_cancel_left (hLK hk')
  classical
  simp only [Set.indicator_apply, h₁, h₂]

omit [BorelSpace G] in
/-- A translate of a section, scaled by `c ^ 2`, is the restriction of a smooth `α` to a box. -/
theorem term_apply (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (α : SchwartzBruhat (G × (Y × G))) (hα : IsSmooth K α)
    (x : G × G) (g₁ : G) (y : Y) (g₂ : G) :
    (((μ.real (K : Set G) : ℂ) ^ 2) • Hecke.TestFunction.pullback (translation Y x.1⁻¹ x.2⁻¹)
        (normalizedSection μ K hK (middle α x))) (g₁, (y, g₂)) =
      (box K x).indicator (fun _ => α (g₁, (y, g₂))) (g₁, g₂) := by
  have hc := Hecke.HeckeAlgebra.compactOpen_complex_mass_ne_zero μ K hK
  change ((μ.real (K : Set G) : ℂ) ^ 2) *
      normalizedSection μ K hK (middle α x) (x.1⁻¹ * g₁, (y, g₂ * x.2⁻¹)) = _
  rw [normalizedSection_apply, middle_apply]
  by_cases h₁ : x.1⁻¹ * g₁ ∈ K
  · by_cases h₂ : g₂ * x.2⁻¹ ∈ K
    · rw [Set.indicator_of_mem (s := box K x) ⟨h₁, h₂⟩,
        Set.indicator_of_mem (s := (K : Set G)) h₁, Set.indicator_of_mem (s := (K : Set G)) h₂]
      have e := hα _ h₁ _ h₂ x.1 y x.2
      rw [mul_inv_cancel_left, inv_mul_cancel_right] at e
      rw [e]
      field_simp
    · rw [Set.indicator_of_notMem (s := box K x) (fun h => h₂ h.2),
        Set.indicator_of_notMem (s := (K : Set G)) h₂, mul_zero, mul_zero]
  · rw [Set.indicator_of_notMem (s := box K x) (fun h => h₁ h.1),
      Set.indicator_of_notMem (s := (K : Set G)) h₁, zero_mul, zero_mul, mul_zero]

omit [BorelSpace G] in
/-- A smooth test function is a finite sum of scaled translates of sections, one for each
box meeting the projection of its support. -/
theorem exists_eq_sum (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (α : SchwartzBruhat (G × (Y × G))) (hα : IsSmooth K α) :
    ∃ u : Finset (G × G), α = ∑ x ∈ u, ((μ.real (K : Set G) : ℂ) ^ 2) •
      Hecke.TestFunction.pullback (translation Y x.1⁻¹ x.2⁻¹)
        (normalizedSection μ K hK (middle α x)) := by
  classical
  have hP : IsCompact ((fun q : G × (Y × G) => (q.1, q.2.2)) '' support (α : G × (Y × G) → ℂ)) :=
    (Hecke.TestFunction.isCompact_support α).image (by fun_prop)
  obtain ⟨t, -, ht⟩ := hP.elim_nhds_subcover (box K) (fun x _ => box_mem_nhds K x)
  obtain ⟨u, -, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn (f := box K) (↑t)
    (t.image (box K)) (by rw [Finset.coe_image]; exact Set.surjOn_image _ _)
  refine ⟨u, Hecke.TestFunction.ext fun q => ?_⟩
  obtain ⟨g₁, y, g₂⟩ := q
  rw [sum_apply]
  simp only [term_apply μ K hK α hα]
  by_cases hq : α (g₁, (y, g₂)) = 0
  · simp [hq]
  · have hp : (g₁, g₂) ∈ ⋃ x ∈ t, box K x := ht ⟨(g₁, (y, g₂)), hq, rfl⟩
    obtain ⟨x, hxt, hx⟩ := Set.mem_iUnion₂.mp hp
    have hmem : box K x ∈ u.image (box K) := himg ▸ Finset.mem_image_of_mem _ hxt
    obtain ⟨x', hx'u, hx'⟩ := Finset.mem_image.mp hmem
    have hp' : (g₁, g₂) ∈ box K x' := hx' ▸ hx
    rw [Finset.sum_eq_single_of_mem x' hx'u fun b hb hne =>
      Set.indicator_of_notMem (fun hb' => hne (hinj hb hx'u (box_eq_of_mem hb' hp'))) _,
      Set.indicator_of_mem hp']

/-- On a test function smooth for `K`, with `χ` trivial on `K`, the distribution `D` agrees
with `D ∘ S_K ∘ characterAverage χ μ`. -/
theorem eq_normalizedSection_of_isSmooth (χ : ContinuousMonoidHom G ℂˣ) (μ : Measure G)
    [μ.IsHaarMeasure] [SFinite μ] [μ.IsMulRightInvariant] (D : Distribution (G × (Y × G)))
    (hD : ∀ (a b : G) (α : SchwartzBruhat (G × (Y × G))),
      D (Hecke.TestFunction.pullback (translation Y a b) α) = ((χ a : ℂ) * (χ b : ℂ)) * D α)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (hχ : ∀ g ∈ K, χ g = 1)
    (α : SchwartzBruhat (G × (Y × G))) (hα : IsSmooth K α) :
    D α = D (normalizedSection μ K hK (SchwartzBruhat.characterAverage χ μ α)) := by
  have key : ∀ (a b : G) (f : SchwartzBruhat Y),
      D (Hecke.TestFunction.pullback (translation Y a b) (normalizedSection μ K hK f)) =
        D (normalizedSection μ K hK (SchwartzBruhat.characterAverage χ μ
          (Hecke.TestFunction.pullback (translation Y a b) (normalizedSection μ K hK f)))) := by
    intro a b f
    rw [SchwartzBruhat.characterAverageCovariance G Y χ μ a b,
      characterAverage_normalizedSection χ μ K hK hχ, LinearMap.map_smul, LinearMap.map_smul,
      hD, smul_eq_mul]
  obtain ⟨u, hu⟩ := exists_eq_sum μ K hK α hα
  rw [← sub_eq_zero]
  let Δ : SchwartzBruhat (G × (Y × G)) →ₗ[ℂ] ℂ :=
    D - D ∘ₗ normalizedSection μ K hK ∘ₗ SchwartzBruhat.characterAverage χ μ
  change Δ α = 0
  rw [hu, map_sum]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [map_smul]
  change _ • (D _ - D _) = 0
  rw [key, LinearMap.comp_apply, sub_self, smul_zero]

end Measure

end CharacterAverageFactorization

open CharacterAverageFactorization in
/-- **Unique factorization of twisted product distributions.** The factor is
`D ∘ normalizedSection μ K₀ hK₀` for a compact open subgroup `K₀` in the kernel of `χ`. -/
theorem characterAverageFactorization : CharacterAverageFactorizationStatement.{uG, uY} := by
  intro G Y _ _ _ _ _ _ _ _ _ _ _ _ χ μ _ _ _ D hD
  have hker : IsOpen ((χ : G →* ℂˣ).ker : Set G) :=
    Langlands.isOpen_ker_of_continuous_complex_character (χ : G →* ℂˣ) χ.continuous
  obtain ⟨K₀, hK₀, hK₀ker⟩ :=
    Langlands.compactOpenSubgroupBasis G _ (hker.mem_nhds (χ : G →* ℂˣ).ker.one_mem)
  have hχ₀ : ∀ g ∈ K₀, χ g = 1 := fun g hg => (χ : G →* ℂˣ).mem_ker.mp (hK₀ker hg)
  -- The value of `D` on sections does not depend on the subgroup.
  have hindep : ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)), K ≤ K₀ →
      ∀ f : SchwartzBruhat Y,
        D (normalizedSection μ K hK f) = D (normalizedSection μ K₀ hK₀ f) := by
    intro K hK hKK₀ f
    rw [eq_normalizedSection_of_isSmooth χ μ D hD K hK (fun g hg => hχ₀ g (hKK₀ hg)) _
      (isSmooth_normalizedSection μ hK₀ hKK₀ f), characterAverage_normalizedSection χ μ K₀ hK₀ hχ₀]
  refine ⟨D ∘ₗ normalizedSection μ K₀ hK₀, ?_, ?_⟩
  · refine LinearMap.ext fun α => ?_
    obtain ⟨K, hK, hKK₀, hα⟩ := exists_isSmooth α (K₀.isOpen.mem_nhds K₀.one_mem)
    rw [characterAverageDual_apply, LinearMap.comp_apply,
      ← hindep K hK (SetLike.coe_subset_coe.mp hKK₀)]
    exact (eq_normalizedSection_of_isSmooth χ μ D hD K hK
      (fun g hg => hχ₀ g (hKK₀ hg)) α hα).symm
  · intro τ hτ
    refine LinearMap.ext fun f => ?_
    rw [LinearMap.comp_apply, ← hτ, characterAverageDual_apply,
      characterAverage_normalizedSection χ μ K₀ hK₀ hχ₀]

end Langlands.HarmonicAnalysis.Distribution
