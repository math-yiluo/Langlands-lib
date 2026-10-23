import Langlands.Representation.Hecke.DoubleCoset

/-!
# Double-coset spanning and sandwich structure of compact-open Hecke corners

For a compact open subgroup `K` of a Hausdorff topological group with a left Haar
measure, the corner `H_K` is spanned by the double-coset elements, and the double-coset
indicators of total mass one multiply as `e_{K g₁ K} * e_{K g₂ K} = e_{K g₁ g₂ K}`
whenever `K g₁ K g₂ K ⊆ K g₁ g₂ K`. Elements normalizing `K` act by exact translations.
Together with a Cartan-type decomposition `G = Γ M Γ` this gives the sandwich structure
of Bernstein--Zelevinsky (1976), Lemma 4.9, page 39.
-/

noncomputable section

namespace Langlands.Hecke

open MeasureTheory MeasureTheory.Measure
open HarmonicAnalysis (SchwartzBruhat)
open scoped Pointwise

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

namespace HeckeAlgebra

variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsMulLeftInvariant μ]

/-- The total integral of a convolution is the product of the total integrals; this
uses only left invariance and compact-support Fubini. -/
theorem integral_mul (f g : HeckeAlgebra μ) :
    ∫ x, (f * g) x ∂μ = (∫ x, f x ∂μ) * ∫ x, g x ∂μ := by
  let f' : SchwartzBruhat G := f
  let g' : SchwartzBruhat G := g
  simp only [mul_apply]
  rw [integral_integral_swap_of_hasCompactSupport (f := fun x y => f y * g (y⁻¹ * x))]
  · calc
      (∫ y, ∫ x, f y * g (y⁻¹ * x) ∂μ ∂μ) = ∫ y, f y * ∫ x, g x ∂μ ∂μ := by
        congr 1
        funext y
        rw [integral_const_mul, integral_mul_left_eq_self (fun x => g x) y⁻¹]
      _ = _ := integral_mul_const _ _
  · exact (f'.continuous.comp continuous_snd).mul
      (g'.continuous.comp (continuous_snd.inv.mul continuous_fst))
  · apply HasCompactSupport.of_support_subset_isCompact
      (((TestFunction.isCompact_support f').mul (TestFunction.isCompact_support g')).prod
        (TestFunction.isCompact_support f'))
    rintro ⟨z, y⟩ hp
    change f y * g (y⁻¹ * z) ≠ 0 at hp
    have hfg := mul_ne_zero_iff.mp hp
    exact ⟨⟨y, hfg.1, y⁻¹ * z, hfg.2, by simp⟩, hfg.1⟩

end HeckeAlgebra

variable [T2Space G] (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

namespace TestFunction

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [T2Space G] in
theorem mem_doubleCosetSet_self (g : G) : g ∈ doubleCosetSet K g :=
  (mem_doubleCosetSet K g g).2 ⟨1, K.one_mem, 1, K.one_mem, by simp⟩

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [T2Space G] in
/-- For an element normalizing `K`, the double coset `K γ g γ' K` is the
two-sided translate of `K g K`. -/
theorem mem_doubleCosetSet_mul_mul_iff {γ γ' : G} (hγ : γ ∈ Subgroup.normalizer (K.toSubgroup : Set G))
    (hγ' : γ' ∈ Subgroup.normalizer (K.toSubgroup : Set G)) (g x : G) :
    x ∈ doubleCosetSet K (γ * g * γ') ↔ γ⁻¹ * x * γ'⁻¹ ∈ doubleCosetSet K g := by
  have hγi : γ⁻¹ ∈ Subgroup.normalizer (K.toSubgroup : Set G) := inv_mem hγ
  have hγi' : γ'⁻¹ ∈ Subgroup.normalizer (K.toSubgroup : Set G) := inv_mem hγ'
  simp only [mem_doubleCosetSet]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨γ⁻¹ * a * γ⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp hγi a).1 ha,
      γ' * b * γ'⁻¹, (Subgroup.mem_normalizer_iff.mp hγ' b).1 hb, ?_⟩
    group
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨γ * a * γ⁻¹, (Subgroup.mem_normalizer_iff.mp hγ a).1 ha,
      γ'⁻¹ * b * γ'⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp hγi' b).1 hb, ?_⟩
    calc
      x = γ * (γ⁻¹ * x * γ'⁻¹) * γ' := by group
      _ = _ := by rw [h]; group

variable (μ : Measure G) [μ.IsHaarMeasure]

include hK in
omit [T2Space G] [BorelSpace G] in
theorem doubleCosetSet_mass_pos (g : G) : 0 < μ.real (doubleCosetSet K g) :=
  ENNReal.toReal_pos (ne_of_gt ((isOpen_doubleCosetSet K g).measure_pos μ
    ⟨g, mem_doubleCosetSet_self K g⟩)) (isCompact_doubleCosetSet K hK g).measure_ne_top

end TestFunction

variable (μ : Measure G) [μ.IsHaarMeasure]

namespace HeckeAlgebra.Corner

open TestFunction

omit [T2Space G] in
@[simp] theorem sub_apply (f g : Corner μ K hK) (x : G) : (f - g) x = f x - g x := rfl

omit [T2Space G] in
@[simp] theorem smul_apply (c : ℂ) (f : Corner μ K hK) (x : G) : (c • f) x = c * f x := rfl

omit [T2Space G] in
@[simp] theorem zero_apply (x : G) : (0 : Corner μ K hK) x = 0 := rfl

omit [T2Space G] in
@[simp] theorem one_apply (x : G) :
    (1 : Corner μ K hK) x =
      (μ.real (K : Set G) : ℂ)⁻¹ * (K : Set G).indicator (fun _ => (1 : ℂ)) x := rfl

omit [T2Space G] in
theorem ext' {f g : Corner μ K hK} (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext (HeckeAlgebra.ext μ h)

omit [T2Space G] in
/-- A corner element is constant on every `K`-double coset. -/
theorem apply_eq_of_mem_doubleCosetSet (f : Corner μ K hK) {g x : G}
    (hx : x ∈ doubleCosetSet K g) : f x = f g := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_doubleCosetSet K g x).1 hx
  rw [rightInvariant μ K hK f ⟨b, hb⟩, leftInvariant μ K hK f ⟨a, ha⟩]

/-- The corner is spanned by its double-coset elements. -/
theorem span_range_doubleCoset :
    Submodule.span ℂ (Set.range (doubleCoset K hK μ)) = ⊤ := by
  classical
  have hmass := HeckeAlgebra.compactOpen_complex_mass_ne_zero μ K hK
  have key : ∀ (t : Finset G) (f : Corner μ K hK),
      Function.support (fun x => f x) ⊆ ⋃ g ∈ t, doubleCosetSet K g →
        f ∈ Submodule.span ℂ (Set.range (doubleCoset K hK μ)) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro f hf
      have hf0 : f = 0 := ext' K hK μ fun x => by
        rw [zero_apply]
        by_contra hx
        have := hf (show x ∈ Function.support (fun x => f x) from hx)
        simp at this
      rw [hf0]
      exact Submodule.zero_mem _
    | insert g t _ ih =>
      intro f hf
      have hrest := ih (f - ((μ.real (K : Set G) : ℂ) * f g) • doubleCoset K hK μ g) (by
        intro x hx
        have hx' : f x - ((μ.real (K : Set G) : ℂ) * f g) * doubleCoset K hK μ g x ≠ 0 := hx
        by_cases hxg : x ∈ doubleCosetSet K g
        · exfalso
          apply hx'
          rw [apply_eq_of_mem_doubleCosetSet K hK μ f hxg, doubleCoset_apply,
            Set.indicator_of_mem hxg]
          field_simp
          ring
        · rw [doubleCoset_apply, Set.indicator_of_notMem hxg, mul_zero, mul_zero,
            sub_zero] at hx'
          have := hf hx'
          simp only [Finset.mem_insert, Set.mem_iUnion, exists_prop] at this
          obtain ⟨h, hh, hxh⟩ := this
          rcases hh with rfl | hh
          · exact absurd hxh hxg
          · exact Set.mem_iUnion₂.2 ⟨h, hh, hxh⟩)
      rw [← sub_add_cancel f (((μ.real (K : Set G) : ℂ) * f g) • doubleCoset K hK μ g)]
      exact Submodule.add_mem _ hrest
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩))
  rw [eq_top_iff]
  intro f _
  let f' : SchwartzBruhat G := toHeckeAlgebra μ K hK f
  obtain ⟨t, ht⟩ := (TestFunction.isCompact_support f').elim_finite_subcover
    (fun g : G => doubleCosetSet K g) (fun g => isOpen_doubleCosetSet K g)
    (fun x _ => Set.mem_iUnion.2 ⟨x, mem_doubleCosetSet_self K x⟩)
  exact key t f ht

/-- The double-coset element of an element normalizing `K` is the left translate of
the unit. -/
theorem doubleCoset_apply_of_mem_normalizer {γ : G}
    (hγ : γ ∈ Subgroup.normalizer (K.toSubgroup : Set G)) (x : G) :
    doubleCoset K hK μ γ x = (1 : Corner μ K hK) (γ⁻¹ * x) := by
  classical
  have h1 := mem_doubleCosetSet_mul_mul_iff K hγ (one_mem _) (1 : G) x
  simp only [mul_one, inv_one, doubleCosetSet_one] at h1
  rw [doubleCoset_apply, one_apply]
  by_cases hx : γ⁻¹ * x ∈ (K : Set G)
  · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

/-- The double-coset element of an element normalizing `K` is the right translate of
the unit by its inverse. -/
theorem doubleCoset_apply_of_mem_normalizer' {γ : G}
    (hγ : γ ∈ Subgroup.normalizer (K.toSubgroup : Set G)) (x : G) :
    doubleCoset K hK μ γ x = (1 : Corner μ K hK) (x * γ⁻¹) := by
  classical
  have h1 := mem_doubleCosetSet_mul_mul_iff K (one_mem _) hγ (1 : G) x
  simp only [one_mul, inv_one, doubleCosetSet_one] at h1
  rw [doubleCoset_apply, one_apply]
  by_cases hx : x * γ⁻¹ ∈ (K : Set G)
  · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

/-- Left multiplication by the double-coset element of a normalizing element is left
translation. -/
theorem doubleCoset_mul_apply_of_mem_normalizer {γ : G}
    (hγ : γ ∈ Subgroup.normalizer (K.toSubgroup : Set G)) (f : Corner μ K hK) (x : G) :
    (doubleCoset K hK μ γ * f) x = f (γ⁻¹ * x) := by
  have h := Corner.mul_apply μ K hK (1 : Corner μ K hK) f (γ⁻¹ * x)
  rw [one_mul] at h
  rw [h, Corner.mul_apply,
    ← integral_mul_left_eq_self (fun y => doubleCoset K hK μ γ y * f (y⁻¹ * x)) γ]
  congr 1
  funext y
  simp only [doubleCoset_apply_of_mem_normalizer K hK μ hγ, inv_mul_cancel_left, mul_inv_rev,
    mul_assoc]

/-- Right multiplication by the double-coset element of a normalizing element is right
translation by its inverse. -/
theorem mul_doubleCoset_apply_of_mem_normalizer {γ : G}
    (hγ : γ ∈ Subgroup.normalizer (K.toSubgroup : Set G)) (f : Corner μ K hK) (x : G) :
    (f * doubleCoset K hK μ γ) x = f (x * γ⁻¹) := by
  have h := Corner.mul_apply μ K hK f (1 : Corner μ K hK) (x * γ⁻¹)
  rw [mul_one] at h
  rw [h, Corner.mul_apply]
  congr 1
  funext y
  rw [doubleCoset_apply_of_mem_normalizer' K hK μ hγ, mul_assoc]

/-- Two-sided multiplication by double-coset elements of normalizing elements. -/
theorem doubleCoset_mul_mul_of_mem_normalizer {γ γ' : G}
    (hγ : γ ∈ Subgroup.normalizer (K.toSubgroup : Set G)) (hγ' : γ' ∈ Subgroup.normalizer (K.toSubgroup : Set G)) (g : G) :
    doubleCoset K hK μ γ * doubleCoset K hK μ g * doubleCoset K hK μ γ' =
      doubleCoset K hK μ (γ * g * γ') := by
  classical
  apply ext' K hK μ
  intro x
  rw [mul_doubleCoset_apply_of_mem_normalizer K hK μ hγ',
    doubleCoset_mul_apply_of_mem_normalizer K hK μ hγ, doubleCoset_apply, doubleCoset_apply,
    ← mul_assoc]
  have h := mem_doubleCosetSet_mul_mul_iff K hγ hγ' g x
  by_cases hx : γ⁻¹ * x * γ'⁻¹ ∈ doubleCosetSet K g
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (h.2 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (h.1 h'))]

/-- The double-coset indicator normalized to total mass one. -/
def massIndicator (g : G) : Corner μ K hK :=
  ((μ.real (doubleCosetSet K g) : ℂ)⁻¹ * (μ.real (K : Set G) : ℂ)) • doubleCoset K hK μ g

include hK in
omit [T2Space G] [BorelSpace G] in
theorem doubleCosetSet_complex_mass_ne_zero (g : G) :
    (μ.real (doubleCosetSet K g) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (doubleCosetSet_mass_pos K hK μ g))

theorem massIndicator_apply (g x : G) :
    massIndicator K hK μ g x =
      (μ.real (doubleCosetSet K g) : ℂ)⁻¹ * (doubleCosetSet K g).indicator (fun _ => 1) x := by
  rw [massIndicator, smul_apply, doubleCoset_apply]
  have := HeckeAlgebra.compactOpen_complex_mass_ne_zero μ K hK
  field_simp

/-- The double-coset element is a nonzero multiple of the mass-one indicator. -/
theorem doubleCoset_eq_smul_massIndicator (g : G) :
    doubleCoset K hK μ g =
      ((μ.real (doubleCosetSet K g) : ℂ) * (μ.real (K : Set G) : ℂ)⁻¹) •
        massIndicator K hK μ g := by
  have h1 := HeckeAlgebra.compactOpen_complex_mass_ne_zero μ K hK
  have h2 := doubleCosetSet_complex_mass_ne_zero K hK μ g
  rw [massIndicator, smul_smul]
  have : (μ.real (doubleCosetSet K g) : ℂ) * (μ.real (K : Set G) : ℂ)⁻¹ *
      ((μ.real (doubleCosetSet K g) : ℂ)⁻¹ * (μ.real (K : Set G) : ℂ)) = 1 := by
    field_simp
  rw [this, one_smul]

theorem massIndicator_one : massIndicator K hK μ (1 : G) = 1 := by
  apply ext' K hK μ
  intro x
  rw [massIndicator_apply, doubleCosetSet_one, one_apply]

theorem integral_massIndicator (g : G) :
    ∫ x, massIndicator K hK μ g x ∂μ = 1 := by
  simp only [massIndicator_apply]
  rw [integral_const_mul, integral_indicator_const _
    (isOpen_doubleCosetSet K g).measurableSet, Complex.real_smul, mul_one]
  exact inv_mul_cancel₀ (doubleCosetSet_complex_mass_ne_zero K hK μ g)

/-- `e_{K g₁ K} * e_{K g₂ K} = e_{K g₁ g₂ K}` for mass-one indicators, whenever
`g₁ K g₂ ⊆ K g₁ g₂ K`. -/
theorem massIndicator_mul {g₁ g₂ : G}
    (h : ∀ k ∈ K, g₁ * k * g₂ ∈ doubleCosetSet K (g₁ * g₂)) :
    massIndicator K hK μ g₁ * massIndicator K hK μ g₂ = massIndicator K hK μ (g₁ * g₂) := by
  classical
  have hD := doubleCosetSet_complex_mass_ne_zero K hK μ (g₁ * g₂)
  -- the product vanishes off `K g₁ g₂ K`
  have hzero : ∀ x, x ∉ doubleCosetSet K (g₁ * g₂) →
      (massIndicator K hK μ g₁ * massIndicator K hK μ g₂) x = 0 := by
    intro x hx
    have hpt : ∀ y, massIndicator K hK μ g₁ y * massIndicator K hK μ g₂ (y⁻¹ * x) = 0 := by
      intro y
      rw [massIndicator_apply, massIndicator_apply]
      by_cases hy : y ∈ doubleCosetSet K g₁
      · by_cases hy' : y⁻¹ * x ∈ doubleCosetSet K g₂
        · exfalso
          apply hx
          obtain ⟨a, ha, b, hb, hab⟩ := (mem_doubleCosetSet K g₁ y).1 hy
          obtain ⟨c, hc, d, hd, hcd⟩ := (mem_doubleCosetSet K g₂ _).1 hy'
          have hx' : x = a * (g₁ * (b * c) * g₂) * d := by
            calc
              x = y * (y⁻¹ * x) := by group
              _ = _ := by rw [hcd, hab]; group
          obtain ⟨a', ha', d', hd', h'⟩ :=
            (mem_doubleCosetSet K _ _).1 (h (b * c) (K.mul_mem hb hc))
          rw [hx', h']
          exact (mem_doubleCosetSet K _ _).2
            ⟨a * a', K.mul_mem ha ha', d' * d, K.mul_mem hd' hd, by group⟩
        · rw [Set.indicator_of_notMem hy']
          simp
      · rw [Set.indicator_of_notMem hy]
        simp
    rw [Corner.mul_apply]
    simp only [hpt, integral_zero]
  -- hence it is a multiple of the mass-one indicator of `K g₁ g₂ K`
  have hF : massIndicator K hK μ g₁ * massIndicator K hK μ g₂ =
      ((massIndicator K hK μ g₁ * massIndicator K hK μ g₂) (g₁ * g₂) *
        (μ.real (doubleCosetSet K (g₁ * g₂)) : ℂ)) • massIndicator K hK μ (g₁ * g₂) := by
    apply ext' K hK μ
    intro x
    rw [smul_apply, massIndicator_apply]
    by_cases hx : x ∈ doubleCosetSet K (g₁ * g₂)
    · rw [Set.indicator_of_mem hx, apply_eq_of_mem_doubleCosetSet K hK μ _ hx]
      field_simp
    · rw [Set.indicator_of_notMem hx, hzero x hx]
      simp
  -- comparing total integrals gives the coefficient `1`
  have hint : ∫ x, (massIndicator K hK μ g₁ * massIndicator K hK μ g₂) x ∂μ = 1 := by
    have := HeckeAlgebra.integral_mul μ (toHeckeAlgebra μ K hK (massIndicator K hK μ g₁))
      (toHeckeAlgebra μ K hK (massIndicator K hK μ g₂))
    change ∫ x, (massIndicator K hK μ g₁ * massIndicator K hK μ g₂) x ∂μ =
      (∫ x, massIndicator K hK μ g₁ x ∂μ) * ∫ x, massIndicator K hK μ g₂ x ∂μ at this
    rw [this, integral_massIndicator, integral_massIndicator, one_mul]
  have hc : (massIndicator K hK μ g₁ * massIndicator K hK μ g₂) (g₁ * g₂) *
      (μ.real (doubleCosetSet K (g₁ * g₂)) : ℂ) = 1 := by
    rw [← hint]
    conv_rhs => rw [hF]
    simp only [smul_apply]
    rw [integral_const_mul, integral_massIndicator, mul_one]
  rw [hF, hc, one_smul]

/-- **Sandwich structure from a Cartan decomposition.** Suppose a compact subgroup `Γ`
normalizes `K`, a submonoid `M` satisfies `m₁ K m₂ ⊆ K m₁ m₂ K`, and every element is
`γ m γ'` with `γ, γ' ∈ Γ` and `m` in the monoid generated by finitely many pairwise
commuting elements `D i` of `M`. Then the corner is spanned by products `x i * m * x j`
with `m` in the subalgebra generated by the commuting mass-one indicators of the `D i`. -/
theorem exists_sandwich_of_decomposition (Γ : Subgroup G) (hΓc : IsCompact (Γ : Set G))
    (hΓ : Γ ≤ Subgroup.normalizer (K.toSubgroup : Set G)) (M : Submonoid G)
    (hM : ∀ m₁ ∈ M, ∀ m₂ ∈ M, ∀ k ∈ K, m₁ * k * m₂ ∈ doubleCosetSet K (m₁ * m₂))
    {l : ℕ} (D : Fin l → G) (hDM : ∀ i, D i ∈ M) (hDcomm : ∀ i j, Commute (D i) (D j))
    (hdecomp : ∀ g : G, ∃ γ ∈ Γ, ∃ γ' ∈ Γ, ∃ m ∈ Submonoid.closure (Set.range D),
      g = γ * m * γ') :
    ∃ (q : ℕ) (x : Fin q → Corner μ K hK) (a : Fin l → Corner μ K hK),
      (∀ i j, Commute (a i) (a j)) ∧
      Submodule.span ℂ
        {y | ∃ i j, ∃ m ∈ Algebra.adjoin ℂ (Set.range a), y = x i * m * x j} = ⊤ := by
  classical
  -- finitely many representatives of `Γ / K`
  obtain ⟨t, ht⟩ := hΓc.elim_finite_subcover
    (fun γ : Γ => (fun y : G => (γ : G)⁻¹ * y) ⁻¹' (K : Set G))
    (fun γ => K.isOpen.preimage (continuous_const.mul continuous_id))
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, by simp⟩)
  let R : Fin t.card → G := fun i => ((t.equivFin.symm i : t) : Γ)
  have hR : ∀ i, R i ∈ Subgroup.normalizer (K.toSubgroup : Set G) := fun i => hΓ ((t.equivFin.symm i : t) : Γ).2
  have hcover : ∀ γ ∈ Γ, ∃ i, (R i)⁻¹ * γ ∈ K := by
    intro γ hγ
    have := ht hγ
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
    obtain ⟨r, hr, hγr⟩ := this
    refine ⟨t.equivFin ⟨r, hr⟩, ?_⟩
    simpa [R] using hγr
  let a : Fin l → Corner μ K hK := fun i => massIndicator K hK μ (D i)
  have hclM : Submonoid.closure (Set.range D) ≤ M :=
    (Submonoid.closure_le).2 (Set.range_subset_iff.2 hDM)
  have hadj : ∀ m ∈ Submonoid.closure (Set.range D),
      massIndicator K hK μ m ∈ Algebra.adjoin ℂ (Set.range a) := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem m hm =>
      obtain ⟨i, rfl⟩ := hm
      exact Algebra.subset_adjoin ⟨i, rfl⟩
    | one =>
      rw [massIndicator_one]
      exact one_mem _
    | mul m₁ m₂ hm₁ hm₂ ih₁ ih₂ =>
      rw [← massIndicator_mul K hK μ (hM m₁ (hclM hm₁) m₂ (hclM hm₂))]
      exact mul_mem ih₁ ih₂
  refine ⟨t.card, fun i => doubleCoset K hK μ (R i), a, ?_, ?_⟩
  · intro i j
    change massIndicator K hK μ (D i) * massIndicator K hK μ (D j) =
      massIndicator K hK μ (D j) * massIndicator K hK μ (D i)
    rw [massIndicator_mul K hK μ (hM _ (hDM i) _ (hDM j)),
      massIndicator_mul K hK μ (hM _ (hDM j) _ (hDM i)), (hDcomm i j).eq]
  · rw [eq_top_iff, ← span_range_doubleCoset K hK μ, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    obtain ⟨γ, hγ, γ', hγ', m, hm, rfl⟩ := hdecomp g
    obtain ⟨i, hi⟩ := hcover γ hγ
    obtain ⟨j, hj⟩ := hcover γ' hγ'
    -- `γ m γ' ∈ K (R i) m (R j) K`
    have hmem : γ * m * γ' ∈ doubleCosetSet K (R i * m * R j) := by
      refine (mem_doubleCosetSet K _ _).2
        ⟨R i * ((R i)⁻¹ * γ) * (R i)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hR i) _).1 hi,
          (R j)⁻¹ * γ', hj, by group⟩
    apply Submodule.subset_span
    refine ⟨i, j, ((μ.real (doubleCosetSet K m) : ℂ) * (μ.real (K : Set G) : ℂ)⁻¹) •
      massIndicator K hK μ m, Subalgebra.smul_mem _ (hadj m hm) _, ?_⟩
    change doubleCoset K hK μ (γ * m * γ') =
      doubleCoset K hK μ (R i) * _ * doubleCoset K hK μ (R j)
    rw [doubleCoset_eq_of_mem K hK μ hmem,
      ← doubleCoset_mul_mul_of_mem_normalizer K hK μ (hR i) (hR j),
      ← doubleCoset_eq_smul_massIndicator]

end HeckeAlgebra.Corner

end Langlands.Hecke
