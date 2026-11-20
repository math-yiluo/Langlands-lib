import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormStabilizer
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartFlatness
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain
import Langlands.Geometry.Analytic.StrictTestDomain.SpectralDisplacement

/-! # Finite tests control rational charts (Berkovich 1994, Proposition 6.1, rational case)

Finitely many tests on the base of a rational chart keep a nearby map inside the chart and control
finitely many functions on the chart through the factorizations. -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open BanachSpectrum

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {S : PresentedAffinoidAlgebra K}

namespace RationalChart

omit [CompleteSpace K] in
/-- Some positive number is at most every radius of a rational chart. -/
theorem exists_le_radii (d : RationalChart K S) : ∃ r : ℝ, 0 < r ∧ ∀ j, r ≤ d.radii.radius j := by
  classical
  rcases isEmpty_or_nonempty (Fin d.arity) with h | h
  · exact ⟨1, one_pos, fun j => (IsEmpty.false j).elim⟩
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image Finset.univ d.radii.radius Finset.univ_nonempty
  exact ⟨d.radii.radius j₀, d.radii.positive j₀, fun j => hj₀ j (Finset.mem_univ j)⟩

omit [CompleteSpace K] in
/-- Ultrametric comparison: a perturbation smaller than the value does not change it. -/
theorem apply_eq_of_apply_sub_lt {B : PresentedAffinoidAlgebra K} (y : BanachSpectrum B)
    {b₁ b₂ : B} (h : y (b₂ - b₁) < y b₁) : y b₂ = y b₁ := by
  have hna := BanachSpectrum.isNonarchimedean (K := K) y
  have h₁ : y b₂ ≤ max (y b₁) (y (b₂ - b₁)) := by
    have := hna b₁ (b₂ - b₁)
    rwa [add_sub_cancel] at this
  have h₂ : y b₁ ≤ max (y b₂) (y (b₂ - b₁)) := by
    have := hna b₂ (-(b₂ - b₁))
    rwa [map_neg_eq_map, neg_sub, add_sub_cancel] at this
  refine le_antisymm (h₁.trans (max_le le_rfl h.le)) ?_
  rcases le_max_iff.1 h₂ with h₂ | h₂
  · exact h₂
  · exact absurd (h₂.trans_lt h) (lt_irrefl _)

omit [CompleteSpace K] in
/-- **Landing.** Finitely many tests on the base keep a map inside a rational chart: if `a₁` sends
the point `y` into the locus and `a₂` is close to `a₁` at `y` on the denominator and the
numerators, then `a₂` sends `y` into the locus. -/
theorem exists_landing_tests (d : RationalChart K S) :
    ∃ (G : Finset S) (δ : ℝ), 0 < δ ∧
      ∀ {B : PresentedAffinoidAlgebra K} (a₁ a₂ : BoundedAlgHom K S B) (y : BanachSpectrum B),
        comap a₁.toBoundedRingHom y ∈ d.locus →
        (∀ s ∈ G, y (a₂ s - a₁ s) ≤ δ) →
        comap a₂.toBoundedRingHom y ∈ d.locus := by
  classical
  obtain ⟨α, hα, hαle⟩ := exists_pos_le_denominator d
  obtain ⟨r, hr, hrle⟩ := exists_le_radii d
  let g : S := presentationMap K S d.denominator
  let f : Fin d.arity → S := fun j => presentationMap K S (d.numerators j)
  refine ⟨insert g (Finset.univ.image f), min (α / 2) (α * r), lt_min (by positivity)
    (by positivity), ?_⟩
  intro B a₁ a₂ y h1 hclose
  have hg : y (a₂ g - a₁ g) ≤ min (α / 2) (α * r) := hclose g (Finset.mem_insert_self _ _)
  have hf : ∀ j, y (a₂ (f j) - a₁ (f j)) ≤ min (α / 2) (α * r) := fun j =>
    hclose (f j) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have hα1 : α ≤ y (a₁ g) := hαle _ h1
  have heq : y (a₂ g) = y (a₁ g) :=
    apply_eq_of_apply_sub_lt y ((hg.trans (min_le_left _ _)).trans_lt
      ((half_lt_self hα).trans_le hα1))
  intro j
  change y (a₂ (f j)) ≤ d.radii.radius j * y (a₂ g)
  have h1j : y (a₁ (f j)) ≤ d.radii.radius j * y (a₁ g) := h1 j
  have hna := BanachSpectrum.isNonarchimedean (K := K) y (a₁ (f j)) (a₂ (f j) - a₁ (f j))
  rw [add_sub_cancel] at hna
  rw [heq]
  refine hna.trans (max_le h1j ((hf j).trans ((min_le_right _ _).trans ?_)))
  calc α * r ≤ α * d.radii.radius j := mul_le_mul_of_nonneg_left (hrle j) hα.le
    _ = d.radii.radius j * α := mul_comm _ _
    _ ≤ d.radii.radius j * y (a₁ g) := mul_le_mul_of_nonneg_left hα1 (d.radii.positive j).le

omit [CompleteSpace K] in
/-- Ultrametric estimate for a difference of powers. -/
theorem apply_pow_sub_pow_le {B : PresentedAffinoidAlgebra K} (y : BanachSpectrum B)
    (a b : B) (n : ℕ) :
    y (a ^ n - b ^ n) ≤ y (a - b) * max (y a) (y b) ^ (n - 1) := by
  have hna := BanachSpectrum.isNonarchimedean (K := K) y
  have hm : 0 ≤ max (y a) (y b) := le_max_of_le_left (apply_nonneg y.toMulRingSeminorm a)
  induction n with
  | zero => simp only [pow_zero, sub_self, map_zero, zero_tsub, mul_one]
            exact apply_nonneg y.toMulRingSeminorm _
  | succ n ih =>
    rcases n with _ | n
    · simp only [zero_add, pow_one, tsub_self, pow_zero, mul_one, le_refl]
    · have hsplit : a ^ (n + 2) - b ^ (n + 2) = a * (a ^ (n + 1) - b ^ (n + 1)) +
          b ^ (n + 1) * (a - b) := by ring
      rw [hsplit]
      refine (hna _ _).trans (max_le ?_ ?_)
      · rw [map_mul]
        calc y a * y (a ^ (n + 1) - b ^ (n + 1))
            ≤ max (y a) (y b) * (y (a - b) * max (y a) (y b) ^ (n + 1 - 1)) :=
              mul_le_mul (le_max_left _ _) ih (apply_nonneg _ _) hm
          _ = y (a - b) * max (y a) (y b) ^ (n + 2 - 1) := by
              rw [show n + 2 - 1 = n + 1 by omega, show n + 1 - 1 = n by omega]; ring
      · rw [map_mul, map_pow]
        calc y b ^ (n + 1) * y (a - b) ≤ max (y a) (y b) ^ (n + 1) * y (a - b) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (apply_nonneg _ _)
                (le_max_right _ _) _) (apply_nonneg _ _)
          _ = y (a - b) * max (y a) (y b) ^ (n + 2 - 1) := by
              rw [show n + 2 - 1 = n + 1 by omega]; ring

omit [CompleteSpace K] in
/-- **Function tests.** For a function `h` on a rational chart and a bound `ε`, finitely many
tests on the base control the values of `h` under the factorizations through the chart, at every
point that the first map sends into the locus. -/
theorem exists_function_tests (d : RationalChart K S) (h : d.algebra) {ε : ℝ} (hε : 0 < ε) :
    ∃ (G : Finset S) (δ : ℝ), 0 < δ ∧
      ∀ {B : PresentedAffinoidAlgebra K} (a₁ a₂ : BoundedAlgHom K S B)
        (a₁' a₂' : BoundedAlgHom K d.algebra B),
        a₁'.comp d.baseMap = a₁ → a₂'.comp d.baseMap = a₂ → ∀ y : BanachSpectrum B,
        comap a₁.toBoundedRingHom y ∈ d.locus →
        (∀ s ∈ G, y (a₂ s - a₁ s) ≤ δ) → y (a₂' h - a₁' h) ≤ ε := by
  classical
  obtain ⟨α₀, hα₀, hα₀le⟩ := exists_pos_le_denominator d
  set α : ℝ := min α₀ 1 with hαdef
  have hα : 0 < α := lt_min hα₀ one_pos
  have hα1 : α ≤ 1 := min_le_right _ _
  let g : S := presentationMap K S d.denominator
  have hdense := RationalPresentation.dense_fractionSubalgebra K S d.radii d.denominator
    d.numerators
  obtain ⟨z, hz, hzh⟩ := hdense.exists_dist_lt h hε
  obtain ⟨n, s', hzs⟩ := hz
  set M : ℝ := max 1 ‖s'‖ with hMdef
  have hM : 0 < M := lt_max_of_lt_left one_pos
  set δ : ℝ := min (α / 2) (ε * α ^ (n + 1) / M) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨{g, s'}, δ, hδ, ?_⟩
  intro B a₁ a₂ a₁' a₂' h₁ h₂ y hy hclose
  have hg : y (a₂ g - a₁ g) ≤ δ := hclose g (by simp)
  have hs : y (a₂ s' - a₁ s') ≤ δ := hclose s' (by simp)
  -- the two values of the denominator agree and are at least `α`
  have hu₁ : α ≤ y (a₁ g) := (min_le_left _ _).trans (hα₀le _ hy)
  have hu : y (a₂ g) = y (a₁ g) :=
    apply_eq_of_apply_sub_lt y ((hg.trans (min_le_left _ _)).trans_lt
      ((half_lt_self hα).trans_le hu₁))
  -- the equations of the fraction
  let z' : Carrier K d.algebra := z
  have hzh' : dist h z' < ε := hzh
  have hzs' : d.baseMap g ^ n * z' = d.baseMap s' := hzs
  have he₁ : a₁ g ^ n * a₁' z' = a₁ s' := by
    have := congrArg a₁' hzs'
    rw [map_mul, map_pow] at this
    subst h₁
    exact this
  have he₂ : a₂ g ^ n * a₂' z' = a₂ s' := by
    have := congrArg a₂' hzs'
    rw [map_mul, map_pow] at this
    subst h₂
    exact this
  have hna := BanachSpectrum.isNonarchimedean (K := K) y
  set c : ℝ := y (a₁ g) with hcdef
  have hc : 0 < c := hα.trans_le hu₁
  have hαc : α ≤ c := hu₁
  have hcn : ∀ k : ℕ, α ^ k ≤ c ^ k := fun k => pow_le_pow_left₀ hα.le hαc k
  have hs'M : y (a₁ s') ≤ M :=
    ((comap a₁.toBoundedRingHom y).le_norm s').trans (le_max_right _ _)
  have hδ₁ : δ ≤ ε * α ^ (n + 1) / M := min_le_right _ _
  have hMδ : M * δ ≤ ε * α ^ (n + 1) := by
    rw [le_div_iff₀ hM] at hδ₁; linarith [mul_comm M δ]
  -- the difference of the two values of the fraction
  set D := a₂' z' - a₁' z' with hDdef
  have hid : a₁ g ^ n * a₂ g ^ n * D =
      a₁ g ^ n * (a₂ s' - a₁ s') + a₁ s' * (a₁ g ^ n - a₂ g ^ n) := by
    rw [hDdef]; linear_combination (a₁ g ^ n) * he₂ - (a₂ g ^ n) * he₁
  have hpow : y (a₁ g ^ n - a₂ g ^ n) ≤ δ * c ^ (n - 1) := by
    have h0 := apply_pow_sub_pow_le y (a₁ g) (a₂ g) n
    have h1 : y (a₁ g - a₂ g) ≤ δ := by
      rw [← map_neg_eq_map, neg_sub]; exact hg
    rw [hu, max_self] at h0
    exact h0.trans (mul_le_mul_of_nonneg_right h1 (pow_nonneg hc.le _))
  have hlhs : y (a₁ g ^ n * a₂ g ^ n * D) = c ^ n * c ^ n * y D := by
    rw [map_mul, map_mul, map_pow, map_pow, hu]
  have hrhs : y (a₁ g ^ n * (a₂ s' - a₁ s') + a₁ s' * (a₁ g ^ n - a₂ g ^ n)) ≤
      max (c ^ n * δ) (M * (δ * c ^ (n - 1))) := by
    refine (hna _ _).trans (max_le_max ?_ ?_)
    · rw [map_mul, map_pow]
      exact mul_le_mul_of_nonneg_left (hs.trans le_rfl) (pow_nonneg hc.le _)
    · rw [map_mul]
      exact mul_le_mul hs'M hpow (apply_nonneg _ _) hM.le
  have hbound : max (c ^ n * δ) (M * (δ * c ^ (n - 1))) ≤ c ^ n * c ^ n * ε := by
    refine max_le ?_ ?_
    · have : δ ≤ c ^ n * ε := by
        have h1 : ε * α ^ (n + 1) / M ≤ ε * α ^ n := by
          rw [div_le_iff₀ hM]
          have hαn : α ^ (n + 1) ≤ α ^ n := pow_le_pow_of_le_one hα.le hα1 (Nat.le_succ n)
          have : ε * α ^ (n + 1) ≤ ε * α ^ n := mul_le_mul_of_nonneg_left hαn hε.le
          have h3 : ε * α ^ n ≤ ε * α ^ n * M :=
            le_mul_of_one_le_right (by positivity) (le_max_left _ _)
          linarith
        have h2 : ε * α ^ n ≤ c ^ n * ε := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hcn n) hε.le
        linarith
      calc c ^ n * δ ≤ c ^ n * (c ^ n * ε) := mul_le_mul_of_nonneg_left this (pow_nonneg hc.le _)
        _ = c ^ n * c ^ n * ε := by ring
    · rcases n with _ | k
      · rw [show (0 : ℕ) - 1 = 0 from rfl, pow_zero]
        have h4 : M * δ ≤ ε * α := by simpa using hMδ
        have h5 : ε * α ≤ ε := mul_le_of_le_one_right hε.le hα1
        simp only [mul_one, one_mul]
        linarith
      · have h1 : M * δ ≤ ε * c ^ (k + 2) := hMδ.trans
          (mul_le_mul_of_nonneg_left (hcn (k + 2)) hε.le)
        calc M * (δ * c ^ (k + 1 - 1)) = (M * δ) * c ^ k := by
              rw [show k + 1 - 1 = k by omega]; ring
          _ ≤ (ε * c ^ (k + 2)) * c ^ k := mul_le_mul_of_nonneg_right h1 (pow_nonneg hc.le _)
          _ = c ^ (k + 1) * c ^ (k + 1) * ε := by ring
  have hD : y D ≤ ε := by
    have h := hlhs ▸ (hid ▸ hrhs).trans hbound
    have hpos : 0 < c ^ n * c ^ n := by positivity
    nlinarith [apply_nonneg y.toMulRingSeminorm D]
  -- the approximation errors
  have happ : ∀ (a' : BoundedAlgHom K d.algebra B) (w : d.algebra), ‖w‖ < ε → y (a' w) ≤ ε :=
    fun a' w hw => ((comap a'.toBoundedRingHom y).le_norm w).trans hw.le
  have hhz : ‖h - z'‖ < ε := by rwa [← dist_eq_norm]
  have hzh2 : ‖z' - h‖ < ε := by rwa [norm_sub_rev]
  have hsplit : a₂' h - a₁' h = a₂' (h - z') + D + a₁' (z' - h) := by
    rw [hDdef, map_sub, map_sub]; ring
  rw [hsplit]
  refine (hna _ _).trans (max_le ((hna _ _).trans (max_le (happ a₂' _ hhz) hD))
    (happ a₁' _ hzh2))

omit [CompleteSpace K] in
/-- **Function tests, finite form.** The tests of `exists_function_tests` for finitely many
functions on a rational chart at once. -/
theorem exists_finset_function_tests (d : RationalChart K S) (F : Finset d.algebra) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (G : Finset S) (δ : ℝ), 0 < δ ∧
      ∀ {B : PresentedAffinoidAlgebra K} (a₁ a₂ : BoundedAlgHom K S B)
        (a₁' a₂' : BoundedAlgHom K d.algebra B),
        a₁'.comp d.baseMap = a₁ → a₂'.comp d.baseMap = a₂ → ∀ y : BanachSpectrum B,
        comap a₁.toBoundedRingHom y ∈ d.locus →
        (∀ s ∈ G, y (a₂ s - a₁ s) ≤ δ) → ∀ h ∈ F, y (a₂' h - a₁' h) ≤ ε := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨∅, 1, one_pos, ?_⟩
    intro B a₁ a₂ a₁' a₂' _ _ y _ _ h hh
    simp at hh
  | insert h F _ ih =>
    obtain ⟨G₁, δ₁, hδ₁, H₁⟩ := ih
    obtain ⟨G₂, δ₂, hδ₂, H₂⟩ := exists_function_tests d h hε
    refine ⟨G₁ ∪ G₂, min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
    intro B a₁ a₂ a₁' a₂' e₁ e₂ y hy hc k hk
    rcases Finset.mem_insert.1 hk with rfl | hk
    · exact H₂ a₁ a₂ a₁' a₂' e₁ e₂ y hy fun s hs =>
        (hc s (Finset.mem_union_right _ hs)).trans (min_le_right _ _)
    · exact H₁ a₁ a₂ a₁' a₂' e₁ e₂ y hy (fun s hs =>
        (hc s (Finset.mem_union_left _ hs)).trans (min_le_left _ _)) k hk

omit [CompleteSpace K] in
/-- **Pointwise transfer.** Finitely many tests on the base, checked at a point `y` which the
first map sends into the locus, send `y` into the locus under the second map and control
finitely many functions on the chart through the factorizations. -/
theorem exists_pointwise_transfer_tests (d : RationalChart K S) (F : Finset d.algebra) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (G : Finset S) (δ : ℝ), 0 < δ ∧
      ∀ {B : PresentedAffinoidAlgebra K} (a₁ a₂ : BoundedAlgHom K S B) (y : BanachSpectrum B),
        comap a₁.toBoundedRingHom y ∈ d.locus →
        (∀ s ∈ G, y (a₂ s - a₁ s) ≤ δ) →
        comap a₂.toBoundedRingHom y ∈ d.locus ∧
          ∀ a₁' a₂' : BoundedAlgHom K d.algebra B,
            a₁'.comp d.baseMap = a₁ → a₂'.comp d.baseMap = a₂ →
            ∀ h ∈ F, y (a₂' h - a₁' h) ≤ ε := by
  classical
  obtain ⟨G₁, δ₁, hδ₁, H₁⟩ := exists_landing_tests d
  obtain ⟨G₂, δ₂, hδ₂, H₂⟩ := exists_finset_function_tests d F hε
  refine ⟨G₁ ∪ G₂, min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro B a₁ a₂ y hy hc
  refine ⟨H₁ a₁ a₂ y hy fun s hs =>
    (hc s (Finset.mem_union_left _ hs)).trans (min_le_left _ _), ?_⟩
  intro a₁' a₂' e₁ e₂
  exact H₂ a₁ a₂ a₁' a₂' e₁ e₂ y hy fun s hs =>
    (hc s (Finset.mem_union_right _ hs)).trans (min_le_right _ _)

omit [CompleteSpace K] in
/-- A map that factors through a rational chart sends every point into its locus. -/
theorem comap_comp_baseMap_mem_locus (d : RationalChart K S) {B : PresentedAffinoidAlgebra K}
    (a : BoundedAlgHom K d.algebra B) (y : BanachSpectrum B) :
    comap (a.comp d.baseMap).toBoundedRingHom y ∈ d.locus := by
  rw [← d.range_comap_baseMap]
  exact ⟨comap a.toBoundedRingHom y, BanachSpectrum.ext fun _ => rfl⟩

/-- **Transfer of tests through a rational chart** (Berkovich 1994, Proposition 6.1, for a
rational chart). Finitely many functions `F` on the chart and a bound `ε` determine finitely many
functions `D` on the base and a bound `δ`: whenever a map `b` out of the base is uniformly
`δ`-close on `D` to a map `old` that factors through the chart, `b` factors through the chart as
well, and its factorization is uniformly `ε`-close to `old` on `F`. -/
theorem exists_transfer_tests (d : RationalChart K S) (F : Finset d.algebra) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (D : Finset S) (δ : ℝ), 0 < δ ∧
      ∀ {B : PresentedAffinoidAlgebra K} (old : BoundedAlgHom K d.algebra B)
        (b : BoundedAlgHom K S B),
        (∀ s ∈ D, SpectralBound (b s - old (d.baseMap s)) δ) →
        ∃ b' : BoundedAlgHom K d.algebra B, b'.comp d.baseMap = b ∧
          ∀ h ∈ F, SpectralBound (b' h - old h) ε := by
  classical
  obtain ⟨D, δ, hδ, H⟩ := exists_pointwise_transfer_tests d F hε
  refine ⟨D, δ, hδ, ?_⟩
  intro B old b hc
  have hc' : ∀ y : BanachSpectrum B, ∀ s ∈ D, y (b s - (old.comp d.baseMap) s) ≤ δ :=
    fun y s hs => hc s hs y
  have hland : HasImageIn K b d.locus := fun y =>
    (H (old.comp d.baseMap) b y (comap_comp_baseMap_mem_locus d old y) (hc' y)).1
  obtain ⟨b', hb', -⟩ := d.represents.2.2 B b hland
  exact ⟨b', hb', fun h hh y =>
    (H (old.comp d.baseMap) b y (comap_comp_baseMap_mem_locus d old y) (hc' y)).2
      old b' rfl hb' h hh⟩

end RationalChart

end Langlands.Analytic.PresentedAffinoidAlgebra
