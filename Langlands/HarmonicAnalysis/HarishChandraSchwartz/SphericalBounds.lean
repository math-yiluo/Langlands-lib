import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermBound
import Mathlib.Analysis.PSeries

/-! # Bounds for `Ξ` and the weight `δ₀(m₀(ū))^{1/2}` (Waldspurger II.1.1, II.4.2, II.4.4)

Three deductions from Waldspurger 2003, each over abstract data with the structural and
analytic inputs as explicit hypotheses:

* the lower bound of Lemma II.1.1, `mes(H) δ₀(m)^{1/2} ≤ Ξ(m)`, for the spherical function
  `xi` of `Spherical`, from a factorization `H = (H ∩ P₀) V` of an open subgroup `H ⊆ K`
  and the inclusions `m⁻¹ V m ⊆ K` (Waldspurger's proof, with `V = H ∩ Ū₀`);
* Lemma II.4.4, from the upper bound of Lemma II.1.1 on Cartan representatives, the
  Cartan covering of `G` and Lemma II.3.2;
* Lemma II.4.2, from the level-set bound of Lemma II.4.1 and the comparison of Lemma
  II.3.4 between `-log δ₀(m₀(ū))` and `1 + σ(ū)`.

The conclusions are the hypotheses `XiLowerBound`, `UnipotentXiBound` and
`UnipotentWeightIntegrable` of `ConstantTermBound`.
-/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory

namespace Langlands.HarishChandraSchwartz

universe u

section IwasawaWeight

variable {G : Type u} [Group G] {P K : Subgroup G} {hPK : IsIwasawaPair P K}
  {δ : P →* ℝ≥0ˣ} (hδ : ∀ p : P, (p : G) ∈ K → δ p = 1)
include hδ

/-- For `g ∈ P`, `φ(g x) = φ(g) φ(x)`, where `φ(p k) = δ(p)^{1/2}`. -/
theorem iwasawaWeight_mul_of_mem {g : G} (hg : g ∈ P) (x : G) :
    iwasawaWeight hPK δ (g * x) = iwasawaWeight hPK δ g * iwasawaWeight hPK δ x := by
  have h1 := iwasawaWeight_mul (hPK := hPK) hδ hg K.one_mem
  rw [mul_one] at h1
  rw [h1]
  exact iwasawaWeight_mul_left (hPK := hPK) hδ ⟨g, hg⟩ x

/-- `φ(p v g) = φ(g)` for `p ∈ P ∩ K` and `g⁻¹ v g ∈ K`. -/
theorem iwasawaWeight_mul_mul_eq {p v g : G} (hp : p ∈ P) (hpK : p ∈ K)
    (hv : g⁻¹ * v * g ∈ K) : iwasawaWeight hPK δ (p * v * g) = iwasawaWeight hPK δ g := by
  have h1 : p * v * g = ((⟨p, hp⟩ : P) : G) * g * (g⁻¹ * v * g) := by
    simp only
    group
  rw [h1, iwasawaWeight_mul_right (hPK := hPK) hδ _ hv,
    iwasawaWeight_mul_left (hPK := hPK) hδ, hδ ⟨p, hp⟩ hpK]
  simp

end IwasawaWeight

section LowerBound

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {P K : Subgroup G} [CompactSpace K]
  {hPK : IsIwasawaPair P K} {δ : P →* ℝ≥0ˣ}
  (hδ : ∀ p : P, (p : G) ∈ K → δ p = 1) (hK : IsOpen (K : Set G))
include hδ hK

/-- `mes(H ∩ K) φ(g) ≤ Ξ(g)` when `φ(h g) = φ(g)` for all `h ∈ H` (the measure is the
normalized Haar measure of `K`). -/
theorem measureReal_mul_iwasawaWeight_le_xi {H : Set G} (hH : IsOpen H) {g : G}
    (hg : ∀ h ∈ H, iwasawaWeight hPK δ (h * g) = iwasawaWeight hPK δ g) :
    (normalizedHaar K).real {k : K | (k : G) ∈ H} * iwasawaWeight hPK δ g ≤
      xi hPK δ g := by
  have hA : MeasurableSet {k : K | (k : G) ∈ H} :=
    (hH.preimage continuous_subtype_val).measurableSet
  calc (normalizedHaar K).real {k : K | (k : G) ∈ H} * iwasawaWeight hPK δ g
      = ∫ k in {k : K | (k : G) ∈ H}, iwasawaWeight hPK δ ((k : G) * g)
          ∂(normalizedHaar K) := by
        rw [setIntegral_congr_fun hA (f := fun k : K => iwasawaWeight hPK δ ((k : G) * g))
          (g := fun _ => iwasawaWeight hPK δ g) (fun k hk => hg k hk), setIntegral_const,
          smul_eq_mul]
    _ ≤ xi hPK δ g :=
        setIntegral_le_integral (integrable_iwasawaWeight_mul hδ hK g)
          (Filter.Eventually.of_forall fun _ => iwasawaWeight_nonneg _)

/-- The lower bound of Lemma II.1.1: if an open subgroup `H ≤ K` factors as
`H = (H ∩ P) V` and `g⁻¹ V g ⊆ K` for every `g ∈ S`, then `mes(H) φ(g) ≤ Ξ(g)` on `S`,
so `XiLowerBound (xi hPK δ) S φ` with `C = mes(H)⁻¹`. -/
theorem xiLowerBound_of_factorization {H : Subgroup G} (hHK : H ≤ K)
    (hH : IsOpen (H : Set G)) {V S : Set G}
    (hfac : ∀ h ∈ H, ∃ p ∈ P, p ∈ H ∧ ∃ v ∈ V, h = p * v)
    (hcontr : ∀ g ∈ S, ∀ v ∈ V, g⁻¹ * v * g ∈ K) :
    XiLowerBound (xi hPK δ) S (iwasawaWeight hPK δ) := by
  have hpos : 0 < (normalizedHaar K).real {k : K | (k : G) ∈ H} := by
    have hopen : IsOpen {k : K | (k : G) ∈ H} := hH.preimage continuous_subtype_val
    have hne : ({k : K | (k : G) ∈ H} : Set K).Nonempty := ⟨1, H.one_mem⟩
    exact ENNReal.toReal_pos (hopen.measure_pos (normalizedHaar K) hne).ne'
      (measure_ne_top _ _)
  refine ⟨((normalizedHaar K).real {k : K | (k : G) ∈ H})⁻¹, fun g hg => ?_⟩
  have h := measureReal_mul_iwasawaWeight_le_xi (hPK := hPK) hδ hK hH (g := g)
    fun h hh => by
      obtain ⟨p, hp, hpH, v, hv, rfl⟩ := hfac h hh
      exact iwasawaWeight_mul_mul_eq (hPK := hPK) hδ hp (hHK hpH) (hcontr g hg v hv)
  rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
  exact h

end LowerBound

section Upper

/-- The upper bound of Lemma II.1.1 on `S`: there are `C` and `d` with
`Ξ(x) ≤ C e(x) (1 + σ(x))^d` for `x ∈ S`. For Waldspurger's `G`, `S = M̄⁺₀` and
`e = δ₀^{1/2}`; with `S = G` and `e(g) = δ₀(m₀(g))^{1/2}` it is the global form used in
Lemma II.4.4. -/
def XiUpperBound {X : Type*} (Ξ σ : X → ℝ) (S : Set X) (e : X → ℝ) : Prop :=
  ∃ C d : ℝ, ∀ x ∈ S, Ξ x ≤ C * e x * (1 + σ x) ^ d

variable {G : Type u} [Group G]

/-- Lemma II.3.2: there is `C` with `φ(s) ≤ C φ(k₁ s k₂)` for `s ∈ S` and `k₁, k₂ ∈ K`.
For Waldspurger's data `S = M̄⁺₀` and `φ(g) = δ₀(m₀(g))^{1/2}`; the lemma states
`δ₀(m) ≤ C δ₀(m₀(g))` for `g ∈ K m K`, which is this inequality with constant `C^{1/2}`. -/
def CartanWeightComparison (K : Subgroup G) (S : Set G) (φ : G → ℝ) : Prop :=
  ∃ C : ℝ, ∀ s ∈ S, ∀ k₁ ∈ K, ∀ k₂ ∈ K, φ s ≤ C * φ (k₁ * s * k₂)

/-- From Cartan representatives to all of `G` (first step of the proof of Lemma II.4.4):
the upper bound of Lemma II.1.1 on `S`, Lemma II.3.2 and `G = K S K` give
`Ξ(g) ≤ C φ(g) (1 + σ(g))^d` for every `g ∈ G`. -/
theorem XiUpperBound.univ_of_cartan {K : Subgroup G} {S : Set G} {Ξ σ φ : G → ℝ}
    (hcover : IsDoubleCosetCover K S)
    (hΞK : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, Ξ (k₁ * g * k₂) = Ξ g)
    (hσK : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, σ (k₁ * g * k₂) = σ g)
    (hσ : ∀ g, 0 ≤ σ g) (hφ : ∀ g, 0 ≤ φ g)
    (hup : XiUpperBound Ξ σ S φ) (h32 : CartanWeightComparison K S φ) :
    XiUpperBound Ξ σ Set.univ φ := by
  obtain ⟨C, d, hup⟩ := hup
  obtain ⟨C', h32⟩ := h32
  refine ⟨max C 0 * max C' 0, d, fun g _ => ?_⟩
  obtain ⟨k₁, hk₁, s, hs, k₂, hk₂, rfl⟩ := hcover g
  rw [hΞK k₁ hk₁ k₂ hk₂, hσK k₁ hk₁ k₂ hk₂]
  have h1 : φ s ≤ max C' 0 * φ (k₁ * s * k₂) :=
    (h32 s hs k₁ hk₁ k₂ hk₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hφ _))
  have hpow : 0 ≤ (1 + σ s) ^ d := by
    have := hσ s
    positivity
  have hφs := hφ s
  calc Ξ s ≤ C * φ s * (1 + σ s) ^ d := hup s hs
    _ ≤ max C 0 * φ s * (1 + σ s) ^ d := by gcongr; exact le_max_left _ _
    _ ≤ max C 0 * (max C' 0 * φ (k₁ * s * k₂)) * (1 + σ s) ^ d := by gcongr
    _ = max C 0 * max C' 0 * φ (k₁ * s * k₂) * (1 + σ s) ^ d := by ring

/-- Lemma II.4.4 from the global upper bound: if `φ(m u) = e(m) w(u)` for `m ∈ S` and
`u ∈ U`, then `UnipotentXiBound Ξ σ S e w`. -/
theorem XiUpperBound.unipotentXiBound {M U : Subgroup G} {Ξ σ φ : G → ℝ} {S : Set M}
    {e : M → ℝ} {w : U → ℝ} (h : XiUpperBound Ξ σ Set.univ φ)
    (hmul : ∀ m ∈ S, ∀ u : U, φ ((m : G) * u) = e m * w u) :
    UnipotentXiBound Ξ σ S e w := by
  obtain ⟨C, d, h⟩ := h
  refine ⟨d, C, fun m hm u => ?_⟩
  rw [mul_assoc C, ← hmul m hm u]
  exact h _ (Set.mem_univ _)

/-- Lemma II.4.4 for the weight `φ(p k) = δ(p)^{1/2}` of `Spherical`: for `S ⊆ M ∩ P`,
`Ξ(m u) ≤ C φ(m) φ(u) (1 + σ(m u))^d`. For Waldspurger's `P₀` and `δ₀`, `φ(m) = δ₀(m)^{1/2}`
for `m ∈ M₀` and `φ(ū) = δ₀(m₀(ū))^{1/2}`. -/
theorem XiUpperBound.unipotentXiBound_iwasawaWeight {P K M U : Subgroup G}
    {hPK : IsIwasawaPair P K} {δ : P →* ℝ≥0ˣ} (hδ : ∀ p : P, (p : G) ∈ K → δ p = 1)
    {Ξ σ : G → ℝ} {S : Set M} (hSP : ∀ m ∈ S, (m : G) ∈ P)
    (h : XiUpperBound Ξ σ Set.univ (iwasawaWeight hPK δ)) :
    UnipotentXiBound Ξ σ S (fun m => iwasawaWeight hPK δ m)
      (fun u : U => iwasawaWeight hPK δ u) :=
  h.unipotentXiBound fun m hm u => iwasawaWeight_mul_of_mem hδ (hSP m hm) u

end Upper

section Integrability

variable {G : Type u} [Group G] [MeasurableSpace G] {U : Subgroup G}

/-- Lemma II.4.1: there are `C` and `d` with `ν{u : N(u) = n} ≤ C q^{n/2} n^d` for every
integer `n ≥ 1`. For Waldspurger's data `δ₀(m₀(ū)) = q^{-N(ū)}`, so `{N = n}` is his
`Ū(n)`. -/
def LevelSetMeasureBound (ν : Measure U) (N : U → ℤ) (q : ℝ) : Prop :=
  ∃ C d : ℝ, ∀ n : ℕ, 1 ≤ n →
    ν {u | N u = n} ≤ ENNReal.ofReal (C * q ^ ((n : ℝ) / 2) * (n : ℝ) ^ d)

variable (U) in
/-- The outer inequalities of Lemma II.3.4 for `P₀`, on `U`: there are `C₀`, `C₁ > 0` and
`C₂ > 0` with `C₁ (1 + σ(u)) ≤ C₀ + N(u) log q ≤ C₂ (1 + σ(u))`. For Waldspurger's data
`N(ū) log q = -log δ₀(m₀(ū))`. -/
def LevelHeightComparison (N : U → ℤ) (q : ℝ) (σ : G → ℝ) : Prop :=
  ∃ C₀ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ u : U,
    C₁ * (1 + σ u) ≤ C₀ + N u * Real.log q ∧ C₀ + N u * Real.log q ≤ C₂ * (1 + σ u)

/-- Lemma II.4.2: if `w(u) = q^{-N(u)/2}` with `q > 1` and a measurable `N : U → ℤ`, the
sublevel sets of `σ` have finite measure, and Lemmas II.4.1 and II.3.4 hold in the form of
`LevelSetMeasureBound` and `LevelHeightComparison`, then
`∫_U w(u) (1 + σ(u))^{-d} dν(u) < ∞` for some `d`. -/
theorem unipotentWeightIntegrable_of_levelSets {ν : Measure U} {N : U → ℤ} {q : ℝ}
    {σ : G → ℝ} {w : U → ℝ} (hq : 1 < q) (hN : Measurable N)
    (hw : ∀ u, w u = q ^ (-(N u : ℝ) / 2)) (hσ : ∀ g, 0 ≤ σ g)
    (hfin : ∀ R : ℝ, ν {u : U | σ u ≤ R} < ⊤)
    (h41 : LevelSetMeasureBound ν N q) (h34 : LevelHeightComparison U N q σ) :
    UnipotentWeightIntegrable ν w σ := by
  obtain ⟨C, d', h41⟩ := h41
  obtain ⟨C₀, C₁, C₂, hC₁, hC₂, h34⟩ := h34
  have hlog : 0 < Real.log q := Real.log_pos hq
  have hq0 : 0 < q := by linarith
  set d := max (d' + 2) 0 with hd_def
  have hd0 : 0 ≤ d := le_max_right _ _
  have hdd : d' + 2 ≤ d := le_max_left _ _
  refine ⟨d, ?_⟩
  set f : U → ℝ≥0∞ := fun u => ENNReal.ofReal (w u * (1 + σ u) ^ (-d)) with hf_def
  set A : Set U := {u | N u ≤ 0} with hA_def
  have hA : MeasurableSet A := hN measurableSet_Iic
  rw [← lintegral_add_compl f hA]
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · -- the levels `N ≤ 0`: a set of finite measure on which `f` is bounded
    set R := C₀ / C₁ - 1
    set n₀ := (C₁ - C₀) / Real.log q
    have hbound : ∀ u ∈ A, f u ≤ ENNReal.ofReal (q ^ (-n₀ / 2)) := by
      intro u hu
      have hNu : (N u : ℝ) ≤ 0 := by exact_mod_cast hu
      have h1 := (h34 u).1
      have hσu := hσ u
      have hn₀ : n₀ ≤ N u := by
        rw [div_le_iff₀ hlog]
        nlinarith
      have hw' : w u ≤ q ^ (-n₀ / 2) := by
        rw [hw]
        exact Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
      have hp : (1 + σ u) ^ (-d) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      refine ENNReal.ofReal_le_ofReal ?_
      calc w u * (1 + σ u) ^ (-d) ≤ q ^ (-n₀ / 2) * 1 :=
            mul_le_mul hw' hp (by positivity) (by positivity)
        _ = q ^ (-n₀ / 2) := mul_one _
    have hAR : A ⊆ {u : U | σ u ≤ R} := by
      intro u hu
      have hNu : (N u : ℝ) ≤ 0 := by exact_mod_cast (show N u ≤ 0 from hu)
      have h1 := (h34 u).1
      have h2 : 1 + σ u ≤ C₀ / C₁ := by
        rw [le_div_iff₀ hC₁]
        nlinarith
      show σ u ≤ C₀ / C₁ - 1
      linarith
    calc ∫⁻ u in A, f u ∂ν ≤ ∫⁻ _ in A, ENNReal.ofReal (q ^ (-n₀ / 2)) ∂ν :=
          setLIntegral_mono' hA hbound
      _ = ENNReal.ofReal (q ^ (-n₀ / 2)) * ν A := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((measure_mono hAR).trans_lt (hfin R))
  · -- the levels `N = n + 1`, `n ∈ ℕ`: Lemma II.4.1 and the lower bound `1 + σ ≥ c N`
    have hAc : Aᶜ = ⋃ n : ℕ, {u : U | N u = (n : ℤ) + 1} := by
      ext u
      simp only [hA_def, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, Set.mem_iUnion]
      constructor
      · intro h
        exact ⟨(N u - 1).toNat, by omega⟩
      · rintro ⟨n, hn⟩
        omega
    have hmeas : ∀ n : ℕ, MeasurableSet {u : U | N u = (n : ℤ) + 1} :=
      fun n => hN (measurableSet_singleton _)
    have hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ => {u : U | N u = (n : ℤ) + 1}) := by
      intro i j hij
      refine Set.disjoint_left.mpr fun u hi hj => hij ?_
      simp only [Set.mem_ofPred_eq] at hi hj
      omega
    rw [hAc, lintegral_iUnion hmeas hdisj f]
    set c := Real.log q / (C₂ + |C₀|)
    have hc : 0 < c := div_pos hlog (by positivity)
    set g : ℕ → ℝ := fun n => max C 0 * c ^ (-d) * ((n : ℝ) + 1) ^ (d' - d)
    have hg0 : ∀ n, 0 ≤ g n := fun n => by positivity
    have hlevel : ∀ n : ℕ, ∫⁻ u in {u : U | N u = (n : ℤ) + 1}, f u ∂ν ≤
        ENNReal.ofReal (g n) := by
      intro n
      set k : ℝ := (n : ℝ) + 1
      have hk : 1 ≤ k := by simp only [k]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hk0 : 0 < k := by linarith
      have hbound : ∀ u ∈ {u : U | N u = (n : ℤ) + 1},
          f u ≤ ENNReal.ofReal (q ^ (-k / 2) * (c * k) ^ (-d)) := by
        intro u hu
        have hNu : (N u : ℝ) = k := by
          simp only [Set.mem_ofPred_eq] at hu
          simp only [k, hu]
          push_cast
          ring
        have h2 := (h34 u).2
        have hσu := hσ u
        have hck : c * k ≤ 1 + σ u := by
          have hpos : 0 < C₂ + |C₀| := by positivity
          simp only [c]
          rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
          have habs : -C₀ ≤ |C₀| * (1 + σ u) := by
            have := neg_le_abs C₀
            have := abs_nonneg C₀
            nlinarith
          rw [hNu] at h2
          nlinarith
        have hp : (1 + σ u) ^ (-d) ≤ (c * k) ^ (-d) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hck (by linarith)
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hw, hNu, neg_div]
        exact mul_le_mul_of_nonneg_left hp (by positivity)
      have hν : ν {u : U | N u = (n : ℤ) + 1} ≤
          ENNReal.ofReal (max C 0 * q ^ (k / 2) * k ^ d') := by
        have h := h41 (n + 1) (by omega)
        push_cast at h
        refine h.trans (ENNReal.ofReal_le_ofReal ?_)
        have : 0 ≤ q ^ (k / 2) * k ^ d' := by positivity
        calc C * q ^ (k / 2) * k ^ d' = C * (q ^ (k / 2) * k ^ d') := by ring
          _ ≤ max C 0 * (q ^ (k / 2) * k ^ d') :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) this
          _ = max C 0 * q ^ (k / 2) * k ^ d' := by ring
      have e1 : q ^ (-k / 2) * q ^ (k / 2) = 1 := by
        rw [← Real.rpow_add hq0, show -k / 2 + k / 2 = 0 by ring, Real.rpow_zero]
      have e2 : (c * k) ^ (-d) = c ^ (-d) * k ^ (-d) := Real.mul_rpow hc.le hk0.le
      have e3 : k ^ (-d) * k ^ d' = k ^ (d' - d) := by
        rw [← Real.rpow_add hk0]
        ring_nf
      calc ∫⁻ u in {u : U | N u = (n : ℤ) + 1}, f u ∂ν
          ≤ ∫⁻ _ in {u : U | N u = (n : ℤ) + 1},
              ENNReal.ofReal (q ^ (-k / 2) * (c * k) ^ (-d)) ∂ν :=
            setLIntegral_mono' (hmeas n) hbound
        _ = ENNReal.ofReal (q ^ (-k / 2) * (c * k) ^ (-d)) *
              ν {u : U | N u = (n : ℤ) + 1} := setLIntegral_const _ _
        _ ≤ ENNReal.ofReal (q ^ (-k / 2) * (c * k) ^ (-d)) *
              ENNReal.ofReal (max C 0 * q ^ (k / 2) * k ^ d') := by gcongr
        _ = ENNReal.ofReal (q ^ (-k / 2) * (c * k) ^ (-d) *
              (max C 0 * q ^ (k / 2) * k ^ d')) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ = ENNReal.ofReal (g n) := by
            congr 1
            simp only [g]
            rw [e2]
            calc q ^ (-k / 2) * (c ^ (-d) * k ^ (-d)) * (max C 0 * q ^ (k / 2) * k ^ d')
                = max C 0 * c ^ (-d) * (k ^ (-d) * k ^ d') * (q ^ (-k / 2) * q ^ (k / 2)) := by
                  ring
              _ = max C 0 * c ^ (-d) * k ^ (d' - d) := by rw [e1, e3, mul_one]
    have hsum : Summable g := by
      have hp : d' - d < -1 := by linarith
      have h := ((summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)).mul_left
        (max C 0 * c ^ (-d))
      refine h.congr fun n => ?_
      simp only [g]
      push_cast
      ring
    calc ∑' n : ℕ, ∫⁻ u in {u : U | N u = (n : ℤ) + 1}, f u ∂ν
        ≤ ∑' n : ℕ, ENNReal.ofReal (g n) := ENNReal.tsum_le_tsum hlevel
      _ = ENNReal.ofReal (∑' n, g n) := (ENNReal.ofReal_tsum_of_nonneg hg0 hsum).symm
      _ < ⊤ := ENNReal.ofReal_lt_top

end Integrability

end Langlands.HarishChandraSchwartz
