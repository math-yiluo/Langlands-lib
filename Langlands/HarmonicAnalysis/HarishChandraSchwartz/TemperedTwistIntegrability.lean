import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitPolynomialOperator
import Langlands.Representation.Smooth.Schur.Proof

/-! # Tempered representations and the hypotheses of Waldspurger, Proposition III.7.1

In the proof of Proposition III.7.1 (printed pp. 274–275), Waldspurger uses two consequences of
the temperedness of an irreducible representation `π`: the characters `χ` with `π ≃ ω ⊗ χ` are
unitary ("Comme `π` est tempérée, `S(π) ⊂ Im X(G)`"), and the Schur orthogonality relation
III.1 (2) holds for a tempered `π₂` ("qui se généralise au cas où `π₂` est seulement tempérée"),
whose integral converges "d'après III.1.2 et II.1.5" (printed p. 265). The Library's
`TraceFamilyScalar` and `OrbitPolynomialOperator` take the convergence as the hypothesis `hint`
and the unitarity of central characters as explicit hypotheses.

This module derives them from temperedness, in the abstract setting of `TraceFamilyScalar`
(a surjective `p : G →* Λ` with open kernel for `G → G/G¹`, a central `A` for `A_G` with
`Λ / p(A)` finite):

* `exists_centralCharacter_of_isIrreducible`: `A` acts on an irreducible admissible
  representation through a character (Schur's lemma);
* `norm_centralCharacter_eq_one`: this character is unitary when the representation has tempered
  coefficients, `Ξ` is invariant under `A` and `σ` is subadditive;
* `integrable_orthogonalityIntegrand_of_tempered`: the convergence for a unitary twist with open
  kernel, from the tempered growth of `π`, the rapid decay of the coefficients of `ω` on `ker p`
  (in place of III.1.2), the translation bounds of the weights and `∫_G Ξ² (1 + σ)^{-d} < ∞`
  (II.1.5);
* `hint_of_tempered`: the hypothesis `hint` for a tempered `π` with unitary central character,
  when every character of `G` with open kernel and absolute value `1` on `A` is unitary
  (`IsUnitaryDetecting A`; sufficient condition `isUnitaryDetecting_of_norm_eq_one_on_ker`);
* `hsub_of_tempered`, `existsUnique_orbitIsotypic_decomposition_of_tempered`,
  `orbitPolynomialOperator_eq_smul_of_equiv_of_tempered`,
  `orbitPolynomialOperator_eq_zero_of_tempered`: Corollary III.7.2 and Proposition III.7.1 (ii),
  (iii) for tempered representations without these hypotheses. -/

noncomputable section

open MeasureTheory Filter Topology

namespace Langlands.HarishChandraSchwartz

open Langlands.Plancherel

section Growth

/-- A nonnegative real number whose powers grow at most polynomially is at most `1`. -/
theorem le_one_of_pow_le {x D : ℝ} (k : ℕ)
    (h : ∀ n : ℕ, x ^ n ≤ D * (1 + n) ^ k) : x ≤ 1 := by
  by_contra hx1
  push Not at hx1
  have hD : 1 ≤ D := by simpa using h 0
  have hpos : 0 < 1 / (D * 2 ^ k) := by positivity
  obtain ⟨n, hn1, hn⟩ := ((eventually_ge_atTop 1).and
    ((tendsto_pow_const_div_const_pow_of_one_lt k hx1).eventually (gt_mem_nhds hpos))).exists
  have hxn : 0 < x ^ n := pow_pos (by linarith) n
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h2 : x ^ n ≤ D * 2 ^ k * (n : ℝ) ^ k := by
    calc x ^ n ≤ D * (1 + n) ^ k := h n
      _ ≤ D * (2 * (n : ℝ)) ^ k := by gcongr; linarith
      _ = D * 2 ^ k * (n : ℝ) ^ k := by rw [mul_pow]; ring
  rw [div_lt_div_iff₀ hxn (by positivity), one_mul] at hn
  linarith

end Growth

section Character

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (A : Subgroup G) (hA : A ≤ Subgroup.center G)

include hA in
/-- **Schur's lemma for a central subgroup**: `A` acts on an irreducible admissible
representation through a character. -/
theorem exists_centralCharacter_of_isIrreducible (hρa : IsAdmissible ρ)
    (hρi : ρ.IsIrreducible) :
    ∃ c : A →* ℂˣ, ∀ (a : A) (x : V), ρ a x = (c a : ℂ) • x := by
  obtain ⟨chi, -, hchi⟩ := (admissibleSchur_centralCharacter ρ hρa hρi).exists
  exact ⟨chi.comp (Subgroup.inclusion hA), fun a x => hchi ⟨a, hA a.2⟩ x⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- `σ(gⁿ) ≤ σ(1) + n σ(g)` for a subadditive `σ`. -/
theorem le_add_nsmul_of_subadditive {σ : G → ℝ} (hσ : ∀ g h, σ (g * h) ≤ σ g + σ h) (g : G)
    (n : ℕ) : σ (g ^ n) ≤ σ 1 + n * σ g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Nat.cast_succ]
    linarith [hσ g (g ^ n)]

variable {Ξ σ : G → ℝ}

/-- **The central character of a tempered representation is unitary**: if `A` acts on a
nonzero smooth `ρ` with tempered coefficients through `c`, `Ξ` is positive and invariant under
`A` (`hΞ`) and `σ` is nonnegative and subadditive, then `‖c a‖ = 1`. -/
theorem norm_centralCharacter_eq_one [Nonempty (CompactOpenSubgroup G)] [Nontrivial V]
    (hρ : IsSmooth ρ) (hT : HasTemperedCoefficients Ξ σ ρ) {c : A →* ℂˣ}
    (hc : ∀ (a : A) (x : V), ρ a x = (c a : ℂ) • x) (hΞ0 : ∀ g, 0 < Ξ g)
    (hΞ : ∀ a ∈ A, ∀ g, Ξ (a * g) = Ξ g)
    (hσ0 : ∀ g, 0 ≤ σ g) (hσ : ∀ g h, σ (g * h) ≤ σ g + σ h) (a : A) :
    ‖(c a : ℂ)‖ = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : SmoothDual ρ, ℓ.val v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (ext_smoothDual hρ fun ℓ => by rw [h ℓ, map_zero])
  obtain ⟨C, r, hCr⟩ := hT v ℓ
  -- `‖c b‖ ≤ 1` for every `b ∈ A`
  have hle : ∀ b : A, ‖(c b : ℂ)‖ ≤ 1 := by
    intro b
    set B : ℝ := 1 + σ 1 + σ b
    have hB : 1 ≤ B := by linarith [hσ0 1, hσ0 b]
    refine le_one_of_pow_le (⌈|r|⌉₊)
      (D := |C| * Ξ 1 * B ^ |r| / ‖ℓ.val v‖) fun n => ?_
    have hval : ℓ.val (ρ ((b : G) ^ n) v) = (c b : ℂ) ^ n * ℓ.val v := by
      have h := hc (b ^ n) v
      rw [Subgroup.coe_pow] at h
      rw [h, map_smul, smul_eq_mul, map_pow, Units.val_pow_eq_pow_val]
    have hbound : ‖ℓ.val (ρ ((b : G) ^ n) v)‖ ≤
        C * Ξ ((b : G) ^ n) * (1 + σ ((b : G) ^ n)) ^ r := hCr ((b : G) ^ n)
    rw [hval, norm_mul, norm_pow] at hbound
    have hΞn : Ξ ((b : G) ^ n) = Ξ 1 := by
      have := hΞ ((b : G) ^ n) (A.pow_mem b.2 n) 1
      rwa [mul_one] at this
    have hσn : 1 + σ ((b : G) ^ n) ≤ B * (1 + n) := by
      have h1 := le_add_nsmul_of_subadditive hσ (b : G) n
      have h2 := hσ0 (b : G)
      have h3 := hσ0 1
      have hn : (0 : ℝ) ≤ n := n.cast_nonneg
      nlinarith
    have hpos : 0 < ‖ℓ.val v‖ := norm_pos_iff.2 hℓ
    set y : ℝ := 1 + σ ((b : G) ^ n) with hy
    have hy1 : 1 ≤ y := by linarith [hσ0 ((b : G) ^ n)]
    have hn1 : (1 : ℝ) ≤ 1 + n := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have hk : |r| ≤ (⌈|r|⌉₊ : ℝ) := Nat.le_ceil _
    have hyr : y ^ r ≤ B ^ |r| * (1 + n) ^ ⌈|r|⌉₊ := by
      calc y ^ r ≤ y ^ |r| := Real.rpow_le_rpow_of_exponent_le hy1 (le_abs_self r)
        _ ≤ (B * (1 + n)) ^ |r| := Real.rpow_le_rpow (by linarith) hσn (abs_nonneg r)
        _ = B ^ |r| * (1 + n) ^ |r| := Real.mul_rpow (by linarith) (by linarith)
        _ ≤ B ^ |r| * (1 + n) ^ (⌈|r|⌉₊ : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hk)
            (Real.rpow_nonneg (by linarith) _)
        _ = B ^ |r| * (1 + n) ^ ⌈|r|⌉₊ := by rw [Real.rpow_natCast]
    have hmain : ‖(c b : ℂ)‖ ^ n * ‖ℓ.val v‖ ≤
        |C| * Ξ 1 * (B ^ |r| * (1 + n) ^ ⌈|r|⌉₊) := by
      calc ‖(c b : ℂ)‖ ^ n * ‖ℓ.val v‖ ≤ C * Ξ ((b : G) ^ n) * y ^ r := hbound
        _ = C * Ξ 1 * y ^ r := by rw [hΞn]
        _ ≤ |C| * Ξ 1 * y ^ r :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (hΞ0 1).le)
            (Real.rpow_nonneg (by linarith) r)
        _ ≤ |C| * Ξ 1 * (B ^ |r| * (1 + n) ^ ⌈|r|⌉₊) :=
          mul_le_mul_of_nonneg_left hyr (mul_nonneg (abs_nonneg C) (hΞ0 1).le)
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    calc ‖(c b : ℂ)‖ ^ n * ‖ℓ.val v‖ ≤ |C| * Ξ 1 * (B ^ |r| * (1 + n) ^ ⌈|r|⌉₊) := hmain
      _ = |C| * Ξ 1 * B ^ |r| * (1 + n) ^ ⌈|r|⌉₊ := by ring
  have h1 := hle a
  have h2 := hle a⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖(c a : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have := (inv_le_one₀ hpos).1 h2
  linarith

end Character

section Twist

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- Every character of `G` with open kernel and absolute value `1` on `A` is unitary. -/
def IsUnitaryDetecting (A : Subgroup G) : Prop :=
  ∀ θ : G →* ℂˣ, IsOpen (θ.ker : Set G) → (∀ a : A, ‖(θ a : ℂ)‖ = 1) → ∀ g, ‖(θ g : ℂ)‖ = 1

omit [IsTopologicalGroup G] in
/-- `IsUnitaryDetecting A` holds when every character of `G` with open kernel has absolute
value `1` on `ker p` and `Λ / p(A)` is finite: for `g ∈ G`, some power `gⁿ` lies in
`A · ker p`. -/
theorem isUnitaryDetecting_of_norm_eq_one_on_ker (A : Subgroup G) {Λ : Type*} [CommGroup Λ]
    (p : G →* Λ) [Finite (Λ ⧸ A.map p)]
    (hker : ∀ θ : G →* ℂˣ, IsOpen (θ.ker : Set G) → ∀ k ∈ p.ker, ‖(θ k : ℂ)‖ = 1) :
    IsUnitaryDetecting A := by
  intro θ hθ hA1 g
  have hpow : ((p g : Λ) : Λ ⧸ A.map p) ^ Nat.card (Λ ⧸ A.map p) = 1 := pow_card_eq_one'
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hpow
  obtain ⟨a, ha, hpa⟩ := Subgroup.mem_map.1 hpow
  set n := Nat.card (Λ ⧸ A.map p)
  have hk : a⁻¹ * g ^ n ∈ p.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hpa, inv_mul_cancel]
  have h1 := hker θ hθ _ hk
  have h2 : ‖(θ a : ℂ)‖ = 1 := hA1 ⟨a, ha⟩
  have h3 : ‖(θ (g ^ n) : ℂ)‖ = 1 := by
    have hg : g ^ n = a * (a⁻¹ * g ^ n) := by group
    rw [hg, map_mul, Units.val_mul, norm_mul, h2, h1, one_mul]
  rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Nat.card_pos.ne').1 h3

/-- A nonzero smooth functional on the twist `ρ ⊗ χ'` of a smooth `ρ` forces `χ'` to be trivial
on an open subgroup: its kernel is open. -/
theorem isOpen_ker_of_smoothDual_ne_zero (hρ : IsSmooth ρ) (χ' : G →* ℂˣ)
    (ℓ : SmoothDual (twist χ' ρ)) (hℓ : ℓ ≠ 0) : IsOpen (χ'.ker : Set G) := by
  obtain ⟨v, hv⟩ : ∃ v, ℓ.val v ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (Subtype.ext (LinearMap.ext h))
  obtain ⟨K₁, hK₁⟩ := hρ v
  have hℓs : IsSmoothVector (twist χ' ρ).dual ℓ.val := ℓ.property
  obtain ⟨K₂, hK₂⟩ := hℓs
  refine Subgroup.isOpen_mono (H₁ := K₁.toSubgroup ⊓ K₂.toSubgroup) ?_
    (by rw [Subgroup.coe_inf]; exact K₁.isOpen.inter K₂.isOpen)
  intro k hk
  have h1 : ((twist χ' ρ).dual k ℓ.val) v = ℓ.val v :=
    congrArg (fun f : Module.Dual ℂ V => f v) (hK₂ ⟨k, hk.2⟩)
  have h2 : ρ k⁻¹ v = v := hK₁ ⟨k⁻¹, K₁.toSubgroup.inv_mem hk.1⟩
  change ℓ.val ((χ' k⁻¹ : ℂ) • ρ k⁻¹ v) = ℓ.val v at h1
  rw [h2, map_smul, smul_eq_mul] at h1
  have h3 : (χ' k⁻¹ : ℂ) = 1 := mul_right_cancel₀ hv (h1.trans (one_mul _).symm)
  have h4 : χ' k⁻¹ = 1 := Units.ext h3
  rw [map_inv, inv_eq_one] at h4
  exact h4

end Twist

section Integrability

universe u v w

open scoped ENNReal

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
  {Λ : Type*} [CommGroup Λ] (p : G →* Λ)
  {A : Subgroup G} [A.Normal] [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  {ν : Measure (G ⧸ A)} [ν.IsMulLeftInvariant] {m : ℝ≥0∞}

/-- A continuous function on `G / A` is integrable if its pullback is integrable on every fibre
of `p`, when `Λ / p(A)` is finite: `G / A` is the union of the finitely many images of the
fibres over representatives of `Λ / p(A)`. -/
theorem integrable_of_integrableOn_preimage [Finite (Λ ⧸ A.map p)]
    (hp : Function.Surjective p)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hm0 : m ≠ 0) (hm : m ≠ ∞) {H : G ⧸ A → ℂ} (hH : Continuous H)
    (h : ∀ g : G, IntegrableOn (fun x : G => H (x : G ⧸ A)) (p ⁻¹' {p g}) μ) :
    Integrable H ν := by
  have hsurj : ∀ q : Λ ⧸ A.map p, ∃ g : G, ((p g : Λ) : Λ ⧸ A.map p) = q := fun q => by
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, rfl⟩ := hp l
    exact ⟨g, rfl⟩
  choose g hg using hsurj
  let T : Λ ⧸ A.map p → Set (G ⧸ A) := fun q =>
    (QuotientGroup.mk : G → G ⧸ A) '' (p ⁻¹' {p (g q)})
  have hU : (⋃ q, T q) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    induction y using QuotientGroup.induction_on with
    | H x =>
      set q : Λ ⧸ A.map p := ((p x : Λ) : Λ ⧸ A.map p)
      have hq : ((p x : Λ) : Λ ⧸ A.map p) = ((p (g q) : Λ) : Λ ⧸ A.map p) := by rw [hg q]
      obtain ⟨a, ha, hpa⟩ := Subgroup.mem_map.1 (QuotientGroup.eq.1 hq)
      refine Set.mem_iUnion.2 ⟨q, x * a, ?_, ?_⟩
      · simp only [Set.mem_preimage, Set.mem_singleton_iff, map_mul, hpa, mul_inv_cancel_left]
      · exact QuotientGroup.eq.2 (by simpa using ha)
  have hT : ∀ q, IntegrableOn H (T q) ν := by
    intro q
    have hint : Integrable H (Measure.map (QuotientGroup.mk : G → G ⧸ A)
        (μ.restrict (p ⁻¹' {p (g q)}))) :=
      (integrable_map_measure hH.aestronglyMeasurable measurable_quotientMk.aemeasurable).2
        (h (g q))
    rw [map_mk_restrict_preimage p hcompat (g q)] at hint
    have h' := hint.smul_measure (ENNReal.inv_ne_top.2 hm0)
    rwa [smul_smul, ENNReal.inv_mul_cancel hm0 hm, one_smul] at h'
  have hU' : IntegrableOn H (⋃ q, T q) ν := integrableOn_finite_iUnion.2 hT
  rwa [hU, integrableOn_univ] at hU'

variable {Ξ σ : G → ℝ}
  {V : Type v} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {W : Type w} [AddCommGroup W] [Module ℂ W] {ω : Representation ℂ G W} {cω : A →* ℂˣ}
  (hω : ∀ (a : A) (x : W), ω a x = (cω a : ℂ) • x)

include hω in
/-- **The extension of Waldspurger III.1 (2) to tempered representations, for unitary twists**:
for `π` smooth with tempered coefficients, a unitary character `χ'` with open kernel such that
`π ⊗ χ'` and `ω` have the same central character on `A`, and `ω` smooth with coefficients
rapidly decreasing on `ker p`, the integrand `gA ↦ ⟨(π ⊗ χ')(g) v₁, ℓ₁⟩ ⟨ω(g⁻¹) v₂, ℓ₂⟩` is
integrable on `G / A`. -/
theorem integrable_orthogonalityIntegrand_of_tempered [Finite (Λ ⧸ A.map p)]
    (hp : Function.Surjective p)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hm0 : m ≠ 0) (hm : m ≠ ∞) (hN : IsOpen (p.ker : Set G))
    (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ) (hωs : IsSmooth ω)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (hπs : IsSmooth π) (hT : HasTemperedCoefficients Ξ σ π) {χ' : G →* ℂˣ}
    (hχo : IsOpen (χ'.ker : Set G)) (hχu : ∀ g, ‖(χ' g : ℂ)‖ = 1)
    (hχ' : ∀ (a : A) (x : V), twist χ' π a x = (cω a : ℂ) • x)
    (v₁ : V) (ℓ₁ : SmoothDual (twist χ' π)) (v₂ : W) (ℓ₂ : SmoothDual ω) :
    Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν := by
  set F : G → ℂ := fun g => ℓ₁.val (twist χ' π g v₁) * ℓ₂.val (ω g⁻¹ v₂) with hF
  have hπ's : IsSmooth (twist χ' π) := (isSmooth_twist_iff χ' π hχo).2 hπs
  have hFc : Continuous F := (continuous_coefficient hπ's v₁ ℓ₁).mul
    ((continuous_coefficient hωs v₂ ℓ₂).comp continuous_inv)
  have hHc : Continuous (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) :=
    (QuotientGroup.isQuotientMap_mk A).continuous_iff.2 hFc
  refine integrable_of_integrableOn_preimage p hp hcompat hm0 hm hHc fun g => ?_
  have hpre : (g * ·) ⁻¹' (p ⁻¹' {p g}) = (p.ker : Set G) := by
    ext x
    simp
  rw [← (measurePreserving_mul_left μ g).integrableOn_comp_preimage
    (measurableEmbedding_mulLeft g), hpre]
  -- the constants
  let ℓ₁' : SmoothDual π := (smoothContragredientTwistEquiv χ' π hχo).toLinearEquiv ℓ₁
  obtain ⟨C₁, r₁, h₁⟩ := hT v₁ ℓ₁'
  obtain ⟨dt, hdt⟩ := ht.bound
  obtain ⟨Ct, hCt⟩ := hdt g 1
  obtain ⟨Ch, hCh⟩ := ht.heightBound g 1
  obtain ⟨d₀, hd₀⟩ := hw.square
  set r₂ : ℝ := |r₁| + dt + d₀ with hr₂
  let ev : SmoothDual (smoothContragredient ω) := smoothBidual hωs (ω g⁻¹ v₂)
  obtain ⟨C₂, h₂⟩ := hD ℓ₂ ev r₂
  set K₀ : ℝ := |C₁| * |Ct| * |Ch| ^ |r₁| * |C₂| with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  -- the pointwise bound on `ker p`
  have hbound : ∀ k ∈ (p.ker : Set G),
      ‖F (g * k)‖ ≤ K₀ * (Ξ k ^ 2 * (1 + σ k) ^ (-d₀)) := by
    intro k hk
    have hs : 0 < 1 + σ k := by linarith [ht.nonneg k]
    have hs1 : 1 ≤ 1 + σ k := by linarith [ht.nonneg k]
    have hgs1 : 1 ≤ 1 + σ (g * k) := by linarith [ht.nonneg (g * k)]
    have hΞk : 0 < Ξ k := ht.pos k
    -- first factor
    have e1 : ‖ℓ₁.val (twist χ' π (g * k) v₁)‖ = ‖ℓ₁'.val (π (g * k) v₁)‖ := by
      change ‖ℓ₁.val ((χ' (g * k) : ℂ) • π (g * k) v₁)‖ = ‖ℓ₁.val (π (g * k) v₁)‖
      rw [map_smul, smul_eq_mul, norm_mul, hχu, one_mul]
    have b1 : ‖ℓ₁'.val (π (g * k) v₁)‖ ≤ |C₁| * Ξ (g * k) * (1 + σ (g * k)) ^ |r₁| := by
      have h := h₁ (g * k)
      change ‖ℓ₁'.val (π (g * k) v₁)‖ ≤ C₁ * Ξ (g * k) * (1 + σ (g * k)) ^ r₁ at h
      refine h.trans ?_
      have hΞg := ht.pos (g * k)
      calc C₁ * Ξ (g * k) * (1 + σ (g * k)) ^ r₁
          ≤ |C₁| * Ξ (g * k) * (1 + σ (g * k)) ^ r₁ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C₁) hΞg.le)
              (Real.rpow_nonneg (by linarith) _)
        _ ≤ |C₁| * Ξ (g * k) * (1 + σ (g * k)) ^ |r₁| :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hgs1 (le_abs_self r₁))
              (mul_nonneg (abs_nonneg _) hΞg.le)
    have bΞ : Ξ (g * k) ≤ |Ct| * Ξ k * (1 + σ k) ^ dt := by
      have h := hCt k
      rw [mul_one] at h
      refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Ct)
        hΞk.le) (pow_nonneg hs.le _))
    have bσ : (1 + σ (g * k)) ^ |r₁| ≤ |Ch| ^ |r₁| * (1 + σ k) ^ |r₁| := by
      have h := hCh k
      rw [mul_one] at h
      rw [← Real.mul_rpow (abs_nonneg _) hs.le]
      exact Real.rpow_le_rpow (by linarith) (h.trans (mul_le_mul_of_nonneg_right
        (le_abs_self Ch) hs.le)) (abs_nonneg _)
    -- second factor
    have e2 : ℓ₂.val (ω (g * k)⁻¹ v₂) =
        ev.val ((contragredientRep ω).representation k ℓ₂) := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply]
      rfl
    have b2 : ‖ℓ₂.val (ω (g * k)⁻¹ v₂)‖ ≤ |C₂| * Ξ k * (1 + σ k) ^ (-r₂) := by
      rw [e2]
      exact (h₂ k hk).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (le_abs_self C₂) hΞk.le) (Real.rpow_nonneg hs.le _))
    -- combine
    have hexp : (1 + σ k) ^ dt * (1 + σ k) ^ |r₁| * (1 + σ k) ^ (-r₂) = (1 + σ k) ^ (-d₀) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hs, ← Real.rpow_add hs, hr₂]
      congr 1
      ring
    have hA1 : 0 ≤ ‖ℓ₁'.val (π (g * k) v₁)‖ := norm_nonneg _
    calc ‖F (g * k)‖ = ‖ℓ₁'.val (π (g * k) v₁)‖ * ‖ℓ₂.val (ω (g * k)⁻¹ v₂)‖ := by
          rw [hF, norm_mul, e1]
      _ ≤ (|C₁| * (|Ct| * Ξ k * (1 + σ k) ^ dt) * (|Ch| ^ |r₁| * (1 + σ k) ^ |r₁|)) *
            (|C₂| * Ξ k * (1 + σ k) ^ (-r₂)) := by
          refine mul_le_mul ?_ b2 (norm_nonneg _) ?_
          · refine b1.trans ?_
            exact mul_le_mul (mul_le_mul_of_nonneg_left bΞ (abs_nonneg _)) bσ
              (Real.rpow_nonneg (by linarith) _)
              (mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (abs_nonneg _) hΞk.le)
                (pow_nonneg hs.le _)))
          · exact mul_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg
              (abs_nonneg _) hΞk.le) (pow_nonneg hs.le _))) (mul_nonneg (Real.rpow_nonneg
              (abs_nonneg _) _) (Real.rpow_nonneg hs.le _))
      _ = K₀ * (Ξ k ^ 2 * ((1 + σ k) ^ dt * (1 + σ k) ^ |r₁| * (1 + σ k) ^ (-r₂))) := by
          rw [hK₀]
          ring
      _ = K₀ * (Ξ k ^ 2 * (1 + σ k) ^ (-d₀)) := by rw [hexp]
  -- integrability
  refine ⟨(hFc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable, ?_⟩
  have hNm : MeasurableSet (p.ker : Set G) := hN.measurableSet
  calc ∫⁻ k in (p.ker : Set G), ‖F (g * k)‖ₑ ∂μ
      ≤ ∫⁻ k in (p.ker : Set G), ENNReal.ofReal (K₀ * (Ξ k ^ 2 * (1 + σ k) ^ (-d₀))) ∂μ := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem hNm fun k hk => ?_)
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hbound k hk)
    _ ≤ ∫⁻ k, ENNReal.ofReal (K₀ * (Ξ k ^ 2 * (1 + σ k) ^ (-d₀))) ∂μ :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal K₀ * ∫⁻ k, ENNReal.ofReal (Ξ k ^ 2 * (1 + σ k) ^ (-d₀)) ∂μ := by
        simp_rw [ENNReal.ofReal_mul hK₀0]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hd₀

include hω in
/-- **The hypothesis `hint` of `TraceFamilyScalar` for a tempered representation**: if `π` is
smooth with tempered coefficients and `A` acts on `π` through a unitary character `cπ`, `cω` is
unitary, and every character of `G` with open kernel and absolute value `1` on `A` is unitary
(`hunit`), then for every character `χ'` with `π ⊗ χ'` acting on `A` through `cω` the integrand
of `π ⊗ χ'` against `ω` is integrable on `G / A`. A nonzero smooth functional on `π ⊗ χ'`
forces `χ'` to have open kernel (`isOpen_ker_of_smoothDual_ne_zero`); the zero functional gives
the zero integrand. -/
theorem hint_of_tempered [Finite (Λ ⧸ A.map p)] (hp : Function.Surjective p)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hm0 : m ≠ 0) (hm : m ≠ ∞) (hN : IsOpen (p.ker : Set G))
    (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ) (hωs : IsSmooth ω)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (hωu : ∀ a : A, ‖(cω a : ℂ)‖ = 1)
    (hunit : IsUnitaryDetecting A)
    (hπs : IsSmooth π) (hT : HasTemperedCoefficients Ξ σ π) {cπ : A →* ℂˣ}
    (hπc : ∀ (a : A) (x : V), π a x = (cπ a : ℂ) • x) (hπu : ∀ a : A, ‖(cπ a : ℂ)‖ = 1) :
    ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V), twist χ' π a x = (cω a : ℂ) • x)
      (v₁ : V) (ℓ₁ : SmoothDual (twist χ' π)) (v₂ : W) (ℓ₂ : SmoothDual ω),
        Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν := by
  intro χ' hχ' v₁ ℓ₁ v₂ ℓ₂
  by_cases hℓ : ℓ₁ = 0
  · have h0 : orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val = 0 := by
      funext q
      induction q using QuotientGroup.induction_on with
      | H x =>
        rw [orthogonalityIntegrand_mk, hℓ]
        simp
    rw [h0]
    exact integrable_zero _ _ _
  have hχo := isOpen_ker_of_smoothDual_ne_zero hπs χ' ℓ₁ hℓ
  have hVnt : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact hℓ (Subtype.ext (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero,
      map_zero]))
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hA1 : ∀ a : A, ‖(χ' a : ℂ)‖ = 1 := by
    intro a
    have h1 := hχ' a x
    change (χ' a : ℂ) • π a x = _ at h1
    rw [hπc, smul_smul] at h1
    have h2 : (χ' a : ℂ) * cπ a = cω a := smul_left_injective ℂ hx h1
    have h3 := congrArg norm h2
    rw [norm_mul, hπu, hωu, mul_one] at h3
    exact h3
  exact integrable_orthogonalityIntegrand_of_tempered p hω hp hcompat hm0 hm hN ht hw hωs hD hπs
    hT hχo (hunit χ' hχo hA1) hχ' v₁ ℓ₁ v₂ ℓ₂

end Integrability

section Corollaries

universe u v w

open scoped ENNReal

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Nonempty (CompactOpenSubgroup G)] {Ξ σ : G → ℝ}
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {μ : Measure G} [μ.IsHaarMeasure] [SFinite μ] [μ.IsMulRightInvariant]
  {K : Subgroup G} [CompactSpace K]
  {Λ : Type*} [CommGroup Λ] (p : G →* Λ)
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (ν : Measure (G ⧸ A)) [ν.IsHaarMeasure] [ν.IsInvInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
  {W : Type v} [AddCommGroup W] [Module ℂ W] {ω : Representation ℂ G W}
  {cω : A →* ℂˣ} (hω : ∀ (a : A) (x : W), ω a x = (cω a : ℂ) • x)
  (hsq : IsSquareIntegrableModCentralSubgroup A hA ω ν) (hiω : ω.IsIrreducible)
  [Fintype (Λ ⧸ A.map p)]
  {V : Type w} [AddCommGroup V] [Module ℂ V]

omit [SecondCountableTopology G] [SFinite μ] [μ.IsMulRightInvariant] [ν.IsInvInvariant] in
include hcof hsq hiω in
/-- **The hypothesis `hsub` of Corollary III.7.2 from temperedness**: every irreducible
subquotient `π'` of an admissible `π` with tempered coefficients has a character of `A` by which
`A` acts, this character is unitary, and `π'` satisfies the hypothesis `hint` of
`TraceFamilyScalar`. -/
theorem hsub_of_tempered (hp : Function.Surjective p) (hN : IsOpen (p.ker : Set G))
    {m : ℝ≥0∞} (hm : m ≠ ∞) (hm0 : m ≠ 0)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (hΞA : ∀ a ∈ A, ∀ g, Ξ (a * g) = Ξ g)
    (hσ : ∀ g h, σ (g * h) ≤ σ g + σ h) (hunit : IsUnitaryDetecting A)
    {π : Representation ℂ G V} (hπa : IsAdmissible π) (hT : HasTemperedCoefficients Ξ σ π) :
      ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      ∃ cπ' : A →* ℂˣ, (∀ (a : A) (x : V'), π' a x = (cπ' a : ℂ) • x) ∧
        (∀ a : A, ‖(cπ' a : ℂ)‖ = 1) ∧
        ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V'), twist χ' π' a x = (cω a : ℂ) • x)
          (v₁ : V') (ℓ₁ : SmoothDual (twist χ' π')) (v₂ : W) (ℓ₂ : SmoothDual ω),
            Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν := by
  intro X _ _ τ i hi V' _ _ π' q hq hiπ'
  have hτa : IsAdmissible τ := isAdmissible_of_injective i hi hπa
  have hτT := hasTemperedCoefficients_of_injective hcof hτa.1 hπa.1 i hi hT
  have hπ'a : IsAdmissible π' :=
    Langlands.Unramified.SphericalExistence.isAdmissible_of_surjective hcof q hq hτa
  have hπ'T := hasTemperedCoefficients_of_surjective q hq hτT
  obtain ⟨c, hc⟩ := exists_centralCharacter_of_isIrreducible A hA hπ'a hiπ'
  have hV' : Nontrivial V' := by
    have := hiπ'
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π'.asModule
  have hcu : ∀ a : A, ‖(c a : ℂ)‖ = 1 :=
    norm_centralCharacter_eq_one A hπ'a.1 hπ'T hc ht.pos hΞA ht.nonneg hσ
  exact ⟨c, hc, hcu, hint_of_tempered p hω hp hcompat hm0 hm hN ht hw hsq.1.1 hD
    (norm_character_eq_one A hA ν hω hsq hiω) hunit hπ'a.1 hπ'T hc hcu⟩

include hcof hω hsq hiω in
/-- **Corollary III.7.2 for tempered representations**: for an admissible `π` with tempered
coefficients there is a unique decomposition `V = V₁ ⊕ V₂` into subrepresentations such that
(i) every irreducible subquotient of `V₁` is equivalent to `ω` and (ii) no irreducible
subquotient of `V₂` is equivalent to `ω`, under the hypotheses on the weights and on the
characters of `G` listed (`hΞA`, `hσ`, `hunit`) in place of `hsub`. -/
theorem existsUnique_orbitIsotypic_decomposition_of_tempered (hp : Function.Surjective p)
    (hN : IsOpen (p.ker : Set G)) (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    {m : ℝ≥0∞} (hm : m ≠ ∞) (hm0 : m ≠ 0)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (hΞA : ∀ a ∈ A, ∀ g, Ξ (a * g) = Ξ g)
    (hσ : ∀ g h, σ (g * h) ≤ σ g + σ h) (hunit : IsUnitaryDetecting A)
    {π : Representation ℂ G V} (hπa : IsAdmissible π) (hT : HasTemperedCoefficients Ξ σ π) :
    ∃ V₁ V₂ : Subrepresentation π, IsCompl V₁.toSubmodule V₂.toSubmodule ∧
      (∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₁) →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      Nonempty (π'.Equiv ω)) ∧
      (∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₂) →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      IsEmpty (π'.Equiv ω)) ∧
      ∀ V₁' V₂' : Subrepresentation π, IsCompl V₁'.toSubmodule V₂'.toSubmodule →
        (∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₁') →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      Nonempty (π'.Equiv ω)) →
        (∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₂') →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      IsEmpty (π'.Equiv ω)) →
        V₁' = V₁ ∧ V₂' = V₂ :=
  existsUnique_orbitIsotypic_decomposition p A hA ν hcof hω hsq hiω hp hN hHN hm hm0 hcompat hc
    ht hw hD hπa hT (hsub_of_tempered p A hA ν hcof hω hsq hiω hp hN hm hm0 hcompat ht hw hD hΞA
      hσ hunit hπa hT)

include hcof hsq hiω in
/-- **Proposition III.7.1 (iii) for tempered representations**: `orbitPolynomialOperator_eq_smul_of_equiv`
without the hypothesis `hint`, which follows from temperedness when every character of `G` with
open kernel and absolute value `1` on `A` is unitary (`hunit`). -/
theorem orbitPolynomialOperator_eq_smul_of_equiv_of_tempered (hp : Function.Surjective p)
    (hN : IsOpen (p.ker : Set G)) (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    {m : ℝ≥0∞} (hm : m ≠ ∞) (hm0 : m ≠ 0)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (hunit : IsUnitaryDetecting A) (b : Λ →₀ ℂ)
    (hb : ∀ χ χ' : Λ →* ℂˣ, (∀ l, ‖(χ l : ℂ)‖ = 1) → (∀ l, ‖(χ' l : ℂ)‖ = 1) →
      Nonempty ((twist (χ.comp p) ω).Equiv (twist (χ'.comp p) ω)) →
        finsuppCharacterSum b χ = finsuppCharacterSum b χ')
    {π : Representation ℂ G V} (hπa : IsAdmissible π) (hiπ : π.IsIrreducible)
    (hT : HasTemperedCoefficients Ξ σ π)
    (χ₁ : Λ →* ℂˣ) (hχ₁ : ∀ l, ‖(χ₁ l : ℂ)‖ = 1) (e : π.Equiv (twist (χ₁.comp p) ω)) (v : V) :
    orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hT v = finsuppCharacterSum b χ₁ • v := by
  let cπ : A →* ℂˣ := χ₁.comp (p.comp A.subtype) * cω
  have hπc : ∀ (a : A) (x : V), π a x = (cπ a : ℂ) • x := by
    intro a x
    have h := congrArg (fun T => T (e x)) (e.symm.isIntertwining' (a : G))
    simp only [LinearMap.comp_apply] at h
    change e.symm (twist (χ₁.comp p) ω a (e x)) = π a (e.symm (e x)) at h
    rw [e.symm_apply_apply] at h
    rw [← h]
    change e.symm ((((χ₁.comp p) a : ℂˣ) : ℂ) • ω a (e x)) = _
    rw [hω, smul_smul, map_smul, e.symm_apply_apply]
    simp [cπ]
  have hωu := norm_character_eq_one A hA ν hω hsq hiω
  have hπu : ∀ a : A, ‖(cπ a : ℂ)‖ = 1 := by
    intro a
    change ‖((χ₁ (p a) * cω a : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, hχ₁, hωu, one_mul]
  exact orbitPolynomialOperator_eq_smul_of_equiv p A hA ν hcof hω hsq hiω hp hN hHN hm hm0 hcompat
    hc ht hw hD b hb hπa hiπ hT (hint_of_tempered p hω hp hcompat hm0 hm hN ht hw hsq.1.1 hD hωu
      hunit hπa.1 hT hπc hπu) χ₁ hχ₁ e v

include hcof hsq hiω in
/-- **Proposition III.7.1 (ii) for tempered representations**: `orbitPolynomialOperator_eq_zero`
without the hypotheses on the central character of `π` and `hint`, which follow from
temperedness under `hΞA`, `hσ` and `hunit`. -/
theorem orbitPolynomialOperator_eq_zero_of_tempered (hp : Function.Surjective p)
    (hN : IsOpen (p.ker : Set G)) (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    {m : ℝ≥0∞} (hm : m ≠ ∞) (hm0 : m ≠ 0)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (hΞA : ∀ a ∈ A, ∀ g, Ξ (a * g) = Ξ g)
    (hσ : ∀ g h, σ (g * h) ≤ σ g + σ h) (hunit : IsUnitaryDetecting A) (b : Λ →₀ ℂ)
    {π : Representation ℂ G V} (hπa : IsAdmissible π) (hiπ : π.IsIrreducible)
    (hT : HasTemperedCoefficients Ξ σ π)
    (hnot : ∀ χ : Λ →* ℂˣ, (∀ l, ‖(χ l : ℂ)‖ = 1) → IsEmpty (π.Equiv (twist (χ.comp p) ω)))
    (v : V) :
    orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hT v = 0 := by
  obtain ⟨cπ, hπc⟩ := exists_centralCharacter_of_isIrreducible A hA hπa hiπ
  have hV : Nontrivial V := by
    have := hiπ
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  have hπu : ∀ a : A, ‖(cπ a : ℂ)‖ = 1 :=
    norm_centralCharacter_eq_one A hπa.1 hT hπc ht.pos hΞA ht.nonneg hσ
  exact orbitPolynomialOperator_eq_zero p A hA ν hcof hω hsq hiω hp hN hHN hm hcompat hc ht hw hD b
    hπa hiπ hT hπc hπu (hint_of_tempered p hω hp hcompat hm0 hm hN ht hw hsq.1.1 hD
      (norm_character_eq_one A hA ν hω hsq hiω) hunit hπa.1 hT hπc hπu) hnot v

end Corollaries

end Langlands.HarishChandraSchwartz
