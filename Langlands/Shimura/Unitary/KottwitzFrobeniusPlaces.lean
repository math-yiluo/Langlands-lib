import Langlands.Shimura.Unitary.KottwitzLiftIndependence

/-!
# Frobenius and the places above `p` of a CM field

For `θ : ℂ →+* Q̄_p`, the place `harrisPlace p θ i` of a complex embedding `i` of `K`
is unchanged by the geometric Frobenius permutation `frobeniusPerm K p θ`, and complex
conjugation of embeddings corresponds to conjugation of places. Consequently the
embedding coordinates `embeddingCochar θ Φ` of the `ℚ_p`-rational cocharacters are
injective. See the paired Markdown.
-/

noncomputable section

open NumberField IsDedekindDomain

namespace Langlands.Shimura.KottwitzDual

open KottwitzUnramified Langlands.Global.AdelicFunctoriality

universe u v

section Valuation

variable (p : ℕ) [Fact p.Prime]

/-- `ℚ_p`-automorphisms of `Q̄_p` preserve its valuation (the spectral norm). -/
theorem padicAlgCl_valuation_algEquiv (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (y : PadicAlgCl p) : (PadicAlgCl.valued p).v (σ y) = (PadicAlgCl.valued p).v y := by
  rw [PadicAlgCl.valuation_def, PadicAlgCl.valuation_def]
  ext
  simp only [coe_nnnorm]
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ y).symm

end Valuation

section Frobenius

variable {K : Type v} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (θ : ℂ →+* PadicAlgCl p)

/-- The geometric Frobenius permutation preserves the prime of an embedding. -/
theorem harrisPrime_frobeniusPerm (i : K →+* ℂ) :
    harrisPrime p θ (frobeniusPerm K p θ i) = harrisPrime p θ i := by
  apply HeightOneSpectrum.ext
  ext x
  rw [harrisPrime_asIdeal, harrisPrime_asIdeal, mem_embeddingIdeal, mem_embeddingIdeal,
    harrisValuation_apply, harrisValuation_apply, theta_frobeniusPerm_apply,
    padicAlgCl_valuation_algEquiv]

/-- The geometric Frobenius permutation preserves the place of an embedding. -/
theorem harrisPlace_frobeniusPerm (i : K →+* ℂ) :
    harrisPlace p θ (frobeniusPerm K p θ i) = harrisPlace p θ i :=
  Subtype.ext (harrisPrime_frobeniusPerm p θ i)

theorem harrisPlace_frobeniusPerm_pow (r : ℕ) (i : K →+* ℂ) :
    harrisPlace p θ ((frobeniusPerm K p θ ^ r) i) = harrisPlace p θ i := by
  induction r with
  | zero => rfl
  | succ r ih => rw [pow_succ', Equiv.Perm.mul_apply, harrisPlace_frobeniusPerm, ih]

/-- Every place of `K` above `p` is the place of some complex embedding. -/
theorem harrisPlace_surjective :
    Function.Surjective (harrisPlace p θ (F := K)) := by
  intro w
  have hw : w.1 ∈ Set.range (harrisPrime p θ (K := K)) := by
    rw [range_harrisPrime]
    exact (liesOver_rationalPrimePlace_iff p w.1).mp w.2
  obtain ⟨i, hi⟩ := hw
  exact ⟨i, Subtype.ext hi⟩

variable (K) in
/-- The Frobenius orbits on the complex embeddings of `K` are the fibres of the place map,
and the orbit of `i` has exactly `f_w` elements, where `f_w` is the inertia degree of
the place `w` of `i`: the minimal period of `i` under the geometric Frobenius
permutation is `f_w`, and the embeddings with the same place as `i` are the
`Frob^r ∘ i`. -/
def FrobeniusOrbitsArePlaces : Prop :=
  ∀ i : K →+* ℂ,
    Function.minimalPeriod (frobeniusPerm K p θ) i =
        KottwitzUnramified.inertiaDegree (harrisPlace p θ i) ∧
      ∀ j : K →+* ℂ, harrisPlace p θ j = harrisPlace p θ i ↔
        ∃ r : ℕ, (frobeniusPerm K p θ ^ r) i = j

open scoped Classical in
/-- The fibre of the place map over a place `w ∣ p`: the complex embeddings `i` of `K`
for which `θ ∘ i` induces `w`. -/
def harrisPlaceFibre (w : FinitePlacesAbove K (rationalPrimePlace p)) : Finset (K →+* ℂ) :=
  Finset.univ.filter fun i => harrisPlace p θ i = w

@[simp] theorem mem_harrisPlaceFibre (w : FinitePlacesAbove K (rationalPrimePlace p))
    (i : K →+* ℂ) : i ∈ harrisPlaceFibre p θ w ↔ harrisPlace p θ i = w := by
  classical
  simp [harrisPlaceFibre]

theorem harrisPlaceFibre_nonempty (w : FinitePlacesAbove K (rationalPrimePlace p)) :
    (harrisPlaceFibre p θ w).Nonempty := by
  obtain ⟨i, hi⟩ := harrisPlace_surjective p θ w
  exact ⟨i, (mem_harrisPlaceFibre p θ w i).mpr hi⟩

/-- The fibres of the place map are stable under the Frobenius permutation. -/
theorem frobeniusPerm_pow_mem_harrisPlaceFibre (r : ℕ)
    (w : FinitePlacesAbove K (rationalPrimePlace p)) (i : K →+* ℂ) :
    (frobeniusPerm K p θ ^ r) i ∈ harrisPlaceFibre p θ w ↔ i ∈ harrisPlaceFibre p θ w := by
  rw [mem_harrisPlaceFibre, mem_harrisPlaceFibre, harrisPlace_frobeniusPerm_pow]

/-- The fibres of the place map partition the complex embeddings: their sizes add up
to `[K : ℚ]`. -/
theorem sum_card_harrisPlaceFibre :
    ∑ w : FinitePlacesAbove K (rationalPrimePlace p), (harrisPlaceFibre p θ w).card =
      Module.finrank ℚ K := by
  classical
  rw [← NumberField.Embeddings.card K ℂ, ← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := harrisPlace p θ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun w _ => congrArg Finset.card ?_
  ext i
  simp [mem_harrisPlaceFibre]

end Frobenius

section Extension

variable {S : Type*} {n : ℕ}

/-- The free coordinates `(a₀, (a_{τ,k}))` of a cocharacter, extended to all CM indices:
`(τ, true) ↦ a_{τ,k}` and `(τ, false) ↦ a₀ - a_{τ, rev k}`. -/
def cocharExtend (a : ℤ × (S → Fin n → ℤ)) (x : S × Bool) (k : Fin n) : ℤ :=
  if x.2 then a.2 x.1 k else a.1 - a.2 x.1 (Fin.rev k)

theorem cocharExtend_cmSwap (a : ℤ × (S → Fin n → ℤ)) (x : S × Bool) (k : Fin n) :
    cocharExtend a (cmSwap S x) k = a.1 - cocharExtend a x (Fin.rev k) := by
  rcases x with ⟨τ, b⟩
  cases b <;> simp [cocharExtend, Fin.rev_rev]

/-- A cocharacter fixed by `G^*` has `G`-invariant extended coordinates. -/
theorem cocharExtend_apply_of_cocharPullback_eq {G : CMPerm S} {a : ℤ × (S → Fin n → ℤ)}
    (h : cocharPullback n G a = a) (x : S × Bool) (k : Fin n) :
    cocharExtend a ((G : Equiv.Perm (S × Bool)) x) k = cocharExtend a x k := by
  have key : ∀ τ k, cocharExtend a ((G : Equiv.Perm (S × Bool)) (τ, true)) k = a.2 τ k := by
    intro τ k
    have hτ := congrFun (congrFun (congrArg Prod.snd h) τ) k
    simp only [cocharPullback_apply] at hτ
    refine Eq.trans ?_ hτ
    rw [CMPerm.apply_eq G τ true]
    simp only [cocharExtend, CMPerm.base_apply, CMPerm.baseFun]
    generalize CMPerm.crosses G τ = c
    cases c <;> simp
  rcases x with ⟨τ, b⟩
  cases b
  · have hs : ((τ, false) : S × Bool) = cmSwap S (τ, true) := rfl
    rw [hs, CMPerm.apply_cmSwap, cocharExtend_cmSwap, cocharExtend_cmSwap, key]
    simp [cocharExtend]
  · rw [key]
    simp [cocharExtend]

end Extension

section Conjugation

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [Algebra.IsQuadraticExtension E K]
  (p : ℕ) [Fact p.Prime] (θ : ℂ →+* PadicAlgCl p)

variable (E) in
omit [NumberField E] in
/-- The place of the conjugate embedding is the conjugate place. -/
theorem harrisPlace_conjugate (i : K →+* ℂ) :
    harrisPlace p θ (ComplexEmbedding.conjugate i) =
      placeConj (E := E) (rationalPrimePlace p) (harrisPlace p θ i) := by
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  ext x
  rw [mem_placeConj, harrisPlace_val, harrisPlace_val, harrisPrime_asIdeal, harrisPrime_asIdeal,
    mem_embeddingIdeal, mem_embeddingIdeal, conjugate_apply (E := E)]
  rfl

variable (E) in
omit [NumberField E] in
/-- Conjugation of embeddings maps the fibre over `w` onto the fibre over `w̄`. -/
theorem conjugate_mem_harrisPlaceFibre (w : FinitePlacesAbove K (rationalPrimePlace p))
    (i : K →+* ℂ) :
    ComplexEmbedding.conjugate i ∈
        harrisPlaceFibre p θ (placeConj (E := E) (rationalPrimePlace p) w) ↔
      i ∈ harrisPlaceFibre p θ w := by
  rw [mem_harrisPlaceFibre, mem_harrisPlaceFibre, harrisPlace_conjugate E]
  constructor
  · intro h
    have h' := congrArg (placeConj (E := E) (rationalPrimePlace p)) h
    rwa [placeConj_placeConj, placeConj_placeConj] at h'
  · intro h
    rw [h]

/-- The embedding coordinates of `ℚ_p`-rational cocharacters determine the cocharacter. -/
theorem embeddingCochar_injective {Φ : (E →+* ℝ) → (K →+* ℂ)} (hΦ : IsCMSection E K Φ)
    (n : ℕ) :
    Function.Injective (embeddingCochar (n := n) (p := p) (E := E) (K := K) θ Φ) := by
  intro m m' h
  have h1 : m.1.2 = m'.1.2 := congrArg Prod.fst h
  have h2 : ∀ τ k, m.1.1 (harrisPlace p θ (Φ τ)) k = m'.1.1 (harrisPlace p θ (Φ τ)) k :=
    fun τ k => congrFun (congrFun (congrArg Prod.snd h) τ) k
  apply Subtype.ext
  refine Prod.ext ?_ h1
  funext w k
  obtain ⟨i, rfl⟩ := harrisPlace_surjective p θ w
  obtain ⟨⟨τ, b⟩, rfl⟩ := (cmFactorEmbeddingEquiv Φ hΦ).surjective i
  cases b
  · have hc : cmFactorEmbeddingEquiv Φ hΦ (τ, false) = ComplexEmbedding.conjugate (Φ τ) := by
      simp [cmFactorEmbedding]
    rw [hc, harrisPlace_conjugate E]
    have hm := m.2 (harrisPlace p θ (Φ τ)) (Fin.rev k)
    have hm' := m'.2 (harrisPlace p θ (Φ τ)) (Fin.rev k)
    rw [Fin.rev_rev] at hm hm'
    have := h2 τ (Fin.rev k)
    omega
  · have hc : cmFactorEmbeddingEquiv Φ hΦ (τ, true) = Φ τ := by
      simp [cmFactorEmbedding]
    rw [hc]
    exact h2 τ k

/-- If the Frobenius orbits on embeddings are the fibres of the place map, then every
Frobenius-invariant cocharacter in embedding coordinates is `ℚ_p`-rational. -/
theorem frobeniusInvariantsRational_of_frobeniusOrbitsArePlaces
    {Φ : (E →+* ℝ) → (K →+* ℂ)} (hΦ : IsCMSection E K Φ) (n : ℕ)
    (h : FrobeniusOrbitsArePlaces K p θ) : FrobeniusInvariantsRational E K n p θ hΦ := by
  intro a ha
  classical
  let b : (K →+* ℂ) → Fin n → ℤ := fun i => cocharExtend a ((cmFactorEmbeddingEquiv Φ hΦ).symm i)
  have hbF : ∀ i, b (frobeniusPerm K p θ i) = b i := by
    intro i
    obtain ⟨x, rfl⟩ := (cmFactorEmbeddingEquiv Φ hΦ).surjective i
    have hx : frobeniusPerm K p θ (cmFactorEmbeddingEquiv Φ hΦ x) =
        cmFactorEmbeddingEquiv Φ hΦ ((frobeniusCMPerm hΦ θ : Equiv.Perm _) x) := by
      rw [frobeniusCMPerm, CMPerm.ofEmbeddingPerm_apply]
    funext k
    simp only [b, hx, Equiv.symm_apply_apply]
    exact cocharExtend_apply_of_cocharPullback_eq ha x k
  have hbFr : ∀ (r : ℕ) i, b ((frobeniusPerm K p θ ^ r) i) = b i := by
    intro r
    induction r with
    | zero => intro i; rfl
    | succ r ih => intro i; rw [pow_succ', Equiv.Perm.mul_apply, hbF, ih]
  have hfib : ∀ i j, harrisPlace p θ j = harrisPlace p θ i → b j = b i := by
    intro i j hij
    obtain ⟨r, rfl⟩ := ((h i).2 j).mp hij
    exact hbFr r i
  have hconj : ∀ i k, b (ComplexEmbedding.conjugate i) k = a.1 - b i (Fin.rev k) := by
    intro i k
    simp only [b, cmFactorEmbeddingEquiv_symm_conjugate, cocharExtend_cmSwap]
  let pick : FinitePlacesAbove K (rationalPrimePlace p) → (K →+* ℂ) :=
    fun w => (harrisPlace_surjective p θ w).choose
  have hpick : ∀ w, harrisPlace p θ (pick w) = w :=
    fun w => (harrisPlace_surjective p θ w).choose_spec
  refine ⟨⟨(fun w k => b (pick w) k, a.1), ?_⟩, ?_⟩
  · intro w k
    change b (pick w) k + b (pick (placeConj (E := E) (rationalPrimePlace p) w)) (Fin.rev k) = a.1
    have hw : b (pick (placeConj (E := E) (rationalPrimePlace p) w)) =
        b (ComplexEmbedding.conjugate (pick w)) :=
      hfib _ _ (by rw [harrisPlace_conjugate E, hpick, hpick])
    rw [hw, hconj, Fin.rev_rev]
    ring
  · refine Prod.ext rfl ?_
    funext τ k
    change b (pick (harrisPlace p θ (Φ τ))) k = a.2 τ k
    rw [hfib (Φ τ) _ (hpick _)]
    have hτ : (cmFactorEmbeddingEquiv Φ hΦ).symm (Φ τ) = (τ, true) := by
      rw [Equiv.symm_apply_eq]
      simp [cmFactorEmbedding]
    simp only [b, hτ, cocharExtend, ite_true]

end Conjugation

end Langlands.Shimura.KottwitzDual
