import Langlands.Global.Factors.FiniteComparisonProof

/-!
# An analytic engine for products of global functional equations

Generic lemmas for the proof of
`Langlands.Global.FunctionalEquationComparison.RelativeWeilTwistFunctionalEquationStatement`.
A global functional-equation package on a type of finite places collects an Euler
product over all finite places, nonvanishing on a right half-plane, a meromorphic
continuation, an archimedean block and the completed functional equation with the
epsilon factors of a finite set. Packages are closed under products, integer powers
and regrouping of places along a map with finite fibres.
-/

noncomputable section

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Langlands.Global.FunctionalEquationComparison

namespace RelativeWeilEngine

/-! ### Equality of punctured germs -/

theorem meromorphicEq_of_eq {f g : ℂ → ℂ} (h : ∀ s, f s = g s) : MeromorphicEq f g :=
  fun _ => Eventually.of_forall h

theorem MeromorphicEq.mul {f g f' g' : ℂ → ℂ} (h : MeromorphicEq f g) (h' : MeromorphicEq f' g') :
    MeromorphicEq (fun s => f s * f' s) (fun s => g s * g' s) :=
  fun z => (h z).mul (h' z)

theorem MeromorphicEq.inv {f g : ℂ → ℂ} (h : MeromorphicEq f g) :
    MeromorphicEq (fun s => (f s)⁻¹) (fun s => (g s)⁻¹) :=
  fun z => (h z).inv

theorem MeromorphicEq.zpow {f g : ℂ → ℂ} (h : MeromorphicEq f g) (n : ℤ) :
    MeromorphicEq (fun s => f s ^ n) (fun s => g s ^ n) :=
  fun z => (h z).fun_comp (· ^ n)

/-- Equality eventually along `Filter.codiscrete ℂ`, that is, outside a closed discrete
subset of `ℂ`, is equality of all punctured germs. -/
theorem meromorphicEq_of_codiscrete {f g : ℂ → ℂ}
    (h : ∀ᶠ s in Filter.codiscrete ℂ, f s = g s) : MeromorphicEq f g := by
  intro z
  have h' := (mem_codiscreteWithin.mp h) z (Set.mem_univ z)
  rw [Filter.disjoint_principal_right] at h'
  filter_upwards [h'] with s hs
  by_contra hne
  exact hs ⟨Set.mem_univ s, hne⟩

/-! ### Nonzero meromorphic functions -/

theorem NonzeroMeromorphic.meromorphicAt {f : ℂ → ℂ} (h : NonzeroMeromorphic f) (z : ℂ) :
    MeromorphicAt f z :=
  h.1 z

theorem NonzeroMeromorphic.congr {f g : ℂ → ℂ} (h : NonzeroMeromorphic f)
    (hfg : MeromorphicEq f g) : NonzeroMeromorphic g := by
  refine ⟨fun z => (h.1 z).congr (hfg z), fun z => ?_⟩
  rw [← meromorphicOrderAt_congr (hfg z)]
  exact h.2 z

theorem nonzeroMeromorphic_const {c : ℂ} (hc : c ≠ 0) : NonzeroMeromorphic (fun _ => c) := by
  refine ⟨fun z => MeromorphicAt.const c z, fun z => ?_⟩
  rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero (MeromorphicAt.const c z)]
  exact Eventually.of_forall fun _ => hc

theorem nonzeroMeromorphic_one : NonzeroMeromorphic (fun _ => (1 : ℂ)) :=
  nonzeroMeromorphic_const one_ne_zero

theorem NonzeroMeromorphic.mul {f g : ℂ → ℂ} (hf : NonzeroMeromorphic f)
    (hg : NonzeroMeromorphic g) : NonzeroMeromorphic (fun s => f s * g s) := by
  refine ⟨fun z => (hf.1 z).mul (hg.1 z), fun z => ?_⟩
  have := meromorphicOrderAt_mul (hf.1 z) (hg.1 z)
  simp only [Pi.mul_def] at this
  rw [this]
  exact WithTop.add_ne_top.mpr ⟨hf.2 z, hg.2 z⟩

theorem NonzeroMeromorphic.inv {f : ℂ → ℂ} (hf : NonzeroMeromorphic f) :
    NonzeroMeromorphic (fun s => (f s)⁻¹) := by
  refine ⟨fun z => (hf.1 z).inv, fun z => ?_⟩
  have := meromorphicOrderAt_inv (f := f) (x := z)
  simp only [Pi.inv_def] at this
  rw [this]
  intro h
  exact hf.2 z (by simpa using h)

theorem NonzeroMeromorphic.zpow {f : ℂ → ℂ} (hf : NonzeroMeromorphic f) (n : ℤ) :
    NonzeroMeromorphic (fun s => f s ^ n) := by
  refine ⟨fun z => (hf.1 z).zpow n, fun z => ?_⟩
  have := meromorphicOrderAt_zpow (hf.1 z) (n := n)
  simp only [Pi.pow_def] at this
  rw [this]
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (hf.2 z)
  rw [← hm]
  exact WithTop.coe_ne_top

theorem NonzeroMeromorphic.finsetProd {ι : Type*} (T : Finset ι) {f : ι → ℂ → ℂ}
    (h : ∀ i ∈ T, NonzeroMeromorphic (f i)) :
    NonzeroMeromorphic (fun s => ∏ i ∈ T, f i s) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using nonzeroMeromorphic_one
  | insert a T ha ih =>
    have h1 := h a (Finset.mem_insert_self a T)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have heq : (fun s => ∏ i ∈ insert a T, f i s) = fun s => f a s * ∏ i ∈ T, f i s := by
      funext s; rw [Finset.prod_insert ha]
    rw [heq]
    exact NonzeroMeromorphic.mul h1 h2

/-- A meromorphic function on `ℂ` that is nonzero on a right half-plane has nonzero
germ everywhere. -/
theorem nonzeroMeromorphic_of_ne_zero_halfPlane {f : ℂ → ℂ} (hf : Meromorphic f) (σ : ℝ)
    (hne : ∀ s : ℂ, σ < s.re → f s ≠ 0) : NonzeroMeromorphic f := by
  refine ⟨hf, fun z => ?_⟩
  set x : ℂ := ((σ + 1 : ℝ) : ℂ)
  have hx : σ < x.re := by simp [x]
  have hxtop : meromorphicOrderAt f x ≠ ⊤ := by
    intro htop
    rw [meromorphicOrderAt_eq_top_iff] at htop
    have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : {s : ℂ | σ < s.re} ∈ 𝓝[≠] x :=
      nhdsWithin_le_nhds (hopen.mem_nhds hx)
    obtain ⟨s, hs1, hs2⟩ := (htop.and hmem).exists
    exact hne s hs2 hs1
  exact (Meromorphic.meromorphicOn hf (s := Set.univ)).meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ x) (Set.mem_univ z) hxtop

/-! ### Euler products with nonzero limits -/

/-- A factor of a product with a nonzero limit is nonzero. -/
theorem ne_zero_of_hasProd {ι : Type*} {f : ι → ℂ} {a : ℂ} (h : HasProd f a) (ha : a ≠ 0)
    (i : ι) : f i ≠ 0 := by
  intro hi
  apply ha
  have h0 : HasProd f 0 := by
    have hev : (fun t : Finset ι ↦ ∏ b ∈ t, f b) =ᶠ[atTop] fun _ ↦ 0 := by
      filter_upwards [eventually_ge_atTop {i}] with t ht
      exact Finset.prod_eq_zero (ht (Finset.mem_singleton_self i)) hi
    exact (tendsto_congr' hev).mpr tendsto_const_nhds
  exact h.unique h0

theorem hasProd_zpow {ι : Type*} {f : ι → ℂ} {a : ℂ} (h : HasProd f a) (ha : a ≠ 0) (n : ℤ) :
    HasProd (fun i ↦ f i ^ n) (a ^ n) := by
  cases n with
  | ofNat m => simpa using h.pow m
  | negSucc m => simpa [zpow_negSucc] using (h.pow (m + 1)).inv₀ (pow_ne_zero _ ha)

/-- Regrouping a product along a map with finite fibres `fib q`. -/
theorem hasProd_fiberwise {P Q : Type*} (π : P → Q) (fib : Q → Finset P)
    (hfib : ∀ p q, p ∈ fib q ↔ π p = q) {f : P → ℂ} {a : ℂ} (h : HasProd f a) :
    HasProd (fun q ↦ ∏ p ∈ fib q, f p) a := by
  let e : (Σ q : Q, fib q) ≃ P :=
    { toFun := fun x ↦ x.2.1
      invFun := fun p ↦ ⟨π p, p, (hfib p _).mpr rfl⟩
      left_inv := by
        rintro ⟨q, p, hp⟩
        obtain rfl := (hfib p q).mp hp
        rfl
      right_inv := fun _ ↦ rfl }
  have h' : HasProd (f ∘ e) a := e.hasProd_iff.mpr h
  refine h'.sigma fun q ↦ ?_
  rw [← Finset.prod_coe_sort]
  exact hasProd_fintype _

/-! ### Global functional-equation packages -/

/-- A global functional-equation package on the places `Q`. The Euler products of `l` and
`d` converge on a right half-plane to nonzero values `Λ s` and `Λd s`. These limits are
meromorphic on `ℂ`, and `Λ(s) A(s) = Ae(s) ∏_{v ∈ T} e_v(s) Λd(1 - s) Ad(1 - s)` as an
equality of punctured germs. -/
def HasGlobalEquation {Q : Type*} (l d e : Q → ℂ → ℂ) (A Ad Ae : ℂ → ℂ) (T : Finset Q) :
    Prop :=
  ∃ (σ : ℝ) (Λ Λd : ℂ → ℂ), Meromorphic Λ ∧ Meromorphic Λd ∧
    (∀ s : ℂ, σ < s.re →
      (HasProd (fun v ↦ l v s) (Λ s) ∧ Λ s ≠ 0) ∧ (HasProd (fun v ↦ d v s) (Λd s) ∧ Λd s ≠ 0)) ∧
    MeromorphicEq (fun s ↦ Λ s * A s)
      (fun s ↦ Ae s * (∏ v ∈ T, e v s) * (Λd (1 - s) * Ad (1 - s)))

section Package

variable {Q : Type*} {l d e l' d' e' : Q → ℂ → ℂ} {A Ad Ae A' Ad' Ae' : ℂ → ℂ} {T : Finset Q}

theorem hasGlobalEquation_one (T : Finset Q) :
    HasGlobalEquation (fun _ _ ↦ (1 : ℂ)) (fun _ _ ↦ 1) (fun _ _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1)
      (fun _ ↦ 1) T := by
  refine ⟨0, fun _ ↦ 1, fun _ ↦ 1, fun z ↦ MeromorphicAt.const 1 z,
    fun z ↦ MeromorphicAt.const 1 z, fun _ _ ↦ ⟨⟨hasProd_one, one_ne_zero⟩, hasProd_one,
      one_ne_zero⟩, meromorphicEq_of_eq fun s ↦ by simp⟩

theorem HasGlobalEquation.mul (h : HasGlobalEquation l d e A Ad Ae T)
    (h' : HasGlobalEquation l' d' e' A' Ad' Ae' T) :
    HasGlobalEquation (fun v s ↦ l v s * l' v s) (fun v s ↦ d v s * d' v s)
      (fun v s ↦ e v s * e' v s) (fun s ↦ A s * A' s) (fun s ↦ Ad s * Ad' s)
      (fun s ↦ Ae s * Ae' s) T := by
  obtain ⟨σ, Λ, Λd, hΛ, hΛd, hp, hfe⟩ := h
  obtain ⟨σ', Λ', Λd', hΛ', hΛd', hp', hfe'⟩ := h'
  refine ⟨max σ σ', fun s ↦ Λ s * Λ' s, fun s ↦ Λd s * Λd' s, fun z ↦ (hΛ z).mul (hΛ' z),
    fun z ↦ (hΛd z).mul (hΛd' z), fun s hs ↦ ?_, ?_⟩
  · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp s (lt_of_le_of_lt (le_max_left _ _) hs)
    obtain ⟨⟨h1', h2'⟩, h3', h4'⟩ := hp' s (lt_of_le_of_lt (le_max_right _ _) hs)
    exact ⟨⟨h1.mul h1', mul_ne_zero h2 h2'⟩, h3.mul h3', mul_ne_zero h4 h4'⟩
  · refine MeromorphicEq.trans (meromorphicEq_of_eq fun s ↦ ?_)
      (MeromorphicEq.trans (MeromorphicEq.mul hfe hfe') (meromorphicEq_of_eq fun s ↦ ?_))
    · ring
    · rw [Finset.prod_mul_distrib]
      ring

theorem HasGlobalEquation.inv (h : HasGlobalEquation l d e A Ad Ae T) :
    HasGlobalEquation (fun v s ↦ (l v s)⁻¹) (fun v s ↦ (d v s)⁻¹) (fun v s ↦ (e v s)⁻¹)
      (fun s ↦ (A s)⁻¹) (fun s ↦ (Ad s)⁻¹) (fun s ↦ (Ae s)⁻¹) T := by
  obtain ⟨σ, Λ, Λd, hΛ, hΛd, hp, hfe⟩ := h
  refine ⟨σ, fun s ↦ (Λ s)⁻¹, fun s ↦ (Λd s)⁻¹, fun z ↦ (hΛ z).inv, fun z ↦ (hΛd z).inv,
    fun s hs ↦ ?_, ?_⟩
  · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp s hs
    exact ⟨⟨h1.inv₀ h2, inv_ne_zero h2⟩, h3.inv₀ h4, inv_ne_zero h4⟩
  · refine MeromorphicEq.trans (meromorphicEq_of_eq fun s ↦ ?_)
      (MeromorphicEq.trans (MeromorphicEq.inv hfe) (meromorphicEq_of_eq fun s ↦ ?_))
    · rw [mul_inv]
    · rw [mul_inv, mul_inv, mul_inv, Finset.prod_inv_distrib]

theorem HasGlobalEquation.zpow (h : HasGlobalEquation l d e A Ad Ae T) (n : ℤ) :
    HasGlobalEquation (fun v s ↦ l v s ^ n) (fun v s ↦ d v s ^ n) (fun v s ↦ e v s ^ n)
      (fun s ↦ A s ^ n) (fun s ↦ Ad s ^ n) (fun s ↦ Ae s ^ n) T := by
  obtain ⟨σ, Λ, Λd, hΛ, hΛd, hp, hfe⟩ := h
  refine ⟨σ, fun s ↦ Λ s ^ n, fun s ↦ Λd s ^ n, fun z ↦ (hΛ z).zpow n, fun z ↦ (hΛd z).zpow n,
    fun s hs ↦ ?_, ?_⟩
  · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp s hs
    exact ⟨⟨hasProd_zpow h1 h2 n, zpow_ne_zero n h2⟩, hasProd_zpow h3 h4 n, zpow_ne_zero n h4⟩
  · refine MeromorphicEq.trans (meromorphicEq_of_eq fun s ↦ ?_)
      (MeromorphicEq.trans (MeromorphicEq.zpow hfe n) (meromorphicEq_of_eq fun s ↦ ?_))
    · rw [mul_zpow]
    · rw [mul_zpow, mul_zpow, mul_zpow, Finset.prod_zpow]

theorem hasGlobalEquation_finsetProd {ι : Type*} (I : Finset ι) {l d e : ι → Q → ℂ → ℂ}
    {A Ad Ae : ι → ℂ → ℂ}
    (h : ∀ i ∈ I, HasGlobalEquation (l i) (d i) (e i) (A i) (Ad i) (Ae i) T) :
    HasGlobalEquation (fun v s ↦ ∏ i ∈ I, l i v s) (fun v s ↦ ∏ i ∈ I, d i v s)
      (fun v s ↦ ∏ i ∈ I, e i v s) (fun s ↦ ∏ i ∈ I, A i s) (fun s ↦ ∏ i ∈ I, Ad i s)
      (fun s ↦ ∏ i ∈ I, Ae i s) T := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact hasGlobalEquation_one T
  | insert a I ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a I)).mul
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- The exceptional set can be changed by places whose epsilon factor is identically `1`. -/
theorem HasGlobalEquation.changeSet {T' : Finset Q} (h : HasGlobalEquation l d e A Ad Ae T)
    (h1 : ∀ v ∈ T, v ∉ T' → ∀ s, e v s = 1) (h2 : ∀ v ∈ T', v ∉ T → ∀ s, e v s = 1) :
    HasGlobalEquation l d e A Ad Ae T' := by
  classical
  obtain ⟨σ, Λ, Λd, hΛ, hΛd, hp, hfe⟩ := h
  refine ⟨σ, Λ, Λd, hΛ, hΛd, hp, MeromorphicEq.trans hfe (meromorphicEq_of_eq fun s ↦ ?_)⟩
  have hA : ∏ v ∈ T, e v s = ∏ v ∈ T ∪ T', e v s := by
    refine Finset.prod_subset Finset.subset_union_left fun v hv hn ↦ ?_
    rcases Finset.mem_union.mp hv with hv | hv
    · exact absurd hv hn
    · exact h2 v hv hn s
  have hB : ∏ v ∈ T', e v s = ∏ v ∈ T ∪ T', e v s := by
    refine Finset.prod_subset Finset.subset_union_right fun v hv hn ↦ ?_
    rcases Finset.mem_union.mp hv with hv | hv
    · exact h1 v hv hn s
    · exact absurd hv hn
  have hT : ∏ v ∈ T, e v s = ∏ v ∈ T', e v s := hA.trans hB.symm
  rw [hT]

/-- Local factors may be replaced by factors agreeing on a right half-plane, exceptional
epsilon factors and archimedean factors by factors with the same punctured germs. -/
theorem HasGlobalEquation.congr (h : HasGlobalEquation l d e A Ad Ae T) (σ' : ℝ)
    (hl : ∀ v s, σ' < s.re → l v s = l' v s) (hd : ∀ v s, σ' < s.re → d v s = d' v s)
    (he : ∀ v ∈ T, MeromorphicEq (e v) (e' v)) (hA : MeromorphicEq A A')
    (hAd : MeromorphicEq Ad Ad') (hAe : MeromorphicEq Ae Ae') :
    HasGlobalEquation l' d' e' A' Ad' Ae' T := by
  obtain ⟨σ, Λ, Λd, hΛ, hΛd, hp, hfe⟩ := h
  refine ⟨max σ σ', Λ, Λd, hΛ, hΛd, fun s hs ↦ ?_, ?_⟩
  · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp s (lt_of_le_of_lt (le_max_left _ _) hs)
    have hs' : σ' < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    refine ⟨⟨?_, h2⟩, ?_, h4⟩
    · simpa only [hl _ s hs'] using h1
    · simpa only [hd _ s hs'] using h3
  · exact MeromorphicEq.trans (MeromorphicEq.mul (MeromorphicEq.refl Λ) (MeromorphicEq.symm hA))
      (MeromorphicEq.trans hfe (MeromorphicEq.mul (MeromorphicEq.mul hAe
        (MeromorphicEq.finset_prod T he)) (MeromorphicEq.mul (MeromorphicEq.refl _) (MeromorphicEq.reflect hAd))))

/-- Regrouping the places along a map `π : P → Q` with finite fibres `fib q`. -/
theorem HasGlobalEquation.pushforward {P : Type*} [DecidableEq P] (π : P → Q)
    (fib : Q → Finset P) (hfib : ∀ p q, p ∈ fib q ↔ π p = q) {l d e : P → ℂ → ℂ}
    (h : HasGlobalEquation l d e A Ad Ae (T.biUnion fib)) :
    HasGlobalEquation (fun q s ↦ ∏ p ∈ fib q, l p s) (fun q s ↦ ∏ p ∈ fib q, d p s)
      (fun q s ↦ ∏ p ∈ fib q, e p s) A Ad Ae T := by
  obtain ⟨σ, Λ, Λd, hΛ, hΛd, hp, hfe⟩ := h
  refine ⟨σ, Λ, Λd, hΛ, hΛd, fun s hs ↦ ?_, MeromorphicEq.trans hfe (meromorphicEq_of_eq fun s ↦ ?_)⟩
  · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp s hs
    exact ⟨⟨hasProd_fiberwise π fib hfib h1, h2⟩, hasProd_fiberwise π fib hfib h3, h4⟩
  · have hdisj : (T : Set Q).PairwiseDisjoint fib := by
      intro q _ q' _ hqq'
      refine Finset.disjoint_left.mpr fun p hp hp' ↦ hqq' ?_
      exact ((hfib p q).mp hp).symm.trans ((hfib p q').mp hp')
    rw [Finset.prod_biUnion hdisj]

end Package

/-! ### Conversion to the format of the target statement -/

/-- Cancelling a nonzero meromorphic factor, as an equality of punctured germs. -/
theorem meromorphicEq_cancel {a b g : ℂ → ℂ} (hg : NonzeroMeromorphic g) :
    MeromorphicEq (fun s ↦ a s * (g s)⁻¹ * (b s * g s)) (fun s ↦ a s * b s) := by
  intro z
  filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hg.1 z)).mp (hg.2 z)]
    with s hs
  calc a s * (g s)⁻¹ * (b s * g s) = a s * b s * (g s * (g s)⁻¹) := by ring
    _ = a s * b s := by rw [mul_inv_cancel₀ hs, mul_one]

/-- Removing finitely many nonzero factors from a product. -/
theorem hasProd_compl_of_ne_zero {Q : Type*} {f : Q → ℂ} {a : ℂ} (h : HasProd f a)
    (B : Finset Q) (hB : ∀ z ∈ B, f z ≠ 0) :
    HasProd (fun z : {z // z ∉ B} ↦ f z) (a * (∏ z ∈ B, f z)⁻¹) := by
  classical
  have h1 := h.congr_cofinite₀ (g := fun z ↦ if z ∈ B then 1 else f z) hB
    (fun z hz ↦ by simp [hz])
  have h2 : (∏ i ∈ B, (if i ∈ B then (1 : ℂ) else f i)) = 1 :=
    Finset.prod_eq_one fun i hi ↦ by simp [hi]
  rw [h2, one_div] at h1
  refine (hasProd_subtype_iff_mulIndicator (s := {z | z ∉ B}) (f := f)).mpr ?_
  convert h1 using 1
  funext z
  by_cases hz : z ∈ B <;> simp [Set.mulIndicator, hz]

/-- The places outside `univ.disjSum B` are the finite places outside `B`. -/
def complDisjSumEquiv {I Q : Type*} [Fintype I] (B : Finset Q) :
    {z : Q // z ∉ B} ≃ {v : I ⊕ Q // v ∉ (Finset.univ : Finset I).disjSum B} where
  toFun z := ⟨Sum.inr z.1, by simpa only [Finset.inr_mem_disjSum] using z.2⟩
  invFun v := match v with
    | ⟨Sum.inl _, h⟩ => absurd (Finset.inl_mem_disjSum.mpr (Finset.mem_univ _)) h
    | ⟨Sum.inr z, h⟩ => ⟨z, by simpa only [Finset.inr_mem_disjSum] using h⟩
  left_inv _ := rfl
  right_inv v := by
    rcases v with ⟨w | z, h⟩
    · exact absurd (Finset.inl_mem_disjSum.mpr (Finset.mem_univ _)) h
    · rfl

/-- A global functional-equation package on the finite places `Q`, with exceptional set
`B`, gives the target's admissibility, Euler products and completed functional equation
for the Euler data with archimedean block `arch` and finite factors `f`, at the exceptional
set `univ.disjSum B`. The archimedean products are `A`, `Ad`, `Ae` up to punctured germs;
`f` agrees with the package on a right half-plane off `B` and as germs on `B`. -/
theorem HasGlobalEquation.toFunctionalEquation {I Q : Type*} [Fintype I] [DecidableEq (I ⊕ Q)]
    {l d e : Q → ℂ → ℂ} {A Ad Ae : ℂ → ℂ} {B : Finset Q}
    (h : HasGlobalEquation l d e A Ad Ae B) (arch : I → LocalFactors) (f : Q → LocalFactors)
    (harch : ∀ w, NonzeroMeromorphic (arch w).lFactor ∧
      NonzeroMeromorphic (arch w).dualLFactor ∧ NonzeroMeromorphic (arch w).epsilonFactor)
    (hA : MeromorphicEq (fun s ↦ ∏ w, (arch w).lFactor s) A)
    (hAd : MeromorphicEq (fun s ↦ ∏ w, (arch w).dualLFactor s) Ad)
    (hAe : MeromorphicEq (fun s ↦ ∏ w, (arch w).epsilonFactor s) Ae)
    (σ' : ℝ) (hout : ∀ z ∉ B, ∀ s : ℂ, σ' < s.re →
      (f z).lFactor s = l z s ∧ (f z).dualLFactor s = d z s)
    (hin : ∀ z ∈ B, MeromorphicEq (f z).lFactor (l z) ∧
      MeromorphicEq (f z).dualLFactor (d z) ∧ MeromorphicEq (f z).epsilonFactor (e z))
    (hinz : ∀ z ∈ B, NonzeroMeromorphic (f z).lFactor ∧
      NonzeroMeromorphic (f z).dualLFactor ∧ NonzeroMeromorphic (f z).epsilonFactor) :
    ∃ (σ : ℝ) (Lp Lpd : ℂ → ℂ),
      Admissible (FiniteEulerData.mk (Sum.elim arch f) Lp Lpd)
        ((Finset.univ : Finset I).disjSum B) ∧
      HasEulerProductsOutside (FiniteEulerData.mk (Sum.elim arch f) Lp Lpd)
        ((Finset.univ : Finset I).disjSum B) σ ∧
      FunctionalEquation (FiniteEulerData.mk (Sum.elim arch f) Lp Lpd)
        ((Finset.univ : Finset I).disjSum B) := by
  obtain ⟨σ, Λ, Λd, hΛ, hΛd, hp, hfe⟩ := h
  have hlB : ∀ z ∈ B, NonzeroMeromorphic (l z) := fun z hz ↦ NonzeroMeromorphic.congr (hinz z hz).1 (hin z hz).1
  have hdB : ∀ z ∈ B, NonzeroMeromorphic (d z) :=
    fun z hz ↦ NonzeroMeromorphic.congr (hinz z hz).2.1 (hin z hz).2.1
  have hPB : NonzeroMeromorphic (fun s ↦ ∏ z ∈ B, l z s) := NonzeroMeromorphic.finsetProd B hlB
  have hPBd : NonzeroMeromorphic (fun s ↦ ∏ z ∈ B, d z s) :=
    NonzeroMeromorphic.finsetProd B hdB
  have hΛnm : NonzeroMeromorphic Λ :=
    nonzeroMeromorphic_of_ne_zero_halfPlane hΛ σ fun s hs ↦ (hp s hs).1.2
  have hΛdnm : NonzeroMeromorphic Λd :=
    nonzeroMeromorphic_of_ne_zero_halfPlane hΛd σ fun s hs ↦ (hp s hs).2.2
  refine ⟨max σ σ', fun s ↦ Λ s * (∏ z ∈ B, l z s)⁻¹, fun s ↦ Λd s * (∏ z ∈ B, d z s)⁻¹,
    ⟨NonzeroMeromorphic.mul hΛnm (NonzeroMeromorphic.inv hPB),
      NonzeroMeromorphic.mul hΛdnm (NonzeroMeromorphic.inv hPBd), fun v hv ↦ ?_⟩, fun s hs ↦ ?_, ?_⟩
  · rcases v with w | z
    · exact harch w
    · exact hinz z (Finset.inr_mem_disjSum.mp hv)
  · have hσ : σ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hσ' : σ' < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp s hσ
    have hl := hasProd_compl_of_ne_zero h1 B fun z _ ↦ ne_zero_of_hasProd h1 h2 z
    have hd := hasProd_compl_of_ne_zero h3 B fun z _ ↦ ne_zero_of_hasProd h3 h4 z
    constructor
    · refine (complDisjSumEquiv (I := I) B).hasProd_iff.mp ?_
      refine hl.congr_fun fun z ↦ ?_
      exact (hout z.1 z.2 s hσ').1
    · refine (complDisjSumEquiv (I := I) B).hasProd_iff.mp ?_
      refine hd.congr_fun fun z ↦ ?_
      exact (hout z.1 z.2 s hσ').2
  · show MeromorphicEq
      (fun s ↦ (Λ s * (∏ z ∈ B, l z s)⁻¹) *
        ∏ v ∈ (Finset.univ : Finset I).disjSum B, (Sum.elim arch f v).lFactor s)
      (fun s ↦ (∏ v ∈ (Finset.univ : Finset I).disjSum B, (Sum.elim arch f v).epsilonFactor s) *
        ((Λd (1 - s) * (∏ z ∈ B, d z (1 - s))⁻¹) *
          ∏ v ∈ (Finset.univ : Finset I).disjSum B, (Sum.elim arch f v).dualLFactor (1 - s)))
    simp only [Finset.prod_disjSum, Sum.elim_inl, Sum.elim_inr]
    have step1 : MeromorphicEq
        (fun s ↦ (Λ s * (∏ z ∈ B, l z s)⁻¹) *
          ((∏ w, (arch w).lFactor s) * ∏ z ∈ B, (f z).lFactor s))
        (fun s ↦ Λ s * (∏ z ∈ B, l z s)⁻¹ * (A s * ∏ z ∈ B, l z s)) :=
      MeromorphicEq.mul (MeromorphicEq.refl _)
        (MeromorphicEq.mul hA (MeromorphicEq.finset_prod B fun z hz ↦ (hin z hz).1))
    have step2 := meromorphicEq_cancel (a := Λ) (b := A) hPB
    have step4 : MeromorphicEq
        (fun s ↦ Λd (1 - s) * (∏ z ∈ B, d z (1 - s))⁻¹ * (Ad (1 - s) * ∏ z ∈ B, d z (1 - s)))
        (fun s ↦ Λd (1 - s) * Ad (1 - s)) :=
      MeromorphicEq.reflect (meromorphicEq_cancel (a := Λd) (b := Ad) hPBd)
    have step5 : MeromorphicEq
        (fun s ↦ ((∏ w, (arch w).epsilonFactor s) * ∏ z ∈ B, (f z).epsilonFactor s) *
          ((Λd (1 - s) * (∏ z ∈ B, d z (1 - s))⁻¹) *
            ((∏ w, (arch w).dualLFactor (1 - s)) * ∏ z ∈ B, (f z).dualLFactor (1 - s))))
        (fun s ↦ (Ae s * ∏ z ∈ B, e z s) *
          (Λd (1 - s) * (∏ z ∈ B, d z (1 - s))⁻¹ * (Ad (1 - s) * ∏ z ∈ B, d z (1 - s)))) :=
      MeromorphicEq.mul
        (MeromorphicEq.mul hAe (MeromorphicEq.finset_prod B fun z hz ↦ (hin z hz).2.2))
        (MeromorphicEq.mul (MeromorphicEq.refl _) (MeromorphicEq.reflect
          (MeromorphicEq.mul hAd (MeromorphicEq.finset_prod B fun z hz ↦ (hin z hz).2.1))))
    exact MeromorphicEq.trans step1 (MeromorphicEq.trans step2 (MeromorphicEq.trans hfe
      (MeromorphicEq.trans (MeromorphicEq.mul (MeromorphicEq.refl _) (MeromorphicEq.symm step4))
        (MeromorphicEq.symm step5))))

end RelativeWeilEngine

end Langlands.Global.FunctionalEquationComparison
