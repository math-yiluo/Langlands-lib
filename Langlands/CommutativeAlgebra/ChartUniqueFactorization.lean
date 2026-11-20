import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.NumDen
import Langlands.AnthropicFLT.Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one

/-! # A unique-factorization criterion from one factorial chart -/

noncomputable section

namespace Langlands.CommutativeAlgebra.ChartUniqueFactorization

variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]

variable (K) in
/-- The localization of `A` at a prime ideal, as a subalgebra of the fraction field. -/
abbrev loc (p : Ideal A) [p.IsPrime] : Subalgebra A K :=
  Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors

theorem mem_loc {p : Ideal A} [p.IsPrime] {x : K} :
    x ∈ loc K p ↔ ∃ a s : A, s ∉ p ∧ x = algebraMap A K a * (algebraMap A K s)⁻¹ :=
  ⟨fun ⟨a, s, hs, h⟩ => ⟨a, s, hs, h⟩, fun ⟨a, s, hs, h⟩ => ⟨a, s, hs, h⟩⟩

theorem algebraMap_mem_loc (p : Ideal A) [p.IsPrime] (a : A) : algebraMap A K a ∈ loc K p :=
  Subalgebra.algebraMap_mem _ a

/-- A nonzero element of a prime ideal is not invertible in the localization at that prime. -/
theorem inv_algebraMap_notMem_loc {p : Ideal A} [p.IsPrime] {a : A} (ha : a ∈ p) (ha0 : a ≠ 0) :
    (algebraMap A K a)⁻¹ ∉ loc K p := by
  rintro ⟨c, s, hs, h⟩
  have hinj := IsFractionRing.injective A K
  have ha' : algebraMap A K a ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap A K)]; exact fun h' => ha0 (hinj h')
  have hs0 : s ≠ 0 := fun h' => hs (h' ▸ p.zero_mem)
  have hs' : algebraMap A K s ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap A K)]; exact fun h' => hs0 (hinj h')
  have : algebraMap A K s = algebraMap A K (a * c) := by
    rw [map_mul]
    field_simp at h
    linear_combination h
  exact hs (hinj this ▸ p.mul_mem_right c ha)

variable (K) in
/-- The localization of a subalgebra `S` of `K` at a prime ideal of `S`, as a subalgebra of `K`. -/
abbrev chartLoc (S : Subalgebra A K) (Q : Ideal S) [Q.IsPrime] : Subalgebra S K :=
  Localization.subalgebra.ofField K Q.primeCompl Q.primeCompl_le_nonZeroDivisors

/-- `S` is a chart of `A`: its localization at every prime equals the localization of `A` at the
contracted prime, inside the fraction field. This is the algebraic shadow of an open immersion
`Spec S → Spec A`. -/
def IsChart (S : Subalgebra A K) : Prop :=
  ∀ (Q : Ideal S) [Q.IsPrime] (x : K), x ∈ chartLoc K S Q ↔ x ∈ loc K (Q.comap (algebraMap A S))

theorem mem_loc_of_mem_chart {S : Subalgebra A K} (hS : IsChart S) (Q : Ideal S) [Q.IsPrime]
    {x : K} (hx : x ∈ S) : x ∈ loc K (Q.comap (algebraMap A S)) :=
  (hS Q x).1 (Subalgebra.algebraMap_mem (chartLoc K S Q) (⟨x, hx⟩ : S))

/-- A chart has the same heights as the ring it charts. -/
theorem height_comap_eq {S : Subalgebra A K} (hS : IsChart S) (Q : Ideal S) [Q.IsPrime] :
    (Q.comap (algebraMap A S)).height = Q.height := by
  have h : (loc K (Q.comap (algebraMap A S))).toSubring = (chartLoc K S Q).toSubring := by
    ext x
    exact (hS Q x).symm
  have e : ringKrullDim (loc K (Q.comap (algebraMap A S))) = ringKrullDim (chartLoc K S Q) :=
    ringKrullDim_eq_of_ringEquiv (RingEquiv.subringCongr h)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (Q.comap (algebraMap A S))
      (loc K (Q.comap (algebraMap A S))),
    IsLocalization.AtPrime.ringKrullDim_eq_height Q (chartLoc K S Q)] at e
  exact_mod_cast e

/-- Integer powers of an element whose inverse also lies in a subalgebra lie in the subalgebra. -/
theorem zpow_mem {R : Type*} [CommRing R] [Algebra R K] (S : Subalgebra R K) {f : K}
    (hf : f ∈ S) (hf' : f⁻¹ ∈ S) (n : ℤ) : f ^ n ∈ S := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using S.pow_mem hf m
  · simpa using S.pow_mem hf' m

/-- Nonnegative integer powers of an element of a subalgebra lie in the subalgebra. -/
theorem zpow_mem_of_nonneg {R : Type*} [CommRing R] [Algebra R K] (S : Subalgebra R K) {f : K}
    (hf : f ∈ S) {n : ℤ} (hn : 0 ≤ n) : f ^ n ∈ S := by
  lift n to ℕ using hn
  simpa using S.pow_mem hf n

/-- Elements invertible in a subalgebra are closed under multiplication. -/
theorem unit_mul {R : Type*} [CommRing R] [Algebra R K] {S : Subalgebra R K} {x y : K}
    (hx : x ∈ S ∧ x⁻¹ ∈ S) (hy : y ∈ S ∧ y⁻¹ ∈ S) : x * y ∈ S ∧ (x * y)⁻¹ ∈ S :=
  ⟨S.mul_mem hx.1 hy.1, by rw [mul_inv]; exact S.mul_mem hx.2 hy.2⟩

/-- Elements invertible in a subalgebra are closed under finite products. -/
theorem unit_prod {R : Type*} [CommRing R] [Algebra R K] {S : Subalgebra R K} {ι : Type*}
    (s : Finset ι) (g : ι → K) (hg : ∀ i ∈ s, g i ∈ S ∧ (g i)⁻¹ ∈ S) :
    (∏ i ∈ s, g i) ∈ S ∧ (∏ i ∈ s, g i)⁻¹ ∈ S :=
  Finset.prod_induction g (fun x => x ∈ S ∧ x⁻¹ ∈ S) (fun _ _ hx hy => unit_mul hx hy)
    ⟨S.one_mem, by rw [inv_one]; exact S.one_mem⟩ hg

/-- **Unique factorization from one factorial chart.** Let `A` be a Noetherian integrally
closed domain with fraction field `K` and let `S ⊆ K` be a factorial chart of `A`. Let `p i`
be finitely many primes of `A` at which `A` is a discrete valuation ring with uniformizer
`f i`, where each `f i` is a unit of `S` and `f j` is a unit at `p i` for `j ≠ i`. If every
height-one prime of `A` either comes from `S` or is some `p i`, then `A` is factorial. -/
theorem uniqueFactorizationMonoid_of_chart [IsNoetherianRing A] [IsIntegrallyClosed A]
    (S : Subalgebra A K) [UniqueFactorizationMonoid S] (hS : IsChart S)
    {r : Type*} [Fintype r] (f : r → K) (hf : ∀ i, f i ∈ S) (hf' : ∀ i, (f i)⁻¹ ∈ S)
    (p : r → Ideal A) [∀ i, (p i).IsPrime]
    (hfp : ∀ i, f i ∈ loc K (p i)) (hfp' : ∀ i, (f i)⁻¹ ∉ loc K (p i))
    (hval : ∀ i (x : K), x ≠ 0 →
      ∃ n : ℤ, x * f i ^ (-n) ∈ loc K (p i) ∧ (x * f i ^ (-n))⁻¹ ∈ loc K (p i))
    (hunit : ∀ i j, i ≠ j → f j ∈ loc K (p i) ∧ (f j)⁻¹ ∈ loc K (p i))
    (hexh : ∀ q : Ideal A, q.IsPrime → q.height = 1 →
      (∃ Q : Ideal S, Q.IsPrime ∧ Q.comap (algebraMap A S) = q) ∨ ∃ i, q = p i) :
    UniqueFactorizationMonoid A := by
  classical
  have hinj := IsFractionRing.injective A K
  have hne : ∀ b : A, b ≠ 0 → algebraMap A K b ≠ 0 := fun b hb h0 =>
    hb (hinj (h0.trans (map_zero (algebraMap A K)).symm))
  -- the Krull property
  have krull : ∀ x : K, (∀ (q : Ideal A) [q.IsPrime], q.height = 1 → x ∈ loc K q) →
      ∃ a : A, algebraMap A K a = x := by
    intro x hx
    refine IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one K x ?_
    intro q _ hq
    obtain ⟨a, s, hs, h⟩ := mem_loc.1 (hx q hq)
    have hs0 : algebraMap A K s ≠ 0 := hne s fun h' => hs (h' ▸ q.zero_mem)
    exact ⟨a, s, hs, by rw [h, mul_assoc, inv_mul_cancel₀ hs0, mul_one]⟩
  -- a criterion: membership in `S` and in all localizations at the `p i`
  have crit : ∀ x : K, x ∈ S → (∀ i, x ∈ loc K (p i)) → ∃ a : A, algebraMap A K a = x := by
    intro x hxS hxp
    refine krull x fun q _ h1 => ?_
    rcases hexh q inferInstance h1 with ⟨Q, hQ, hQq⟩ | ⟨i, rfl⟩
    · subst hQq
      exact mem_loc_of_mem_chart hS Q hxS
    · exact hxp i
  -- units of `S` that are powers of the `f i`
  have hzS : ∀ (i : r) (m : ℤ), f i ^ m ∈ S ∧ (f i ^ m)⁻¹ ∈ S := fun i m =>
    ⟨zpow_mem S (hf i) (hf' i) m, by rw [← zpow_neg]; exact zpow_mem S (hf i) (hf' i) _⟩
  have hzp : ∀ (i j : r) (m : ℤ), i ≠ j →
      f j ^ m ∈ loc K (p i) ∧ (f j ^ m)⁻¹ ∈ loc K (p i) := fun i j m hij =>
    ⟨zpow_mem _ (hunit i j hij).1 (hunit i j hij).2 m, by
      rw [← zpow_neg]; exact zpow_mem _ (hunit i j hij).1 (hunit i j hij).2 _⟩
  refine UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one ?_
  intro q hq h1
  rcases hexh q hq h1 with ⟨Q, hQ, hQq⟩ | ⟨i, rfl⟩
  · -- a height-one prime coming from the chart
    have hQ1 : Q.height = 1 := by rw [← height_comap_eq hS Q, hQq, h1]
    obtain ⟨π, hπ⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hQ1)
    have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hQ1
    have hπ0 : (π : K) ≠ 0 := by
      intro h0
      apply hQne
      rw [hπ, Submodule.span_singleton_eq_bot]
      exact Subtype.ext h0
    choose n hn using fun i => hval i (π : K) hπ0
    set u : K := ∏ i, f i ^ (-n i) with hu
    have huS : u ∈ S ∧ u⁻¹ ∈ S := unit_prod _ _ fun i _ => hzS i (-n i)
    -- `π * u` is a unit at every `p j`
    have hπu : ∀ j, (π : K) * u ∈ loc K (p j) ∧ ((π : K) * u)⁻¹ ∈ loc K (p j) := by
      intro j
      rw [hu, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), ← mul_assoc]
      exact unit_mul (hn j) (unit_prod _ _ fun i hi => hzp j i _ (Finset.ne_of_mem_erase hi).symm)
    obtain ⟨a, ha⟩ := crit ((π : K) * u) (S.mul_mem π.2 huS.1) fun j => (hπu j).1
    refine ⟨a, le_antisymm ?_ ?_⟩
    · intro b hb
      rw [← hQq, Ideal.mem_comap, hπ, Ideal.mem_span_singleton'] at hb
      obtain ⟨s, hs⟩ := hb
      have hs' : (s : K) * π = algebraMap A K b := congrArg Subtype.val hs
      have hsu : (s : K) * u⁻¹ = algebraMap A K b * ((π : K) * u)⁻¹ := by
        rw [← hs', mul_inv, mul_assoc, ← mul_assoc (π : K), mul_inv_cancel₀ hπ0, one_mul]
      obtain ⟨c, hc⟩ := crit ((s : K) * u⁻¹) (S.mul_mem s.2 huS.2) fun j => by
        rw [hsu]; exact (loc K (p j)).mul_mem (algebraMap_mem_loc _ b) (hπu j).2
      refine (Submodule.mem_span_singleton (R := A)).2 ⟨c, hinj ?_⟩
      have hu0 : u ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ fun h0 =>
        hfp' i (by rw [h0, inv_zero]; exact Subalgebra.zero_mem _)
      rw [smul_eq_mul, map_mul, hc, ha, ← hs']
      field_simp
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, ← hQq, Ideal.mem_comap,
        hπ, Ideal.mem_span_singleton']
      exact ⟨⟨u, huS.1⟩, Subtype.ext (by
        change u * (π : K) = algebraMap A K a
        rw [ha, mul_comm])⟩
  · -- one of the primes `p i`
    obtain ⟨a, ha⟩ := crit (f i) (hf i) fun j => by
      rcases eq_or_ne j i with rfl | hji
      · exact hfp j
      · exact (hunit j i hji).1
    have hfi0 : f i ≠ 0 := fun h0 => hfp' i (by rw [h0, inv_zero]; exact Subalgebra.zero_mem _)
    have hai : a ∈ p i := by
      by_contra h
      apply hfp' i
      rw [← ha]
      exact mem_loc.2 ⟨1, a, h, by rw [map_one, one_mul]⟩
    refine ⟨a, le_antisymm ?_ ?_⟩
    · intro b hb
      rcases eq_or_ne b 0 with rfl | hb0
      · exact Submodule.zero_mem _
      obtain ⟨n, hn1, hn2⟩ := hval i (algebraMap A K b) (hne b hb0)
      have hbn : algebraMap A K b * f i ^ (-n) * f i ^ n = algebraMap A K b := by
        rw [mul_assoc, ← zpow_add₀ hfi0, neg_add_cancel, zpow_zero, mul_one]
      have hn : 1 ≤ n := by
        by_contra hlt
        push Not at hlt
        apply inv_algebraMap_notMem_loc (K := K) hb hb0
        rw [← hbn, mul_inv, ← zpow_neg]
        exact (loc K (p i)).mul_mem hn2 (zpow_mem_of_nonneg _ (hfp i) (by omega))
      have hxi : algebraMap A K b * (f i)⁻¹ ∈ loc K (p i) := by
        have : algebraMap A K b * (f i)⁻¹ = algebraMap A K b * f i ^ (-n) * f i ^ (n - 1) := by
          rw [mul_assoc, ← zpow_add₀ hfi0, show -n + (n - 1) = -1 by ring, zpow_neg_one]
        rw [this]
        exact (loc K (p i)).mul_mem hn1 (zpow_mem_of_nonneg _ (hfp i) (by omega))
      obtain ⟨c, hc⟩ := crit (algebraMap A K b * (f i)⁻¹)
        (S.mul_mem (Subalgebra.algebraMap_mem S b) (hf' i)) fun j => by
          rcases eq_or_ne j i with rfl | hji
          · exact hxi
          · exact (loc K (p j)).mul_mem (algebraMap_mem_loc _ b) (hunit j i hji).2
      refine (Submodule.mem_span_singleton (R := A)).2 ⟨c, hinj ?_⟩
      rw [smul_eq_mul, map_mul, hc, ha, mul_assoc, inv_mul_cancel₀ hfi0, mul_one]
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hai

end Langlands.CommutativeAlgebra.ChartUniqueFactorization
