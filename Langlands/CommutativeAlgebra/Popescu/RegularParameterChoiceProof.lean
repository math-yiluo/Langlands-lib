import Langlands.CommutativeAlgebra.Popescu.RegularParameterChoiceStatement
import Langlands.CommutativeAlgebra.Popescu.RegularSequencePowersProof
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_RegularLocalRingFlatLocalAscent

/-! # Proof of Stacks Lemma 16.10.2 (07FD): choosing regular parameters -/

universe u

open RingTheory IsLocalRing

namespace Langlands.CommutativeAlgebra.Popescu

namespace RegularParameterChoice

/-- The first `i` entries of `List.ofFn x` are the values `x j` with `j < i`. -/
theorem mem_take_ofFn_iff {α : Type*} {d : ℕ} (x : Fin d → α) (i : Fin d) (r : α) :
    r ∈ (List.ofFn x).take i.val ↔ r ∈ x '' {j | j < i} := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simp only [List.length_ofFn] at hj
    exact ⟨⟨j, by omega⟩, by simp only [Set.mem_ofPred_eq, Fin.lt_def]; omega, by simp⟩
  · rintro ⟨j, hj, rfl⟩
    simp only [Set.mem_ofPred_eq, Fin.lt_def] at hj
    exact ⟨j.val, by simp only [List.length_ofFn]; omega, by simp⟩

section Ring

variable {R : Type*} [CommRing R]

theorem ofList_take_ofFn {d : ℕ} (x : Fin d → R) (i : Fin d) :
    Ideal.ofList ((List.ofFn x).take i.val) = Ideal.span (x '' {j | j < i}) := by
  unfold Ideal.ofList
  congr 1
  ext r
  exact mem_take_ofFn_iff x i r

/-- Weak regularity of `List.ofFn x` on the ring itself, as an ideal-membership condition. -/
theorem isWeaklyRegular_ofFn_iff {d : ℕ} (x : Fin d → R) :
    Sequence.IsWeaklyRegular R (List.ofFn x) ↔
      ∀ (i : Fin d) (z : R), x i * z ∈ Ideal.span (x '' {j | j < i}) →
        z ∈ Ideal.span (x '' {j | j < i}) := by
  rw [Sequence.isWeaklyRegular_iff]
  have key : ∀ (i : Fin d), (Ideal.ofList ((List.ofFn x).take i.val) • ⊤ : Submodule R R) =
      Ideal.span (x '' {j | j < i}) := by
    intro i
    rw [ofList_take_ofFn, Ideal.smul_eq_mul, Ideal.mul_top]
  constructor
  · intro h i z hz
    have hi : i.val < (List.ofFn x).length := by simp
    have h' := h i.val hi
    rw [key i, isSMulRegular_quotient_iff_mem_of_smul_mem] at h'
    simp only [List.getElem_ofFn, smul_eq_mul] at h'
    exact h' z hz
  · intro h i hi
    have hi' : i < d := by simpa using hi
    have h' := h ⟨i, hi'⟩
    rw [key ⟨i, hi'⟩, isSMulRegular_quotient_iff_mem_of_smul_mem]
    simp only [List.getElem_ofFn, smul_eq_mul]
    exact h'

/-- Multiplying the generators by units does not change the ideal they span. -/
theorem span_image_mul_units {d : ℕ} (x u : Fin d → R) (hu : ∀ i, IsUnit (u i))
    (T : Set (Fin d)) :
    Ideal.span ((fun j => u j * x j) '' T) = Ideal.span (x '' T) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨j, hj, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, hj, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨v, hv⟩ := hu j
    have hx : x j = ↑v⁻¹ * (u j * x j) := by
      rw [← hv, ← mul_assoc, Units.inv_mul, one_mul]
    rw [SetLike.mem_coe, hx]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, hj, rfl⟩)

/-- Multiplying the terms of a weakly regular sequence by units keeps it weakly regular. -/
theorem isWeaklyRegular_ofFn_mul_units {d : ℕ} (x u : Fin d → R) (hu : ∀ i, IsUnit (u i))
    (h : Sequence.IsWeaklyRegular R (List.ofFn x)) :
    Sequence.IsWeaklyRegular R (List.ofFn fun i => u i * x i) := by
  rw [isWeaklyRegular_ofFn_iff] at h ⊢
  intro i z hz
  rw [span_image_mul_units x u hu] at hz ⊢
  apply h i
  obtain ⟨v, hv⟩ := hu i
  have hxz : x i * z = ↑v⁻¹ * (u i * x i * z) := by
    rw [← hv, mul_assoc, ← mul_assoc (↑v⁻¹ : R), Units.inv_mul, one_mul]
  rw [hxz]
  exact Ideal.mul_mem_left _ _ hz

/-- If finitely many generators of `K` are each moved into `J` by an element of `S`, then one
element of `S` moves all of `K` into `J`. -/
theorem exists_mem_forall_mul_mem (S : Submonoid R) (K J : Ideal R) (hK : K.FG)
    (h : ∀ x ∈ K, ∃ s ∈ S, s * x ∈ J) : ∃ s ∈ S, ∀ x ∈ K, s * x ∈ J := by
  classical
  obtain ⟨G, rfl⟩ := hK
  choose! t ht using fun g (hg : g ∈ G) => h g (Ideal.subset_span (Finset.mem_coe.mpr hg))
  refine ⟨∏ g ∈ G, t g, prod_mem fun g hg => (ht g hg).1, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨c, hc⟩ : t g ∣ ∏ g ∈ G, t g := Finset.dvd_prod_of_mem t (Finset.mem_coe.mp hg)
    rw [hc, mul_comm (t g) c, mul_assoc]
    exact J.mul_mem_left c (ht g (Finset.mem_coe.mp hg)).2
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact J.add_mem ha hb
  | smul a b _ hb => rw [smul_eq_mul, mul_left_comm]; exact J.mul_mem_left a hb

end Ring

section Localization

variable {A : Type*} [CommRing A] (S : Submonoid A) (B : Type*) [CommRing B] [Algebra A B]
  [IsLocalization S B]

/-- An element whose image lies in `J B` is moved into `J` by an element of `S`. -/
theorem exists_mul_mem_of_algebraMap_mem_map (J : Ideal A) (x : A)
    (hx : algebraMap A B x ∈ J.map (algebraMap A B)) : ∃ s ∈ S, s * x ∈ J := by
  obtain ⟨⟨a, m⟩, hm⟩ := (IsLocalization.mem_map_algebraMap_iff S B).mp hx
  rw [← map_mul] at hm
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists S B).mp hm
  refine ⟨c * m, S.mul_mem c.2 m.2, ?_⟩
  have : (↑c * ↑m : A) * x = ↑c * (a : A) := by rw [← hc]; ring
  rw [this]
  exact J.mul_mem_left _ a.2

end Localization

section Powers

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- From Stacks 07DV: if `x₀, …, x_{d-1}` in the maximal ideal is weakly regular, then `xᵢ` is a
nonzerodivisor modulo `(x_j^e : j < i)`. -/
theorem mem_of_mul_mem_span_pow (hpow : RegularSequencePowersStatement.{u}) {d : ℕ}
    (x : Fin d → R) (hx : ∀ i, x i ∈ maximalIdeal R)
    (hreg : Sequence.IsWeaklyRegular R (List.ofFn x)) (e : ℕ) (he : 0 < e) (i : Fin d)
    (z : R) (hz : x i * z ∈ Ideal.span ((fun j => x j ^ e) '' {j | j < i})) :
    z ∈ Ideal.span ((fun j => x j ^ e) '' {j | j < i}) := by
  have hR : Sequence.IsRegular R (List.ofFn x) :=
    Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R
      (fun r hr => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
        exact hx j) hreg
  let ee : Fin d → ℕ := fun j => if j < i then e else 1
  have hee : ∀ j, 0 < ee j := by
    intro j
    simp only [ee]
    split_ifs <;> omega
  have h2 := ((hpow R R d x ee hee).mp hR).toIsWeaklyRegular
  rw [isWeaklyRegular_ofFn_iff] at h2
  have hspan : Ideal.span ((fun j => x j ^ ee j) '' {j | j < i}) =
      Ideal.span ((fun j => x j ^ e) '' {j | j < i}) := by
    congr 1
    apply Set.image_congr
    intro j hj
    have hj' : j < i := hj
    simp only [ee, hj', ite_true]
  have hi : x i ^ ee i = x i := by simp [ee]
  have key := h2 i z
  rw [hspan, hi] at key
  exact key hz

end Powers

section Main

variable {Λ : Type u} [CommRing Λ] (q : Ideal Λ) [q.IsPrime]

/-- Multiplying the `πᵢ` by elements of `Λ \ q` preserves conditions (1) and (2). -/
theorem span_isWeaklyRegular_mul {d : ℕ} (π s : Fin d → Λ) (hs : ∀ i, s i ∈ q.primeCompl)
    (h : Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (π i)) =
          maximalIdeal (Localization.AtPrime q) ∧
        Sequence.IsWeaklyRegular (Localization.AtPrime q)
          (List.ofFn fun i => algebraMap Λ (Localization.AtPrime q) (π i))) :
    Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (s i * π i)) =
          maximalIdeal (Localization.AtPrime q) ∧
        Sequence.IsWeaklyRegular (Localization.AtPrime q)
          (List.ofFn fun i => algebraMap Λ (Localization.AtPrime q) (s i * π i)) := by
  have hu : ∀ i, IsUnit (algebraMap Λ (Localization.AtPrime q) (s i)) :=
    fun i => IsLocalization.map_units (Localization.AtPrime q) (⟨s i, hs i⟩ : q.primeCompl)
  simp only [map_mul]
  refine ⟨?_, isWeaklyRegular_ofFn_mul_units _ _ hu h.2⟩
  have := span_image_mul_units (fun i => algebraMap Λ (Localization.AtPrime q) (π i))
    (fun i => algebraMap Λ (Localization.AtPrime q) (s i)) hu Set.univ
  simp only [Set.image_univ] at this
  rw [this, h.1]

/-- Steps 1 and 2 of the source proof: elements of `Λ` whose images form a regular sequence
generating the maximal ideal of `Λ_q`, with `πᵢⁿ ∈ I`. -/
theorem exists_initial (I : Ideal Λ) (n : ℕ) (hIq : I ≤ q)
    (hn : (q ^ n).map (algebraMap Λ (Localization.AtPrime q)) ≤
      I.map (algebraMap Λ (Localization.AtPrime q)))
    [IsRegularLocalRing (Localization.AtPrime q)] :
    ∃ π : Fin (maximalIdeal (Localization.AtPrime q)).spanFinrank → Λ,
      (Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (π i)) =
          maximalIdeal (Localization.AtPrime q) ∧
        Sequence.IsWeaklyRegular (Localization.AtPrime q)
          (List.ofFn fun i => algebraMap Λ (Localization.AtPrime q) (π i))) ∧
      ∀ i, π i ^ n ∈ I := by
  obtain ⟨rs, hof, hlen, hw⟩ :=
    RegularFlatLocalAscent.exists_isWeaklyRegular_ofList_eq_maximalIdeal
      (Localization.AtPrime q)
  let y : Fin (maximalIdeal (Localization.AtPrime q)).spanFinrank → Localization.AtPrime q :=
    fun i => rs[i.val]'(by rw [hlen]; exact i.2)
  have hy : List.ofFn y = rs := by
    apply List.ext_getElem (by simp [hlen])
    intro k h1 h2
    simp [y]
  have hyspan : Ideal.span (Set.range y) = maximalIdeal (Localization.AtPrime q) := by
    refine Eq.trans ?_ hof
    unfold Ideal.ofList
    congr 1
    ext r
    rw [Set.mem_range, Set.mem_ofPred_eq, ← hy, List.mem_ofFn]
  -- clear denominators
  choose a b hab using fun i => IsLocalization.exists_mk'_eq q.primeCompl (y i)
  have ha : ∀ i, algebraMap Λ (Localization.AtPrime q) (a i) =
      algebraMap Λ (Localization.AtPrime q) (b i) * y i := by
    intro i
    rw [← hab i, IsLocalization.mk'_spec']
  have hbu : ∀ i, IsUnit (algebraMap Λ (Localization.AtPrime q) (b i)) :=
    fun i => IsLocalization.map_units (Localization.AtPrime q) (b i)
  have h12 : Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (a i)) =
        maximalIdeal (Localization.AtPrime q) ∧
      Sequence.IsWeaklyRegular (Localization.AtPrime q)
        (List.ofFn fun i => algebraMap Λ (Localization.AtPrime q) (a i)) := by
    simp only [ha]
    refine ⟨?_, isWeaklyRegular_ofFn_mul_units y _ hbu (by rw [hy]; exact hw)⟩
    have := span_image_mul_units y (fun i => algebraMap Λ (Localization.AtPrime q) (b i))
      hbu Set.univ
    simp only [Set.image_univ] at this
    rw [this, hyspan]
  -- make the `n`-th powers lie in `I`
  have hpow : ∀ i, ∃ t ∈ q.primeCompl, t * a i ^ n ∈ I := by
    intro i
    apply exists_mul_mem_of_algebraMap_mem_map q.primeCompl (Localization.AtPrime q)
    apply hn
    rw [Ideal.map_pow, map_pow]
    apply Ideal.pow_mem_pow
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q), ← h12.1]
    exact Ideal.subset_span ⟨i, rfl⟩
  choose t ht hti using hpow
  refine ⟨fun i => t i * a i, span_isWeaklyRegular_mul q a t ht h12, fun i => ?_⟩
  cases n with
  | zero =>
    exfalso
    apply ht i
    apply hIq
    simpa using hti i
  | succ k =>
    have : (t i * a i) ^ (k + 1) = t i ^ k * (t i * a i ^ (k + 1)) := by ring
    rw [this]
    exact I.mul_mem_left _ (hti i)

variable [IsNoetherianRing Λ]

/-- Step 3 of the source proof, by induction on the number `k` of indices for which the
annihilator condition already holds. -/
theorem exists_stage (hpow : RegularSequencePowersStatement.{u}) (I : Ideal Λ) (n : ℕ)
    (hIq : I ≤ q)
    (hn : (q ^ n).map (algebraMap Λ (Localization.AtPrime q)) ≤
      I.map (algebraMap Λ (Localization.AtPrime q)))
    [IsRegularLocalRing (Localization.AtPrime q)] (e : ℕ) (he : 0 < e) (k : ℕ) :
    ∃ π : Fin (maximalIdeal (Localization.AtPrime q)).spanFinrank → Λ,
      (Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (π i)) =
          maximalIdeal (Localization.AtPrime q) ∧
        Sequence.IsWeaklyRegular (Localization.AtPrime q)
          (List.ofFn fun i => algebraMap Λ (Localization.AtPrime q) (π i))) ∧
      (∀ i, π i ^ n ∈ I) ∧
      ∀ i : Fin (maximalIdeal (Localization.AtPrime q)).spanFinrank, i.val < k →
        ∀ x : Λ, π i ^ 2 * x ∈ Ideal.span ((fun j => π j ^ e) '' {j | j < i}) →
          π i * x ∈ Ideal.span ((fun j => π j ^ e) '' {j | j < i}) := by
  induction k with
  | zero =>
    obtain ⟨π, h12, h3⟩ := exists_initial q I n hIq hn
    exact ⟨π, h12, h3, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨π, h12, h3, h4⟩ := ih
    by_cases hk : k < (maximalIdeal (Localization.AtPrime q)).spanFinrank
    swap
    · exact ⟨π, h12, h3, fun i hi => h4 i (by have := i.2; omega)⟩
    let i₀ : Fin (maximalIdeal (Localization.AtPrime q)).spanFinrank := ⟨k, hk⟩
    let J : Ideal Λ := Ideal.span ((fun j => π j ^ e) '' {j | j < i₀})
    obtain ⟨s₀, hs₀, hs₀J⟩ := exists_mem_forall_mul_mem q.primeCompl
      ((J.map (algebraMap Λ (Localization.AtPrime q))).comap
        (algebraMap Λ (Localization.AtPrime q))) J (IsNoetherian.noetherian _)
      (fun x hx => exists_mul_mem_of_algebraMap_mem_map q.primeCompl
        (Localization.AtPrime q) J x hx)
    let s : Fin (maximalIdeal (Localization.AtPrime q)).spanFinrank → Λ :=
      fun j => if j = i₀ then s₀ else 1
    have hs : ∀ j, s j ∈ q.primeCompl := by
      intro j
      simp only [s]
      split_ifs
      · exact hs₀
      · exact q.primeCompl.one_mem
    have hsne : ∀ j, j ≠ i₀ → s j * π j = π j := by
      intro j hj
      simp [s, hj]
    have hseq : s i₀ * π i₀ = s₀ * π i₀ := by simp [s]
    refine ⟨fun j => s j * π j, span_isWeaklyRegular_mul q π s hs h12, fun j => ?_, ?_⟩
    · rw [mul_pow]
      exact I.mul_mem_left _ (h3 j)
    intro i hi x hx
    have hspan : ∀ i : Fin (maximalIdeal (Localization.AtPrime q)).spanFinrank, i ≤ i₀ →
        Ideal.span ((fun j => (s j * π j) ^ e) '' {j | j < i}) =
          Ideal.span ((fun j => π j ^ e) '' {j | j < i}) := by
      intro i hi
      congr 1
      apply Set.image_congr
      intro j hj
      have hj' : j < i := hj
      show (s j * π j) ^ e = π j ^ e
      rw [hsne j (ne_of_lt (lt_of_lt_of_le hj' hi))]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · -- an index already treated: nothing changes
      have hlt' : i < i₀ := hlt
      try simp only at hx ⊢
      rw [hspan i (le_of_lt hlt'), hsne i (ne_of_lt hlt')] at hx ⊢
      exact h4 i hlt x hx
    · -- the new index `i₀`
      have hii : i = i₀ := Fin.ext heq
      rw [hii] at hx ⊢
      try simp only at hx ⊢
      rw [hspan i₀ le_rfl, hseq] at hx ⊢
      have hmax : ∀ j, algebraMap Λ (Localization.AtPrime q) (π j) ∈
          maximalIdeal (Localization.AtPrime q) := by
        intro j
        rw [← h12.1]
        exact Ideal.subset_span ⟨j, rfl⟩
      have hJmap : J.map (algebraMap Λ (Localization.AtPrime q)) =
          Ideal.span ((fun j => (algebraMap Λ (Localization.AtPrime q) (π j)) ^ e) ''
            {j | j < i₀}) := by
        simp only [J]
        rw [Ideal.map_span, Set.image_image]
        simp only [map_pow]
      have hz : algebraMap Λ (Localization.AtPrime q) (π i₀) *
          algebraMap Λ (Localization.AtPrime q) (s₀ ^ 2 * (π i₀ * x)) ∈
            J.map (algebraMap Λ (Localization.AtPrime q)) := by
        rw [← map_mul]
        apply Ideal.mem_map_of_mem
        have : π i₀ * (s₀ ^ 2 * (π i₀ * x)) = (s₀ * π i₀) ^ 2 * x := by ring
        rw [this]
        exact hx
      rw [hJmap] at hz
      have hz' := mem_of_mul_mem_span_pow hpow
        (fun j => algebraMap Λ (Localization.AtPrime q) (π j)) hmax h12.2 e he i₀ _ hz
      rw [map_mul] at hz'
      have hunit : IsUnit (algebraMap Λ (Localization.AtPrime q) (s₀ ^ 2)) :=
        IsLocalization.map_units (Localization.AtPrime q)
          (⟨s₀ ^ 2, pow_mem hs₀ 2⟩ : q.primeCompl)
      have hmem : π i₀ * x ∈ (J.map (algebraMap Λ (Localization.AtPrime q))).comap
          (algebraMap Λ (Localization.AtPrime q)) := by
        rw [Ideal.mem_comap, hJmap]
        exact (Ideal.unit_mul_mem_iff_mem _ hunit).mp hz'
      rw [mul_assoc]
      exact hs₀J _ hmem

end Main

end RegularParameterChoice

/-- Stacks Lemma 16.10.2 (07FD), assuming Stacks Lemma 10.68.9 (07DV) on powers of regular
sequences. -/
theorem regularParameterChoice_of_powers (hpow : RegularSequencePowersStatement.{u}) :
    RegularParameterChoiceStatement.{u} := by
  intro Λ _ _ I q _ n hIq hn hreg e he
  obtain ⟨π, h12, h3, h4⟩ := RegularParameterChoice.exists_stage q hpow I n hIq hn e he
    (maximalIdeal (Localization.AtPrime q)).spanFinrank
  exact ⟨π, h12.1, h12.2, h3, fun i x hx => h4 i i.2 x hx⟩

/-- Stacks Lemma 16.10.2 (07FD): choice of regular parameters with annihilator conditions. -/
theorem regularParameterChoice : RegularParameterChoiceStatement.{u} :=
  regularParameterChoice_of_powers regularSequencePowers

end Langlands.CommutativeAlgebra.Popescu
