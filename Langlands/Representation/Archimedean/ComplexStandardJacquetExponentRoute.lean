import Langlands.Representation.Archimedean.ComplexStandardHomExponentJacquetReduction
import Langlands.Representation.Archimedean.ComplexJacquetTorus

/-!
# A route to the exponent shape of Jacquet functionals on complex principal series

Three statements about the `U(n)`-finite principal series `X(d)` of `GL_n(ℂ)` and the proved
implication `CO → Trans → Bound → JE`, where JE is the Library's
`ComplexStandardJacquetExponentStatement`.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

/-- **Casselman–Osborne for complex principal series.** The holomorphic and antiholomorphic
coordinates of the exponents of a nonzero Jacquet functional on `X(d)` are permutations of
those of `d`: with `p(e) = t(e) + l(e)/2` and `q(e) = t(e) - l(e)/2`, there are permutations
`α`, `β` with `a_j = p(d_{α j}) + q(d_{β j}) + (n - 1) - 2j` and
`b_j = i (p(d_{α j}) - q(d_{β j}))`. -/
def ComplexJacquetCasselmanOsborneStatement : Prop :=
  ∀ (n : ℕ) (d : Fin n → ComplexCharacterData)
    (ℓ : kFiniteFunctions (complexStandardModule n (List.ofFn d)) (unitaryCompact ℂ n) →ₗ[ℂ] ℂ)
    (a b : Fin n → ℂ),
    ℓ ≠ 0 → IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn d)) ℓ a b →
      ∃ α β : Equiv.Perm (Fin n), ∀ j : Fin n,
        a j = ((d (α j)).exponent + ((d (α j)).weight : ℂ) / 2) +
            ((d (β j)).exponent - ((d (β j)).weight : ℂ) / 2) + ((n : ℂ) - 1) -
              2 * ((j : ℕ) : ℂ) ∧
          b j = Complex.I * (((d (α j)).exponent + ((d (α j)).weight : ℂ) / 2) -
            ((d (β j)).exponent - ((d (β j)).weight : ℂ) / 2))

/-- **Translation by an exterior power.** Let `ℓ ≠ 0` be a Jacquet functional on `X(d)` with
exponents `(a, b)`, let `k ≤ n` and `ε = ±1`. Then for some `k`-element set `S` of positions,
the characters `d'` obtained from `d` by adding `1` to the holomorphic coordinate `p` (if
`ε = 1`) or to the antiholomorphic coordinate `q` (if `ε = -1`) at the positions in `S` carry a
nonzero Jacquet functional with exponents `a_j + λ_j` and `b_j + i ε λ_j`, where `λ` is the
indicator of the last `k` positions (the lowest weight of `Λ^k ℂ^n`). -/
def ComplexJacquetTranslationStatement : Prop :=
  ∀ (n : ℕ) (d : Fin n → ComplexCharacterData)
    (ℓ : kFiniteFunctions (complexStandardModule n (List.ofFn d)) (unitaryCompact ℂ n) →ₗ[ℂ] ℂ)
    (a b : Fin n → ℂ),
    ℓ ≠ 0 → IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn d)) ℓ a b →
    ∀ (k : ℕ) (ε : ℤ), k ≤ n → (ε = 1 ∨ ε = -1) →
      ∃ (S : Finset (Fin n)) (d' : Fin n → ComplexCharacterData)
        (ℓ' : kFiniteFunctions (complexStandardModule n (List.ofFn d')) (unitaryCompact ℂ n)
          →ₗ[ℂ] ℂ),
        S.card = k ∧
        (∀ j, (d' j).weight = (d j).weight + if j ∈ S then ε else 0) ∧
        (∀ j, (d' j).exponent = (d j).exponent + if j ∈ S then (1 / 2 : ℂ) else 0) ∧
        ℓ' ≠ 0 ∧
        IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn d')) ℓ'
          (fun j => a j + if n ≤ (j : ℕ) + k then 1 else 0)
          (fun j => b j + Complex.I * (ε : ℂ) * if n ≤ (j : ℕ) + k then 1 else 0)

/-- **Weight bound for antidominant exponents.** Let `ℓ ≠ 0` be a Jacquet functional on `X(d)`
with exponents `(a, b)`, `b_j = i w_j` with integers `w_j ≤ 0` that do not increase with `j`,
and `Re a_j + 2j` strictly increasing in `j`. Then `∑_j |l(d_j)| ≤ ∑_j |w_j|`. -/
def ComplexJacquetAntidominantBoundStatement : Prop :=
  ∀ (n : ℕ) (d : Fin n → ComplexCharacterData)
    (ℓ : kFiniteFunctions (complexStandardModule n (List.ofFn d)) (unitaryCompact ℂ n) →ₗ[ℂ] ℂ)
    (a b : Fin n → ℂ) (w : Fin n → ℤ),
    ℓ ≠ 0 → IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn d)) ℓ a b →
    (∀ j, b j = Complex.I * (w j : ℂ)) → (∀ j, w j ≤ 0) → (∀ i j : Fin n, i ≤ j → w j ≤ w i) →
    (∀ i j : Fin n, i < j → (a i).re + 2 * ((i : ℕ) : ℝ) < (a j).re + 2 * ((j : ℕ) : ℝ)) →
      ∑ j, |(d j).weight| ≤ ∑ j, |w j|

/-- The three statements imply the exponent shape of Jacquet functionals (JE). -/
def ComplexStandardJacquetExponentRouteStatement : Prop :=
  ComplexJacquetCasselmanOsborneStatement → ComplexJacquetTranslationStatement →
    ComplexJacquetAntidominantBoundStatement → ComplexStandardJacquetExponentStatement

namespace JacquetExponentRoute

/-! ## The cone of nonnegative simple-root combinations -/

section Cone

variable {n : ℕ}

theorem cone_zero : IsNonnegSimpleRootCombination (0 : Fin n → ℤ) := by
  refine ⟨fun k => ?_, ?_⟩ <;> simp

theorem cone_add {u u' : Fin n → ℤ}
    (hu : IsNonnegSimpleRootCombination u) (hu' : IsNonnegSimpleRootCombination u') :
    IsNonnegSimpleRootCombination (fun j => u j + u' j) := by
  refine ⟨fun k => ?_, ?_⟩
  · simp only [Finset.sum_add_distrib]
    exact add_nonneg (hu.1 k) (hu'.1 k)
  · simp only [Finset.sum_add_distrib, hu.2, hu'.2, add_zero]

/-- The indicator of a `k`-element set minus the indicator of the last `k` positions lies in
the cone. -/
theorem cone_indicator (T : Finset (Fin n)) {k : ℕ} (hT : T.card = k) :
    IsNonnegSimpleRootCombination
      (fun j : Fin n => (if j ∈ T then 1 else 0 : ℤ) - if n ≤ (j : ℕ) + k then 1 else 0) := by
  classical
  have hkn : k ≤ n := by
    rw [← hT]; simpa using T.card_le_univ
  -- cardinality of `{j | j < m}` and of its complement
  have hlt : ∀ m : ℕ, (Finset.univ.filter (fun j : Fin n => (j : ℕ) < m)).card = min n m :=
    fun m => Fin.card_filter_val_lt
  have hge : ∀ m : ℕ, (Finset.univ.filter (fun j : Fin n => ¬ (j : ℕ) < m)).card = n - min n m := by
    intro m
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun j : Fin n => (j : ℕ) < m)
    rw [Finset.card_univ, Fintype.card_fin, hlt m] at this
    omega
  -- the last `k` positions
  have htop : ∀ m : ℕ, (Finset.univ.filter
      (fun j : Fin n => (j : ℕ) < m ∧ n ≤ (j : ℕ) + k)).card = min n m - min m (n - k) := by
    intro m
    have h1 := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun j : Fin n => (j : ℕ) < m)) (fun j : Fin n => n ≤ (j : ℕ) + k)
    rw [Finset.filter_filter, Finset.filter_filter, hlt m] at h1
    have h2 : (Finset.univ.filter (fun j : Fin n => (j : ℕ) < m ∧ ¬ n ≤ (j : ℕ) + k)) =
        Finset.univ.filter (fun j : Fin n => (j : ℕ) < min m (n - k)) := by
      apply Finset.filter_congr
      intro j _
      constructor
      · rintro ⟨h1, h2⟩; omega
      · intro h; omega
    rw [h2, Fin.card_filter_val_lt] at h1
    have : min n (min m (n - k)) = min m (n - k) := by omega
    omega
  refine ⟨fun m => ?_, ?_⟩
  · simp only [Finset.sum_sub_distrib]
    rw [Finset.sum_boole, Finset.sum_boole, Finset.filter_filter, Finset.filter_filter]
    have hT1 := Finset.card_filter_add_card_filter_not (s := T)
      (fun j : Fin n => (j : ℕ) < m)
    have hT2 : (T.filter (fun j : Fin n => ¬ (j : ℕ) < m)).card ≤ n - min n m := by
      rw [← hge m]
      exact Finset.card_le_card (Finset.monotone_filter_left _ (Finset.subset_univ T))
    have hT3 : (T.filter (fun j : Fin n => ¬ (j : ℕ) < m)).card ≤ k := by
      rw [← hT]; exact Finset.card_filter_le _ _
    have hT4 : (Finset.univ.filter (fun j : Fin n => (j : ℕ) < m ∧ j ∈ T)) =
        T.filter (fun j : Fin n => (j : ℕ) < m) := by
      ext j; simp [and_comm]
    rw [hT4, htop m]
    have : ((T.filter (fun j : Fin n => (j : ℕ) < m)).card : ℤ) ≥ (min n m - min m (n - k) : ℕ) := by
      have : min n m - min m (n - k) ≤ (T.filter (fun j : Fin n => (j : ℕ) < m)).card := by omega
      exact_mod_cast this
    simp only [ge_iff_le] at this ⊢
    linarith
  · simp only [Finset.sum_sub_distrib]
    rw [Finset.sum_boole, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, hT]
    have h := htop n
    rw [show (Finset.univ.filter (fun j : Fin n => (j : ℕ) < n ∧ n ≤ (j : ℕ) + k)) =
      Finset.univ.filter (fun j : Fin n => n ≤ (j : ℕ) + k) from
        Finset.filter_congr (fun j _ => ⟨fun h => h.2, fun h => ⟨j.2, h⟩⟩)] at h
    rw [h]
    have : min n n - min n (n - k) = k := by omega
    rw [this]
    simp

/-- For a monotone `lam : Fin n → ℕ`, the positions where `lam` is positive are the last `k` of
them, `k` being their number. -/
theorem pos_iff_of_monotone {lam : Fin n → ℕ} (hlam : Monotone lam) (j : Fin n) :
    0 < lam j ↔ n ≤ (j : ℕ) + (Finset.univ.filter (fun i : Fin n => 0 < lam i)).card := by
  classical
  set k := (Finset.univ.filter (fun i : Fin n => 0 < lam i)).card with hk
  have hcompl : (Finset.univ.filter (fun i : Fin n => ¬ 0 < lam i)).card = n - k := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i : Fin n => 0 < lam i)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  constructor
  · intro hj
    -- every `i ≥ j` is positive, so the zero set lies below `j`
    have hsub : Finset.univ.filter (fun i : Fin n => ¬ 0 < lam i) ⊆
        Finset.univ.filter (fun i : Fin n => (i : ℕ) < j) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Nat.le_zero] at hi ⊢
      by_contra hij
      have : lam j ≤ lam i := hlam (Fin.le_iff_val_le_val.mpr (by omega))
      omega
    have := Finset.card_le_card hsub
    rw [hcompl, Fin.card_filter_val_lt] at this
    have : (j : ℕ) < n := j.2
    omega
  · intro hj
    by_contra h0
    have h0' : lam j = 0 := by omega
    -- every `i ≤ j` is zero
    have hsub : Finset.univ.filter (fun i : Fin n => (i : ℕ) < (j : ℕ) + 1) ⊆
        Finset.univ.filter (fun i : Fin n => ¬ 0 < lam i) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have : lam i ≤ lam j := hlam (Fin.le_iff_val_le_val.mpr (by omega))
      omega
    have := Finset.card_le_card hsub
    rw [hcompl, Fin.card_filter_val_lt] at this
    have : (j : ℕ) < n := j.2
    have hkn : k ≤ n := by
      rw [hk]; simpa using (Finset.univ.filter (fun i : Fin n => 0 < lam i)).card_le_univ
    omega

end Cone

/-! ## Iterated translation -/

section Translate

/-- Iterating the translation statement along a monotone vector `lam : Fin n → ℕ` (a sum of
indicators of final segments): the exponents move by `lam` (and `i ε lam`), and the holomorphic
(`ε = 1`) or antiholomorphic (`ε = -1`) coordinates of the characters move by some `μ` with
`σ·μ - lam` in the cone for every permutation `σ`. -/
theorem translate_mono (hTr : ComplexJacquetTranslationStatement) {n : ℕ} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) :
    ∀ (N : ℕ) (lam : Fin n → ℕ), Monotone lam → ∑ j, lam j = N →
    ∀ (d : Fin n → ComplexCharacterData)
      (ℓ : kFiniteFunctions (complexStandardModule n (List.ofFn d)) (unitaryCompact ℂ n)
        →ₗ[ℂ] ℂ) (a b : Fin n → ℂ), ℓ ≠ 0 →
      IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn d)) ℓ a b →
      ∃ (d' : Fin n → ComplexCharacterData)
        (ℓ' : kFiniteFunctions (complexStandardModule n (List.ofFn d')) (unitaryCompact ℂ n)
          →ₗ[ℂ] ℂ) (μ : Fin n → ℕ),
        ℓ' ≠ 0 ∧
        IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn d')) ℓ'
          (fun j => a j + (lam j : ℂ)) (fun j => b j + Complex.I * (ε : ℂ) * (lam j : ℂ)) ∧
        (∀ j, (d' j).weight = (d j).weight + ε * (μ j : ℤ)) ∧
        (∀ j, (d' j).exponent = (d j).exponent + (μ j : ℂ) / 2) ∧
        ∀ σ : Equiv.Perm (Fin n),
          IsNonnegSimpleRootCombination (fun j => (μ (σ j) : ℤ) - (lam j : ℤ)) := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro lam hlam hsum d ℓ a b hℓ hJ
  set k := (Finset.univ.filter (fun i : Fin n => 0 < lam i)).card with hk
  by_cases hk0 : k = 0
  · -- `lam = 0`
    have hl0 : ∀ j, lam j = 0 := by
      intro j
      by_contra h
      have := (pos_iff_of_monotone hlam j).mp (by omega)
      rw [← hk, hk0] at this
      have : (j : ℕ) < n := j.2
      omega
    refine ⟨d, ℓ, fun _ => 0, hℓ, ?_, fun j => by simp, fun j => by simp, fun σ => ?_⟩
    · simpa [hl0] using hJ
    · refine ⟨fun m => ?_, ?_⟩ <;> simp [hl0]
  · have hkn : k ≤ n := by
      rw [hk]; simpa using (Finset.univ.filter (fun i : Fin n => 0 < lam i)).card_le_univ
    obtain ⟨S, d₁, ℓ₁, hS, hw₁, he₁, hℓ₁, hJ₁⟩ := hTr n d ℓ a b hℓ hJ k ε hkn hε
    set lam' : Fin n → ℕ := fun j => lam j - if n ≤ (j : ℕ) + k then 1 else 0 with hlam'
    have hpos := pos_iff_of_monotone hlam
    have hlam'm : Monotone lam' := by
      intro i j hij
      have hij' : (i : ℕ) ≤ j := hij
      have := hlam hij
      have hi := hpos i
      have hj := hpos j
      simp only [hlam', ← hk] at hi hj ⊢
      split_ifs <;> omega
    have hsum' : ∑ j, lam' j + k = N := by
      rw [← hsum]
      have : ∀ j, lam' j + (if n ≤ (j : ℕ) + k then 1 else 0) = lam j := by
        intro j
        have := hpos j
        simp only [hlam', ← hk] at this ⊢
        split_ifs <;> omega
      rw [← Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_boole, Nat.cast_id, hk]
      congr 1
      exact Finset.filter_congr (fun j _ => hpos j)
    have hlt : ∑ j, lam' j < N := by
      have : 0 < k := Nat.pos_of_ne_zero hk0
      omega
    obtain ⟨d', ℓ', μ', hℓ', hJ', hw', he', hcone'⟩ :=
      ih _ hlt lam' hlam'm rfl d₁ ℓ₁ _ _ hℓ₁ hJ₁
    refine ⟨d', ℓ', fun j => μ' j + if j ∈ S then 1 else 0, hℓ', ?_, fun j => ?_, fun j => ?_,
      fun σ => ?_⟩
    · have hadd : ∀ j : Fin n, ((lam' j : ℕ) : ℂ) + (if n ≤ (j : ℕ) + k then 1 else 0) =
          (lam j : ℂ) := by
        intro j
        have := hpos j
        simp only [hlam', ← hk] at this ⊢
        split_ifs with h
        · have : 1 ≤ lam j := by omega
          push_cast [Nat.cast_sub this]
          ring
        · have : lam j = 0 := by omega
          simp [this]
      convert hJ' using 2 with j j
      · rw [← hadd j]; ring
      · rw [← hadd j]; ring
    · rw [hw', hw₁ j]
      by_cases h : j ∈ S <;> simp [h]; ring
    · rw [he', he₁ j]
      by_cases h : j ∈ S <;> simp [h]; ring
    · have h1 := hcone' σ
      have h2 := cone_indicator (S.map σ.symm.toEmbedding) (k := k) (by rw [Finset.card_map, hS])
      have := cone_add h1 h2
      convert this using 2 with j
      simp only [Finset.mem_map_equiv, Equiv.symm_symm]
      have hj' : 0 < lam j ↔ n ≤ (j : ℕ) + k := hpos j
      simp only [hlam']
      by_cases hS' : σ j ∈ S <;> by_cases hn : n ≤ (j : ℕ) + k <;>
        simp only [hS', hn, ite_true, ite_false] <;> push_cast <;> omega

end Translate

end JacquetExponentRoute

open JacquetExponentRoute in
/-- **Proof of the route.** -/
theorem complexStandardJacquetExponentRoute : ComplexStandardJacquetExponentRouteStatement := by
  classical
  intro hCO hTr hB n d ℓ a b hℓ hJ
  obtain ⟨w0, hw0, -⟩ :=
    hJ.exists_weight (isComplexGKModule_complexStandardModule n (List.ofFn d)) hℓ
  -- constants independent of the size `M` of the translation
  set K : ℕ := ∑ i : Fin n, ∑ j : Fin n, (w0 i - w0 j).natAbs with hK
  set C : ℕ := ∑ j : Fin n, (w0 j).natAbs with hC
  set ψ : Fin n → ℤ := fun j => w0 j + (K : ℤ) * ((j : ℕ) : ℤ) + C with hψ
  have hdiff : ∀ i j : Fin n, (w0 i - w0 j).natAbs ≤ K := fun i j =>
    (Finset.single_le_sum (f := fun j => (w0 i - w0 j).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j : Fin n, (w0 i - w0 j).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hCj : ∀ j : Fin n, (w0 j).natAbs ≤ C := fun j =>
    Finset.single_le_sum (f := fun j => (w0 j).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  have hψnn : ∀ j, 0 ≤ ψ j := by
    intro j
    have := hCj j
    simp only [hψ]
    have : -(C : ℤ) ≤ w0 j := by omega
    have : 0 ≤ (K : ℤ) * ((j : ℕ) : ℤ) := by positivity
    omega
  have hψmono : ∀ i j : Fin n, i ≤ j → ψ i ≤ ψ j := by
    intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    rcases Nat.eq_or_lt_of_le hij' with h | h
    · rw [Fin.ext h]
    · have := hdiff i j
      simp only [hψ]
      have h1 : ((K : ℤ) * ((i : ℕ) : ℤ)) + K ≤ (K : ℤ) * ((j : ℕ) : ℤ) := by
        have : ((i : ℕ) : ℤ) + 1 ≤ ((j : ℕ) : ℤ) := by exact_mod_cast h
        nlinarith
      omega
  set ψN : Fin n → ℕ := fun j => (ψ j).toNat with hψN
  have hψN' : ∀ j, ((ψN j : ℕ) : ℤ) = ψ j := fun j => Int.toNat_of_nonneg (hψnn j)
  -- the holomorphic and antiholomorphic coordinates of the exponents of `ℓ`
  set A : Fin n → ℂ := fun j => (a j - ((n : ℂ) - 1) + 2 * ((j : ℕ) : ℂ) + (w0 j : ℂ)) / 2
    with hA
  set Bq : Fin n → ℂ := fun j => (a j - ((n : ℂ) - 1) + 2 * ((j : ℕ) : ℂ) - (w0 j : ℂ)) / 2
    with hBq
  set B₁ : ℝ := ∑ i : Fin n, ∑ j : Fin n, |(a i).re - (a j).re| with hB₁
  set B₂ : ℝ := ∑ i : Fin n, ∑ y : Fin n, ‖A i - Bq y - (ψ y : ℂ)‖ with hB₂
  set D : ℤ := ∑ j : Fin n, ((K : ℤ) * ((j : ℕ) : ℤ) + C) with hD
  have hB₁nn : 0 ≤ B₁ := by positivity
  have hB₂nn : 0 ≤ B₂ := by positivity
  have hDnn : (0 : ℝ) ≤ D := by
    have : (0 : ℤ) ≤ D := Finset.sum_nonneg (fun j _ => by positivity)
    exact_mod_cast this
  set M : ℕ := ⌈B₁ + (D : ℝ) + B₂⌉₊ + 1 with hMdef
  have hM : B₁ + (D : ℝ) + B₂ < M := by
    have := Nat.le_ceil (B₁ + (D : ℝ) + B₂)
    simp only [hMdef, Nat.cast_add, Nat.cast_one]
    linarith
  have hre : ∀ i j : Fin n, |(a i).re - (a j).re| ≤ B₁ := fun i j =>
    (Finset.single_le_sum (f := fun j => |(a i).re - (a j).re|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j : Fin n, |(a i).re - (a j).re|)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i))
  -- translate holomorphically by `M ρ'` and antiholomorphically by `M ρ' + ψ`
  have hmono₁ : Monotone (fun j : Fin n => M * (j : ℕ)) := fun i j hij =>
    Nat.mul_le_mul_left _ hij
  have hmono₂ : Monotone (fun j : Fin n => M * (j : ℕ) + ψN j) := by
    intro i j hij
    have h1 : M * (i : ℕ) ≤ M * (j : ℕ) := Nat.mul_le_mul_left _ hij
    have h2 : ψN i ≤ ψN j := by
      have := hψmono i j hij
      have h3 := hψN' i
      have h4 := hψN' j
      omega
    show M * (i : ℕ) + ψN i ≤ M * (j : ℕ) + ψN j
    omega
  obtain ⟨d₁, ℓ₁, μ₁, hℓ₁, hJ₁, hw₁, he₁, hc₁⟩ :=
    translate_mono hTr (ε := 1) (Or.inl rfl) _ _ hmono₁ rfl d ℓ a b hℓ hJ
  obtain ⟨d₂, ℓ₂, μ₂, hℓ₂, hJ₂, hw₂, he₂, hc₂⟩ :=
    translate_mono hTr (ε := -1) (Or.inr rfl) _ _ hmono₂ rfl d₁ ℓ₁ _ _ hℓ₁ hJ₁
  set a₂ : Fin n → ℂ := fun j => (a j + ((M * (j : ℕ) : ℕ) : ℂ)) +
    ((M * (j : ℕ) + ψN j : ℕ) : ℂ) with ha₂
  set b₂ : Fin n → ℂ := fun j => (b j + Complex.I * ((1 : ℤ) : ℂ) * ((M * (j : ℕ) : ℕ) : ℂ)) +
    Complex.I * ((-1 : ℤ) : ℂ) * ((M * (j : ℕ) + ψN j : ℕ) : ℂ) with hb₂
  have hb₂w : ∀ j, b₂ j = Complex.I * ((w0 j - ψ j : ℤ) : ℂ) := by
    intro j
    simp only [hb₂, hw0 j]
    have := hψN' j
    have h' : ((ψN j : ℕ) : ℂ) = ((ψ j : ℤ) : ℂ) := by exact_mod_cast this
    push_cast
    rw [h']
    ring
  have ha₂ψ : ∀ j : Fin n, a₂ j = a j + 2 * (M : ℂ) * ((j : ℕ) : ℂ) + ((ψ j : ℤ) : ℂ) := by
    intro j
    simp only [ha₂]
    have h' : ((ψN j : ℕ) : ℂ) = ((ψ j : ℤ) : ℂ) := by exact_mod_cast hψN' j
    push_cast
    rw [h']
    ring
  have hJ₂' : IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn d₂)) ℓ₂ a₂ b₂ := hJ₂
  -- the weight bound at the translated parameter
  have hbound := hB n d₂ ℓ₂ a₂ b₂ (fun j => w0 j - ψ j) hℓ₂ hJ₂' hb₂w
    (fun j => by
      simp only [hψ]
      have : 0 ≤ (K : ℤ) * ((j : ℕ) : ℤ) := by positivity
      omega)
    (fun i j hij => by
      have hij' : ((i : ℕ) : ℤ) ≤ ((j : ℕ) : ℤ) := by exact_mod_cast hij
      simp only [hψ]
      have : (K : ℤ) * ((i : ℕ) : ℤ) ≤ (K : ℤ) * ((j : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left hij' (by positivity)
      omega)
    (fun i j hij => by
      rw [ha₂ψ i, ha₂ψ j]
      have hij' : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
        have : (i : ℕ) + 1 ≤ (j : ℕ) := hij
        exact_mod_cast this
      have hψij : ((ψ i : ℤ) : ℝ) ≤ ((ψ j : ℤ) : ℝ) := by exact_mod_cast hψmono i j hij.le
      have hai := (abs_le.mp (hre i j)).2
      have hM0 : (0 : ℝ) ≤ M := by positivity
      simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        Complex.intCast_re, Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero]
      nlinarith)
  have hD : ∑ j : Fin n, |w0 j - ψ j| = D := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hψ]
    have : 0 ≤ (K : ℤ) * ((j : ℕ) : ℤ) + C := by positivity
    rw [show w0 j - (w0 j + (K : ℤ) * ((j : ℕ) : ℤ) + C) = -((K : ℤ) * ((j : ℕ) : ℤ) + C) by ring,
      abs_neg, abs_of_nonneg this]
  rw [hD] at hbound
  -- Casselman–Osborne at the translated parameter
  obtain ⟨α, β, hαβ⟩ := hCO n d₂ ℓ₂ a₂ b₂ hℓ₂ hJ₂'
  have hp : ∀ j : Fin n, (d₂ (α j)).exponent + ((d₂ (α j)).weight : ℂ) / 2 =
      A j + (M : ℂ) * ((j : ℕ) : ℂ) := by
    intro j
    have h1 := (hαβ j).1
    have h2 := (hαβ j).2
    rw [hb₂w j] at h2
    have h2' := mul_left_cancel₀ Complex.I_ne_zero h2
    have h3 := ha₂ψ j
    simp only [hA]
    push_cast at h2' ⊢
    linear_combination (-1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2' + (1 / 2 : ℂ) * h3
  have hq : ∀ j : Fin n, (d₂ (β j)).exponent - ((d₂ (β j)).weight : ℂ) / 2 =
      Bq j + (M : ℂ) * ((j : ℕ) : ℂ) + ((ψ j : ℤ) : ℂ) := by
    intro j
    have h1 := (hαβ j).1
    have h2 := (hαβ j).2
    rw [hb₂w j] at h2
    have h2' := mul_left_cancel₀ Complex.I_ne_zero h2
    have h3 := ha₂ψ j
    simp only [hBq]
    push_cast at h2' ⊢
    linear_combination (-1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2' + (1 / 2 : ℂ) * h3
  -- the weights of the translated characters
  have hwt : ∀ x : Fin n, ((d₂ x).weight : ℂ) =
      (M : ℂ) * (((α.symm x : ℕ) : ℂ) - ((β.symm x : ℕ) : ℂ)) +
        (A (α.symm x) - Bq (β.symm x) - ((ψ (β.symm x) : ℤ) : ℂ)) := by
    intro x
    have h1 := hp (α.symm x)
    have h2 := hq (β.symm x)
    rw [Equiv.apply_symm_apply] at h1 h2
    linear_combination h1 - h2
  -- one permutation for both coordinates
  have hαβeq : α = β := by
    by_contra hne
    obtain ⟨x₀, hx₀⟩ : ∃ x, α.symm x ≠ β.symm x := by
      by_contra h
      push Not at h
      have : α.symm = β.symm := Equiv.ext h
      exact hne (by simpa using congrArg Equiv.symm this)
    set E : Fin n → Fin n → ℂ := fun i y => A i - Bq y - ((ψ y : ℤ) : ℂ) with hE
    have hlow : ∀ x : Fin n, (M : ℝ) * |((α.symm x : ℕ) : ℝ) - ((β.symm x : ℕ) : ℝ)| -
        ‖E (α.symm x) (β.symm x)‖ ≤ |((d₂ x).weight : ℝ)| := by
      intro x
      have hw := hwt x
      have hn1 : ‖((d₂ x).weight : ℂ)‖ = |((d₂ x).weight : ℝ)| := by
        rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      have hn2 : ‖(M : ℂ) * (((α.symm x : ℕ) : ℂ) - ((β.symm x : ℕ) : ℂ))‖ =
          (M : ℝ) * |((α.symm x : ℕ) : ℝ) - ((β.symm x : ℕ) : ℝ)| := by
        have : (M : ℂ) * (((α.symm x : ℕ) : ℂ) - ((β.symm x : ℕ) : ℂ)) =
            (((M : ℝ) * (((α.symm x : ℕ) : ℝ) - ((β.symm x : ℕ) : ℝ)) : ℝ) : ℂ) := by
          push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
      have htri := norm_sub_le ((d₂ x).weight : ℂ) (E (α.symm x) (β.symm x))
      rw [hw, show (M : ℂ) * (((α.symm x : ℕ) : ℂ) - ((β.symm x : ℕ) : ℂ)) +
          (A (α.symm x) - Bq (β.symm x) - ((ψ (β.symm x) : ℤ) : ℂ)) -
            E (α.symm x) (β.symm x) = (M : ℂ) * (((α.symm x : ℕ) : ℂ) - ((β.symm x : ℕ) : ℂ))
          by simp [hE]] at htri
      rw [hn2, ← hw, hn1] at htri
      linarith
    have hsumE : ∑ x : Fin n, ‖E (α.symm x) (β.symm x)‖ ≤ B₂ := by
      calc ∑ x : Fin n, ‖E (α.symm x) (β.symm x)‖
          ≤ ∑ x : Fin n, ∑ y : Fin n, ‖E (α.symm x) y‖ :=
            Finset.sum_le_sum (fun x _ => Finset.single_le_sum
              (f := fun y => ‖E (α.symm x) y‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _))
        _ = ∑ i : Fin n, ∑ y : Fin n, ‖E i y‖ :=
            Equiv.sum_comp α.symm (fun i => ∑ y : Fin n, ‖E i y‖)
        _ = B₂ := rfl
    have hsumM : (M : ℝ) ≤ ∑ x : Fin n,
        (M : ℝ) * |((α.symm x : ℕ) : ℝ) - ((β.symm x : ℕ) : ℝ)| := by
      have h1 : (1 : ℝ) ≤ |((α.symm x₀ : ℕ) : ℝ) - ((β.symm x₀ : ℕ) : ℝ)| := by
        have hne' : ((α.symm x₀ : ℕ) : ℤ) ≠ ((β.symm x₀ : ℕ) : ℤ) := by
          intro h; exact hx₀ (Fin.ext (by exact_mod_cast h))
        have : (1 : ℤ) ≤ |((α.symm x₀ : ℕ) : ℤ) - ((β.symm x₀ : ℕ) : ℤ)| :=
          Int.one_le_abs (sub_ne_zero.mpr hne')
        exact_mod_cast this
      calc (M : ℝ) = (M : ℝ) * 1 := by ring
        _ ≤ (M : ℝ) * |((α.symm x₀ : ℕ) : ℝ) - ((β.symm x₀ : ℕ) : ℝ)| :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ _ := Finset.single_le_sum
            (f := fun x => (M : ℝ) * |((α.symm x : ℕ) : ℝ) - ((β.symm x : ℕ) : ℝ)|)
            (fun _ _ => by positivity) (Finset.mem_univ x₀)
    have hboundR : ∑ x : Fin n, |((d₂ x).weight : ℝ)| ≤ (D : ℝ) := by
      have : ((∑ x : Fin n, |(d₂ x).weight| : ℤ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hbound
      simpa [Int.cast_sum, Int.cast_abs] using this
    have hsumlow := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hlow x)
    rw [Finset.sum_sub_distrib] at hsumlow
    linarith
  subst hαβeq
  refine ⟨α, fun j => (μ₁ (α j) : ℤ) - ((M * (j : ℕ) : ℕ) : ℤ),
    fun j => (μ₂ (α j) : ℤ) - ((M * (j : ℕ) + ψN j : ℕ) : ℤ), hc₁ α, hc₂ α, fun j => ⟨?_, ?_⟩⟩
  · have h1 := hp j
    have h2 := hq j
    have hw1 := hw₁ (α j)
    have hw2 := hw₂ (α j)
    have he1 := he₁ (α j)
    have he2 := he₂ (α j)
    have hψj : ((ψN j : ℕ) : ℂ) = ((ψ j : ℤ) : ℂ) := by exact_mod_cast hψN' j
    have hw1' : ((d₁ (α j)).weight : ℂ) = (d (α j)).weight + (μ₁ (α j) : ℂ) := by
      rw [hw1]; push_cast; ring
    have hw2' : ((d₂ (α j)).weight : ℂ) = (d₁ (α j)).weight - (μ₂ (α j) : ℂ) := by
      rw [hw2]; push_cast; ring
    simp only [hA, hBq] at h1 h2
    push_cast
    rw [hψj]
    linear_combination -(h1 + h2) + 2 * he2 + 2 * he1
  · have h1 := hp j
    have h2 := hq j
    have hw1 := hw₁ (α j)
    have hw2 := hw₂ (α j)
    have hψj : ((ψN j : ℕ) : ℂ) = ((ψ j : ℤ) : ℂ) := by exact_mod_cast hψN' j
    have hw1' : ((d₁ (α j)).weight : ℂ) = (d (α j)).weight + (μ₁ (α j) : ℂ) := by
      rw [hw1]; push_cast; ring
    have hw2' : ((d₂ (α j)).weight : ℂ) = (d₁ (α j)).weight - (μ₂ (α j) : ℂ) := by
      rw [hw2]; push_cast; ring
    simp only [hA, hBq] at h1 h2
    push_cast
    rw [hψj, hw0 j]
    linear_combination Complex.I * (h2 - h1 + hw2' + hw1')


end Langlands.Archimedean
