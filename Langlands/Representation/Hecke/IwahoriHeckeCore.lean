import Langlands.Representation.Hecke.MassIndicatorProducts
import Mathlib.Algebra.Order.Floor.Ring

/-!
# The group-theoretic core of Renard V.5.3

For a compact open subgroup `K` with a three-factor decomposition `K = (K ∩ N)(K ∩ M)(K ∩ N̄)`,
a family `c y` of elements indexed by a lattice `Λ`, whose "dominant" members (nonnegative
pairings with finitely many roots) contract `K ∩ N`, normalize `K ∩ M` and expand `K ∩ N̄`,
and finitely many further elements `fe f` commuting with every `c y`, this module proves:
the sandwich spanning criterion `H = ∑ H₀ S H₀` from a Cartan-type decomposition, and the
finiteness lemma of Renard V.5.3 in both orders: finitely many admissible pairs `(t, f)` such
that every admissible `a (c y * fe f)` equals `a (c z) * a (c t * fe f)`, respectively
`a (c t * fe f) * a (c z)`, with `z` dominant.
-/

noncomputable section

namespace Langlands.Hecke

open MeasureTheory TestFunction HeckeAlgebra.Corner
open scoped Pointwise

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G]
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (μ : Measure G) [μ.IsHaarMeasure]

/-- **Sandwich spanning.** If `K₀` normalizes `K`, every element is `p₁ t p₂` with `p₁, p₂ ∈ K₀`
and `t ∈ T`, and every `a t` (`t ∈ T`) lies in the span of `S`, then the products
`a x₁ * s * a x₂` (`x₁, x₂ ∈ K₀`, `s ∈ S`) span the corner. -/
theorem span_sandwich_eq_top (K₀ : Subgroup G)
    (hnorm : ∀ k₀ ∈ K₀, ∀ k ∈ K, k₀ * k * k₀⁻¹ ∈ K)
    (T : Set G) (hcartan : ∀ g : G, ∃ p₁ ∈ K₀, ∃ t ∈ T, ∃ p₂ ∈ K₀, g = p₁ * t * p₂)
    (S : Set (HeckeAlgebra.Corner μ K hK))
    (hS : ∀ t ∈ T, massIndicator K hK μ t ∈ Submodule.span ℂ S) :
    Submodule.span ℂ {u | ∃ x₁ ∈ K₀, ∃ s ∈ S, ∃ x₂ ∈ K₀,
      u = massIndicator K hK μ x₁ * s * massIndicator K hK μ x₂} = ⊤ := by
  rw [eq_top_iff, ← span_range_doubleCoset K hK μ, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  obtain ⟨p₁, hp₁, t, ht, p₂, hp₂, rfl⟩ := hcartan g
  rw [SetLike.mem_coe, doubleCoset_eq_smul_massIndicator]
  apply Submodule.smul_mem
  have hp₂' : ∀ k ∈ K, p₂⁻¹ * k * p₂ ∈ K := by
    intro k hk
    simpa using hnorm p₂⁻¹ (K₀.inv_mem hp₂) k hk
  rw [← massIndicator_mul_of_normalizes K hK μ hp₂',
    ← massIndicator_mul_of_normalizes' K hK μ (hnorm p₁ hp₁)]
  refine Submodule.span_induction
    (p := fun x _ => massIndicator K hK μ p₁ * x * massIndicator K hK μ p₂ ∈
      Submodule.span ℂ {u | ∃ x₁ ∈ K₀, ∃ s ∈ S, ∃ x₂ ∈ K₀,
        u = massIndicator K hK μ x₁ * s * massIndicator K hK μ x₂})
    ?_ ?_ ?_ ?_ (hS t ht)
  · intro s hs
    exact Submodule.subset_span ⟨p₁, hp₁, s, hs, p₂, hp₂, rfl⟩
  · rw [mul_zero, zero_mul]
    exact Submodule.zero_mem _
  · intro u v _ _ hu hv
    rw [mul_add, add_mul]
    exact Submodule.add_mem _ hu hv
  · intro r u _ hu
    rw [mul_smul_comm, smul_mul_assoc]
    exact Submodule.smul_mem _ r hu

/-- Natural floors of `n + e` and `m + e`, both nonnegative, compare like `n` and `m`. -/
theorem int_le_of_natFloor_add_le {m n : ℤ} {e : ℝ} (hm : 0 ≤ (m : ℝ) + e)
    (hn : 0 ≤ (n : ℝ) + e) (h : ⌊(n : ℝ) + e⌋₊ ≤ ⌊(m : ℝ) + e⌋₊) : n ≤ m := by
  have h' : ⌊(n : ℝ) + e⌋ ≤ ⌊(m : ℝ) + e⌋ := by
    rw [← Int.natCast_floor_eq_floor hn, ← Int.natCast_floor_eq_floor hm]
    exact_mod_cast h
  rw [Int.floor_intCast_add, Int.floor_intCast_add] at h'
  omega

omit [Group G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [T2Space G] in
/-- **Finitely many stable representatives.** Let `φ` reflect a relation `R` on `S`, and let
`V y` (`y ∈ S`) be sets, determined by finitely many test points inside any compact set, with
`V y ⊆ B t` (compact) whenever `R t y`. Then finitely many `t ∈ S` satisfy: every `y ∈ S`
has a representative `t` with `R t y` and `V t = V y`. -/
theorem exists_finite_stable_representatives {X ι : Type*} [Finite ι]
    (S : Set X) (φ : X → ι → ℕ) (R : X → X → Prop)
    (hφ : ∀ t ∈ S, ∀ y ∈ S, φ t ≤ φ y → R t y)
    (V B : X → Set G) (hB : ∀ t, IsCompact (B t))
    (hVB : ∀ t y, y ∈ S → R t y → V y ⊆ B t)
    (htest : ∀ W : Set G, IsCompact W → ∃ tW : Finset G, ∀ y ∈ S, ∀ y' ∈ S,
      V y ⊆ W → V y' ⊆ W → (∀ g ∈ tW, g ∈ V y ↔ g ∈ V y') → V y = V y') :
    ∃ T : Set X, T.Finite ∧ T ⊆ S ∧ ∀ y ∈ S, ∃ t ∈ T, R t y ∧ V t = V y := by
  classical
  obtain ⟨T₀, hT₀fin, hT₀S, hT₀⟩ := exists_finite_le_of_label φ (fun _ => ()) S
  let W : Set G := ⋃ t ∈ T₀, B t
  have hW : IsCompact W := hT₀fin.isCompact_biUnion fun t _ => hB t
  have hVW : ∀ y ∈ S, V y ⊆ W := by
    intro y hy
    obtain ⟨t, ht, hty, -⟩ := hT₀ y hy
    exact (hVB t y hy (hφ t (hT₀S ht) y hy hty)).trans (Set.subset_biUnion_of_mem ht)
  obtain ⟨tW, htW⟩ := htest W hW
  obtain ⟨T, hTfin, hTS, hT⟩ := exists_finite_le_of_label φ
    (fun y => {g : tW | (g : G) ∈ V y}) S
  refine ⟨T, hTfin, hTS, fun y hy => ?_⟩
  obtain ⟨t, ht, hty, hlab⟩ := hT y hy
  refine ⟨t, ht, hφ t (hTS ht) y hy hty, ?_⟩
  apply htW t (hTS ht) y hy (hVW t (hTS ht)) (hVW y hy)
  intro g hg
  have := congrArg (fun A : Set tW => (⟨g, hg⟩ : tW) ∈ A) hlab
  exact Iff.of_eq this

section Finiteness

variable {Λ : Type*} [AddCommGroup Λ] {ι : Type*} [Finite ι]

/-- The data of the finiteness lemma: an ordered three-factor decomposition of `K` and a
lattice family `c` whose dominant members contract `K ∩ N`, normalize `K ∩ M` and expand
`K ∩ N̄`. -/
structure IwahoriLatticeData (K : OpenSubgroup G) (Λ : Type*) [AddCommGroup Λ]
    (ι : Type*) where
  /-- `K ∩ N`. -/
  Kn : Set G
  /-- `K ∩ M`. -/
  Km : Set G
  /-- `K ∩ N̄`. -/
  Knb : Set G
  Kn_subset : Kn ⊆ K
  Km_subset : Km ⊆ K
  Knb_subset : Knb ⊆ K
  /-- Every element of `K` is `n * m * nb`. -/
  decomp : ∀ k ∈ K, ∃ n ∈ Kn, ∃ m ∈ Km, ∃ nb ∈ Knb, k = n * m * nb
  /-- The lattice family. -/
  c : Λ → G
  c_add : ∀ y y', c (y + y') = c y * c y'
  /-- The root pairings. -/
  pair : ι → Λ →+ ℤ
  conj_Km : ∀ y, (∀ α, 0 ≤ pair α y) → ∀ m ∈ Km,
    c y * m * (c y)⁻¹ ∈ K ∧ (c y)⁻¹ * m * c y ∈ K
  conj_Kn : ∀ y, (∀ α, 0 ≤ pair α y) → ∀ n ∈ Kn, c y * n * (c y)⁻¹ ∈ Kn
  conj_Knb : ∀ y, (∀ α, 0 ≤ pair α y) → ∀ nb ∈ Knb, (c y)⁻¹ * nb * c y ∈ Knb

namespace IwahoriLatticeData

variable {K} (L : IwahoriLatticeData K Λ ι)

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [T2Space G] [Finite ι] in
theorem c_sub_mul (y t : Λ) : L.c (y - t) * L.c t = L.c y := by
  rw [← L.c_add, sub_add_cancel]

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [T2Space G] [Finite ι] in
theorem mul_c_sub (y t : Λ) : L.c t * L.c (y - t) = L.c y := by
  rw [← L.c_add, add_sub_cancel]

omit [Finite ι] in
/-- **Products of dominant elements.** -/
theorem massIndicator_mul_dominant {y₁ y₂ : Λ} (h₁ : ∀ α, 0 ≤ L.pair α y₁)
    (h₂ : ∀ α, 0 ≤ L.pair α y₂) :
    massIndicator K hK μ (L.c y₁) * massIndicator K hK μ (L.c y₂) =
      massIndicator K hK μ (L.c (y₁ + y₂)) := by
  rw [L.c_add]
  apply massIndicator_mul K hK μ
  refine mul_mem_doubleCosetSet_of_factor_left K L.Kn L.Km L.Knb L.decomp
    (fun n hn => L.Kn_subset (L.conj_Kn y₁ h₁ n hn))
    (fun m hm => (L.conj_Km y₁ h₁ m hm).1) ?_
  intro nb hnb
  refine (mem_doubleCosetSet K _ _).2
    ⟨1, K.one_mem, (L.c y₂)⁻¹ * nb * L.c y₂, L.Knb_subset (L.conj_Knb y₂ h₂ nb hnb), ?_⟩
  group

variable {Fidx : Type*} [Finite Fidx] (fe : Fidx → G) (e : ι → Fidx → ℝ)

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [T2Space G] [Finite ι]
  [Finite Fidx] in
/-- Order reflection of the floor coordinates on the admissible set of `f`. -/
theorem dominant_sub_of_floor_le (f : Fidx) {t y : Λ}
    (ht : ∀ α, 0 ≤ (L.pair α t : ℝ) + e α f) (hy : ∀ α, 0 ≤ (L.pair α y : ℝ) + e α f)
    (hle : (fun α => ⌊(L.pair α t : ℝ) + e α f⌋₊) ≤ fun α => ⌊(L.pair α y : ℝ) + e α f⌋₊) :
    ∀ α, 0 ≤ L.pair α (y - t) := by
  intro α
  rw [map_sub, sub_nonneg]
  exact int_le_of_natFloor_add_le (hy α) (ht α) (hle α)

include hK in
/-- **Finiteness lemma, left version** (Renard V.5.3, Lemme). Finitely many admissible pairs
`(t, f)` suffice: every admissible `a (c y * fe f)` is `a (c z) * a (c t * fe f)` with `z`
dominant. -/
theorem exists_finite_left :
    ∃ T : Set (Λ × Fidx), T.Finite ∧ (∀ p ∈ T, ∀ α, 0 ≤ (L.pair α p.1 : ℝ) + e α p.2) ∧
      ∀ y f, (∀ α, 0 ≤ (L.pair α y : ℝ) + e α f) → ∃ p ∈ T, ∃ z, (∀ α, 0 ≤ L.pair α z) ∧
        massIndicator K hK μ (L.c z) * massIndicator K hK μ (L.c p.1 * fe p.2) =
          massIndicator K hK μ (L.c y * fe f) := by
  classical
  have hfix : ∀ f : Fidx, ∃ T : Set Λ, T.Finite ∧
      T ⊆ {y | ∀ α, 0 ≤ (L.pair α y : ℝ) + e α f} ∧
      ∀ y ∈ {y | ∀ α, 0 ≤ (L.pair α y : ℝ) + e α f}, ∃ t ∈ T,
        (∀ α, 0 ≤ L.pair α (y - t)) ∧
        {g | ∃ nb ∈ L.Knb, ∃ k ∈ K, g = (L.c t)⁻¹ * nb * L.c t * fe f * k} =
          {g | ∃ nb ∈ L.Knb, ∃ k ∈ K, g = (L.c y)⁻¹ * nb * L.c y * fe f * k} := by
    intro f
    refine exists_finite_stable_representatives _
      (fun y α => ⌊(L.pair α y : ℝ) + e α f⌋₊) (fun t y => ∀ α, 0 ≤ L.pair α (y - t))
      (fun t ht y hy hle => L.dominant_sub_of_floor_le e f ht hy hle)
      (fun y => {g | ∃ nb ∈ L.Knb, ∃ k ∈ K, g = (L.c y)⁻¹ * nb * L.c y * fe f * k})
      (fun t => (fun p : G × G => (L.c t)⁻¹ * p.1 * L.c t * fe f * p.2) ''
        ((K : Set G) ×ˢ (K : Set G)))
      (fun t => (hK.prod hK).image (by fun_prop)) ?_ ?_
    · rintro t y - hty _ ⟨nb, hnb, k, hk, rfl⟩
      refine ⟨((L.c (y - t))⁻¹ * nb * L.c (y - t), k),
        ⟨L.Knb_subset (L.conj_Knb _ hty nb hnb), hk⟩, ?_⟩
      simp only [← L.c_sub_mul y t]
      group
    · intro W hW
      obtain ⟨tW, htW⟩ := exists_finset_test_rightInvariant K hW
      refine ⟨tW, fun y _ y' _ hy hy' hiff => htW _ _ hy hy' ?_ ?_ hiff⟩
      · rintro _ ⟨nb, hnb, k, hk, rfl⟩ k' hk'
        exact ⟨nb, hnb, k * k', K.mul_mem hk hk', by group⟩
      · rintro _ ⟨nb, hnb, k, hk, rfl⟩ k' hk'
        exact ⟨nb, hnb, k * k', K.mul_mem hk hk', by group⟩
  choose T hTfin hTS hT using hfix
  refine ⟨⋃ f, (fun t => (t, f)) '' T f, Set.finite_iUnion fun f => (hTfin f).image _, ?_, ?_⟩
  · intro p hp
    obtain ⟨f, t, ht, rfl⟩ := Set.mem_iUnion.1 hp
    exact hTS f ht
  · intro y f hy
    obtain ⟨t, ht, hdom, hV⟩ := hT f y hy
    refine ⟨(t, f), Set.mem_iUnion.2 ⟨f, t, ht, rfl⟩, y - t, hdom, ?_⟩
    have hprod : L.c (y - t) * (L.c t * fe f) = L.c y * fe f := by
      rw [← mul_assoc, L.c_sub_mul]
    rw [← hprod]
    apply massIndicator_mul K hK μ
    refine mul_mem_doubleCosetSet_of_factor_left K L.Kn L.Km L.Knb L.decomp
      (fun n hn => L.Kn_subset (L.conj_Kn _ hdom n hn))
      (fun m hm => (L.conj_Km _ hdom m hm).1) ?_
    intro nb hnb
    have hmem : (L.c t)⁻¹ * nb * L.c t * fe f ∈
        {g | ∃ nb ∈ L.Knb, ∃ k ∈ K, g = (L.c y)⁻¹ * nb * L.c y * fe f * k} := by
      rw [← hV]
      exact ⟨nb, hnb, 1, K.one_mem, by group⟩
    obtain ⟨nb', hnb', k, hk, hk'⟩ := hmem
    rw [hprod]
    refine (mem_doubleCosetSet K _ _).2 ⟨nb', L.Knb_subset hnb', k, hk, ?_⟩
    calc L.c (y - t) * nb * (L.c t * fe f)
        = L.c (y - t) * L.c t * ((L.c t)⁻¹ * nb * L.c t * fe f) := by group
      _ = nb' * (L.c y * fe f) * k := by
        rw [hk', L.c_sub_mul]
        group

include hK in
/-- **Finiteness lemma, right version** (Renard V.5.3, Remarque). If the dominant `c z` commute
with the `fe f`, finitely many admissible pairs `(t, f)` suffice: every admissible
`a (c y * fe f)` is `a (c t * fe f) * a (c z)` with `z` dominant. -/
theorem exists_finite_right
    (hcomm : ∀ y, (∀ α, 0 ≤ L.pair α y) → ∀ f, Commute (L.c y) (fe f)) :
    ∃ T : Set (Λ × Fidx), T.Finite ∧ (∀ p ∈ T, ∀ α, 0 ≤ (L.pair α p.1 : ℝ) + e α p.2) ∧
      ∀ y f, (∀ α, 0 ≤ (L.pair α y : ℝ) + e α f) → ∃ p ∈ T, ∃ z, (∀ α, 0 ≤ L.pair α z) ∧
        massIndicator K hK μ (L.c p.1 * fe p.2) * massIndicator K hK μ (L.c z) =
          massIndicator K hK μ (L.c y * fe f) := by
  classical
  have hshift : ∀ f t y, (∀ α, 0 ≤ L.pair α (y - t)) →
      L.c t * fe f * L.c (y - t) = L.c y * fe f := by
    intro f t y hty
    rw [mul_assoc, ← (hcomm _ hty f).eq, ← mul_assoc, L.mul_c_sub]
  have hfix : ∀ f : Fidx, ∃ T : Set Λ, T.Finite ∧
      T ⊆ {y | ∀ α, 0 ≤ (L.pair α y : ℝ) + e α f} ∧
      ∀ y ∈ {y | ∀ α, 0 ≤ (L.pair α y : ℝ) + e α f}, ∃ t ∈ T,
        (∀ α, 0 ≤ L.pair α (y - t)) ∧
        {g | ∃ k ∈ K, ∃ n ∈ L.Kn, g = k * (L.c t * fe f) * n * (L.c t * fe f)⁻¹} =
          {g | ∃ k ∈ K, ∃ n ∈ L.Kn, g = k * (L.c y * fe f) * n * (L.c y * fe f)⁻¹} := by
    intro f
    refine exists_finite_stable_representatives _
      (fun y α => ⌊(L.pair α y : ℝ) + e α f⌋₊) (fun t y => ∀ α, 0 ≤ L.pair α (y - t))
      (fun t ht y hy hle => L.dominant_sub_of_floor_le e f ht hy hle)
      (fun y => {g | ∃ k ∈ K, ∃ n ∈ L.Kn, g = k * (L.c y * fe f) * n * (L.c y * fe f)⁻¹})
      (fun t => (fun p : G × G => p.1 * (L.c t * fe f) * p.2 * (L.c t * fe f)⁻¹) ''
        ((K : Set G) ×ˢ (K : Set G)))
      (fun t => (hK.prod hK).image (by fun_prop)) ?_ ?_
    · rintro t y - hty _ ⟨k, hk, n, hn, rfl⟩
      refine ⟨(k, L.c (y - t) * n * (L.c (y - t))⁻¹),
        ⟨hk, L.Kn_subset (L.conj_Kn _ hty n hn)⟩, ?_⟩
      simp only [← hshift f t y hty]
      group
    · intro W hW
      obtain ⟨tW, htW⟩ := exists_finset_test_leftInvariant K hW
      refine ⟨tW, fun y _ y' _ hy hy' hiff => htW _ _ hy hy' ?_ ?_ hiff⟩
      · rintro _ ⟨k, hk, n, hn, rfl⟩ k' hk'
        exact ⟨k' * k, K.mul_mem hk' hk, n, hn, by group⟩
      · rintro _ ⟨k, hk, n, hn, rfl⟩ k' hk'
        exact ⟨k' * k, K.mul_mem hk' hk, n, hn, by group⟩
  choose T hTfin hTS hT using hfix
  refine ⟨⋃ f, (fun t => (t, f)) '' T f, Set.finite_iUnion fun f => (hTfin f).image _, ?_, ?_⟩
  · intro p hp
    obtain ⟨f, t, ht, rfl⟩ := Set.mem_iUnion.1 hp
    exact hTS f ht
  · intro y f hy
    obtain ⟨t, ht, hdom, hV⟩ := hT f y hy
    refine ⟨(t, f), Set.mem_iUnion.2 ⟨f, t, ht, rfl⟩, y - t, hdom, ?_⟩
    have hprod := hshift f t y hdom
    rw [← hprod]
    apply massIndicator_mul K hK μ
    refine mul_mem_doubleCosetSet_of_factor_right K L.Kn L.Km L.Knb L.decomp
      (fun m hm => (L.conj_Km _ hdom m hm).2)
      (fun nb hnb => L.Knb_subset (L.conj_Knb _ hdom nb hnb)) ?_
    intro n hn
    have hmem : L.c t * fe f * n * (L.c t * fe f)⁻¹ ∈
        {g | ∃ k ∈ K, ∃ n ∈ L.Kn, g = k * (L.c y * fe f) * n * (L.c y * fe f)⁻¹} := by
      rw [← hV]
      exact ⟨1, K.one_mem, n, hn, by group⟩
    obtain ⟨k, hk, n', hn', hk'⟩ := hmem
    rw [hprod]
    refine (mem_doubleCosetSet K _ _).2 ⟨k, hk, n', L.Kn_subset hn', ?_⟩
    calc L.c t * fe f * n * L.c (y - t)
        = L.c t * fe f * n * (L.c t * fe f)⁻¹ * (L.c t * fe f * L.c (y - t)) := by
          group
      _ = k * (L.c y * fe f) * n' := by
        rw [hk', hprod]
        group

end IwahoriLatticeData

end Finiteness

end Langlands.Hecke
