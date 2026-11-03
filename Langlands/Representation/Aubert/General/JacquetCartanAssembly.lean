import Langlands.Representation.Smooth.Admissibility.JacquetCartan

/-!
# Jacquet–Cartan data from standard parabolic systems

A `StandardParabolicSystem G` on a topological group `G` records the structure
of the standard parabolic subgroups `P_I = M_I N_I` of a reductive group, indexed
by finite sets `I` of simple roots, as used in Renard VI.2.1 and VI.2.2: Levi
decompositions, an Iwasawa decomposition `G = P_∅ K`, a Cartan decomposition of
each standard Levi with a countable middle set, and the contraction dichotomy of
the proof of VI.2.1 `a) ⇒ b)` for the walls `J ⊊ I`.

`StandardParabolicSystem.toJacquetCartanDatum` assembles a
`Langlands.JacquetCartanDatum G`: the indices are the finite sets `I`, ranked by
cardinality; the walls of `I` are the proper subsets `J ⊊ I`, with wall subgroup
`N_J ∩ M_I` and descent index `J`.
-/

noncomputable section

open Filter Topology

namespace Langlands.Aubert.General

universe uG uι

/-- **The wall contraction dichotomy** for the Cartan elements of `M_I`
(proof of Renard VI.2.1 `a) ⇒ b)`), with the walls `J ⊊ I` and wall subgroups
`N_J ∩ M_I`. For every neighbourhood `O` of `1` and finitely many elements of
each wall subgroup there is a compact set `D` such that each `t ∈ cartanSet I`
is either `d * z` with `d ∈ D` and `z` central in `M_I`, or conjugates the given
elements of some wall into `O`. -/
def HasWallContraction {G : Type uG} [Group G] [TopologicalSpace G] {Δ : Type uι}
    (levi unipotent : Finset Δ → Subgroup G) (cartanSet : Finset Δ → Set G)
    (I : Finset Δ) : Prop :=
  ∀ O ∈ 𝓝 (1 : G), ∀ S : {J : Finset Δ // J ⊂ I} → Finset G,
    (∀ J, (S J : Set G) ⊆ unipotent J.1 ⊓ levi I) →
    ∃ D : Set G, IsCompact D ∧ ∀ t ∈ cartanSet I,
      (∃ d ∈ D, ∃ z ∈ levi I, (∀ m ∈ levi I, m * z = z * m) ∧ t = d * z) ∨
        ∃ J, ∀ u ∈ S J, t * u * t⁻¹ ∈ O

/-- **Standard parabolic systems.** The structure of the standard parabolic
subgroups of a reductive group needed for Jacquet's admissibility argument.

* `parabolic I`, `levi I`, `unipotent I` model `P_I`, `M_I`, `N_I` for finite
  sets `I` of simple roots `Δ`. The parabolics increase with `I`, each element of
  `P_I` is `m * n` with `m ∈ M_I` and `n ∈ N_I`, `M_I` is closed and normalizes
  `N_I`, and some index `top` (all simple roots) has `N_top = ⊥`.
* `unipotent_descent`: for `J ⊆ I`, `N_J ⊆ (N_J ∩ M_I) N_I`.
* `iwasawa`: `G = P_∅ K` for a compact set `K` (Renard V.5.1 (1)).
* `cartan`: `M_I = K_I Λ_I K_I` with `K_I ⊆ M_I` compact and `Λ_I ⊆ M_I`
  countable (Renard V.5.1 (4), (5)).
* `contraction`: the wall contraction dichotomy `HasWallContraction` for every
  `I` (proof of Renard VI.2.1 `a) ⇒ b)`). -/
structure StandardParabolicSystem (G : Type uG) [Group G] [TopologicalSpace G] where
  /-- The simple roots. -/
  Δ : Type uι
  [decEq : DecidableEq Δ]
  /-- The standard parabolic subgroup `P_I`. -/
  parabolic : Finset Δ → Subgroup G
  /-- The standard Levi subgroup `M_I`. -/
  levi : Finset Δ → Subgroup G
  /-- The unipotent radical `N_I` of `P_I`. -/
  unipotent : Finset Δ → Subgroup G
  parabolic_mono : ∀ ⦃I J : Finset Δ⦄, I ⊆ J → parabolic I ≤ parabolic J
  levi_mul_unipotent : ∀ I, ∀ p ∈ parabolic I, ∃ m ∈ levi I, ∃ n ∈ unipotent I, p = m * n
  levi_le_normalizer : ∀ I, levi I ≤ Subgroup.normalizer (unipotent I : Set G)
  isClosed_levi : ∀ I, IsClosed (levi I : Set G)
  /-- The set of all simple roots. -/
  top : Finset Δ
  unipotent_top : unipotent top = ⊥
  unipotent_descent : ∀ ⦃I J : Finset Δ⦄, J ⊆ I → ∀ n ∈ unipotent J,
    ∃ u ∈ unipotent J ⊓ levi I, ∃ n' ∈ unipotent I, n = u * n'
  iwasawa : ∃ K : Set G, IsCompact K ∧ ∀ g : G, ∃ p ∈ parabolic ∅, ∃ k ∈ K, g = p * k
  /-- The compact part `K_I` of the Cartan decomposition of `M_I`. -/
  cartanCompact : Finset Δ → Set G
  /-- The countable middle set `Λ_I` of the Cartan decomposition of `M_I`. -/
  cartanSet : Finset Δ → Set G
  isCompact_cartanCompact : ∀ I, IsCompact (cartanCompact I)
  cartanCompact_subset : ∀ I, cartanCompact I ⊆ levi I
  countable_cartanSet : ∀ I, (cartanSet I).Countable
  cartanSet_subset : ∀ I, cartanSet I ⊆ levi I
  cartan : ∀ I, ∀ m ∈ levi I,
    ∃ k₁ ∈ cartanCompact I, ∃ t ∈ cartanSet I, ∃ k₂ ∈ cartanCompact I, m = k₁ * t * k₂
  contraction : ∀ I, HasWallContraction levi unipotent cartanSet I

namespace StandardParabolicSystem

variable {G : Type uG} [Group G] [TopologicalSpace G]
  (𝒮 : StandardParabolicSystem.{uG, uι} G)

attribute [instance] StandardParabolicSystem.decEq

/-- The wall subgroup `N_J ∩ M_I` of a wall `J ⊊ I`. -/
def wallUnipotent (I : Finset 𝒮.Δ) (J : {J : Finset 𝒮.Δ // J ⊂ I}) : Subgroup G :=
  𝒮.unipotent J.1 ⊓ 𝒮.levi I

/-- **The Jacquet–Cartan datum of a standard parabolic system.** The indices are
the finite sets `I` of simple roots with rank `|I|`; the Iwasawa compact set is
the compact set of `G = P_∅ K`; the walls of `I` are the proper subsets `J ⊊ I`
with wall subgroup `N_J ∩ M_I` and descent index `J`. -/
def toJacquetCartanDatum : JacquetCartanDatum.{uG, uι} G where
  ι := Finset 𝒮.Δ
  rank I := I.card
  levi := 𝒮.levi
  unipotent := 𝒮.unipotent
  top := 𝒮.top
  unipotent_top := 𝒮.unipotent_top
  levi_le_normalizer := 𝒮.levi_le_normalizer
  isClosed_levi := 𝒮.isClosed_levi
  iwasawa I := by
    obtain ⟨K, hK, hiw⟩ := 𝒮.iwasawa
    refine ⟨K, hK, fun g => ?_⟩
    obtain ⟨p, hp, k, hk, rfl⟩ := hiw g
    obtain ⟨m, hm, n, hn, rfl⟩ :=
      𝒮.levi_mul_unipotent I p (𝒮.parabolic_mono (Finset.empty_subset I) hp)
    exact ⟨m, hm, n, hn, k, hk, rfl⟩
  wall I := {J : Finset 𝒮.Δ // J ⊂ I}
  wallUnipotent := 𝒮.wallUnipotent
  wallUnipotent_le _ _ := inf_le_right
  descent _ J := ⟨J.1, Finset.card_lt_card J.2, 𝒮.unipotent_descent J.2.subset⟩
  cartanCompact := 𝒮.cartanCompact
  cartanSet := 𝒮.cartanSet
  isCompact_cartanCompact := 𝒮.isCompact_cartanCompact
  cartanCompact_subset := 𝒮.cartanCompact_subset
  countable_cartanSet := 𝒮.countable_cartanSet
  cartanSet_subset := 𝒮.cartanSet_subset
  cartan := 𝒮.cartan
  contraction I := 𝒮.contraction I

end StandardParabolicSystem

/-- A topological group with a standard parabolic system carries a
Jacquet–Cartan datum. -/
theorem StandardParabolicSystem.nonempty_jacquetCartanDatum {G : Type uG} [Group G]
    [TopologicalSpace G] (𝒮 : StandardParabolicSystem.{uG, uι} G) :
    Nonempty (JacquetCartanDatum.{uG, uι} G) :=
  ⟨𝒮.toJacquetCartanDatum⟩

end Langlands.Aubert.General
