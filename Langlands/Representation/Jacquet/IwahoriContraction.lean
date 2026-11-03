import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Tactic.Group

/-! Explicit Iwahori factorization and contraction hypotheses for actual subgroups. -/

namespace Langlands.Jacquet

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Explicit factorization and contraction conditions on an open subgroup and
an element, relative to three actual subgroups. Compactness is a separate
hypothesis in applications. -/
structure IsIwahoriContraction (K : OpenSubgroup G) (N M Nbar : Subgroup G) (g : G) :
    Prop where
  /-- The contracting element lies in `M`. -/
  mem_levi : g ∈ M
  /-- Iwahori factorization `K = (K ∩ Nbar)(K ∩ M)(K ∩ N)`. -/
  factor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
    ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u
  /-- Conjugation by `g` maps `K ∩ N` into itself. -/
  upper : ∀ u ∈ K.toSubgroup ⊓ N, g * u * g⁻¹ ∈ K.toSubgroup ⊓ N
  /-- Conjugation by `g⁻¹` maps `K ∩ M` into itself. -/
  levi : ∀ m ∈ K.toSubgroup ⊓ M, g⁻¹ * m * g ∈ K.toSubgroup ⊓ M
  /-- Conjugation by `g⁻¹` maps `K ∩ Nbar` into itself. -/
  lower : ∀ l ∈ K.toSubgroup ⊓ Nbar, g⁻¹ * l * g ∈ K.toSubgroup ⊓ Nbar
  /-- Each element of `N` is carried into `K` by some positive power of `g`. -/
  exhaust : ∀ x ∈ N, ∃ r : ℕ, g ^ r * x * (g ^ r)⁻¹ ∈ K
  /-- Powers of `g⁻¹` contract `K ∩ Nbar` uniformly into every open subgroup. -/
  contract : ∀ L : OpenSubgroup G, ∃ s : ℕ,
    ∀ l ∈ K.toSubgroup ⊓ Nbar, (g ^ s)⁻¹ * l * g ^ s ∈ L

namespace IsIwahoriContraction

variable {K : OpenSubgroup G} {N M Nbar : Subgroup G} {g : G}

theorem upper_pow (h : IsIwahoriContraction K N M Nbar g) (s : ℕ) :
    ∀ u ∈ K.toSubgroup ⊓ N, g ^ s * u * (g ^ s)⁻¹ ∈ K.toSubgroup ⊓ N := by
  induction s with
  | zero => intro u hu; simpa using hu
  | succ s ih =>
    intro u hu
    have e : g ^ (s + 1) * u * (g ^ (s + 1))⁻¹ = g * (g ^ s * u * (g ^ s)⁻¹) * g⁻¹ := by
      group
    rw [e]
    exact h.upper _ (ih u hu)

theorem levi_pow (h : IsIwahoriContraction K N M Nbar g) (s : ℕ) :
    ∀ m ∈ K.toSubgroup ⊓ M, (g ^ s)⁻¹ * m * g ^ s ∈ K.toSubgroup ⊓ M := by
  induction s with
  | zero => intro m hm; simpa using hm
  | succ s ih =>
    intro m hm
    have e : (g ^ (s + 1))⁻¹ * m * g ^ (s + 1) = g⁻¹ * ((g ^ s)⁻¹ * m * g ^ s) * g := by
      group
    rw [e]
    exact h.levi _ (ih m hm)

/-- For every `x ∈ N`, conjugation by `g ^ s` carries `x` into `K` for all
sufficiently large `s`. -/
theorem eventually_mem (h : IsIwahoriContraction K N M Nbar g)
    (hMN : M ≤ Subgroup.normalizer N) (x : N) :
    ∃ r : ℕ, ∀ s : ℕ, r ≤ s → g ^ s * x.val * (g ^ s)⁻¹ ∈ K := by
  obtain ⟨r, hr⟩ := h.exhaust x.val x.property
  refine ⟨r, fun s hs => ?_⟩
  have hgN : g ^ r ∈ Subgroup.normalizer N := pow_mem (hMN h.mem_levi) r
  have hN : g ^ r * x.val * (g ^ r)⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp hgN x.val).mp x.property
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  have e : g ^ (r + t) * x.val * (g ^ (r + t))⁻¹ =
      g ^ t * (g ^ r * x.val * (g ^ r)⁻¹) * (g ^ t)⁻¹ := by
    group
  rw [e]
  exact (h.upper_pow t _ ⟨hr, hN⟩).1

end IsIwahoriContraction

/-- Compact open subgroups with the specified contraction conditions have
arbitrarily small intersections with the Levi subgroup. -/
def HasIwahoriContractionBasis (N M Nbar : Subgroup G) : Prop :=
  ∀ L : OpenSubgroup M, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
    K.toSubgroup.comap M.subtype ≤ L.toSubgroup ∧
      ∃ g : G, IsIwahoriContraction K N M Nbar g

end Langlands.Jacquet
