import Langlands.Group.HaarModulus
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-! # Haar moduli along a filtration with vector-space quotients -/

noncomputable section

universe u v

open scoped NNReal

namespace Langlands.HaarModulus

/-- Let `k` be a nonarchimedean local field and `U` a closed subgroup of a locally compact
Hausdorff group `G` in which every element lies in a compact open subgroup. Let `g` normalize
`U`. Suppose `U = F 0 ⊇ F 1 ⊇ ⋯ ⊇ F N = 1` is a chain of subgroups normalized by `g`. Suppose
that for each `r < N` there is a continuous, open, surjective additive map
`q r : F r → k^(n r)` with kernel `F (r + 1)`, and a `k`-linear automorphism `L r` of
`k^(n r)` with `q r (g x g⁻¹) = L r (q r x)`. Then the Haar modulus of conjugation by `g` on
`U` is `∏ r < N, |det (L r)|`, where `|a|` is Mathlib's Haar scaling factor
`distribHaarChar k a` of multiplication by `a` on `k`. This is a proof target. -/
def VectorFiltrationHaarModulusStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G]
    (U : Subgroup G) (hU : IsClosed (U : Set G))
    (_hcover : ∀ u : U, ∃ K : OpenSubgroup U, IsCompact (K : Set U) ∧ u ∈ K)
    (g : Subgroup.normalizer (U : Set G))
    (N : ℕ) (F : ℕ → Subgroup G)
    (_hF0 : F 0 = U) (_hFN : F N = ⊥)
    (_hFle : ∀ r < N, F (r + 1) ≤ F r)
    (_hFg : ∀ r < N, (g : G) ∈ Subgroup.normalizer (F r : Set G))
    (n : ℕ → ℕ) (q : ∀ r, F r → Fin (n r) → k)
    (_hqmul : ∀ r < N, ∀ x y : F r, q r (x * y) = q r x + q r y)
    (_hqker : ∀ r < N, ∀ x : F r, q r x = 0 ↔ (x : G) ∈ F (r + 1))
    (_hqc : ∀ r < N, Continuous (q r))
    (_hqo : ∀ r < N, IsOpenMap (q r))
    (_hqs : ∀ r < N, Function.Surjective (q r))
    (L : ∀ r, (Fin (n r) → k) ≃ₗ[k] (Fin (n r) → k))
    (_hqL : ∀ r < N, ∀ x y : F r, (y : G) = (g : G) * x * (g : G)⁻¹ →
      q r y = L r (q r x)),
    (closedNormalizerCharacter U hU g : ℝ≥0) =
      ∏ r ∈ Finset.range N, MeasureTheory.distribHaarChar k (LinearEquiv.det (L r))

end Langlands.HaarModulus
