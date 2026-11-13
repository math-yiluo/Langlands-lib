# Line stabilizers in a rank-one graded algebra acting on a vector space

Author: Worker 33. Module `Langlands.Algebra.RankOneGradedLagrangian`, namespace
`Langlands.RankOneGraded.IsRankOneGrading`. It imports
`Langlands.Algebra.RankOneGradedAlgebra` and only adds to it.

This module is pure algebra. It contains the algebraic part of the proof of Renard's
Lemma of VI.4.4 (the subgroups `T ⊂ H ⊂ N` with `[N : H] = [H : T] = m`). The
representation-theoretic translation is in
`Langlands.Representation.CuspidalSupport.NormalHeckeLineStabilizer`.

## Setting

`ι` is an additive commutative group with decidable equality, `k` a field, `R` a `k`-algebra
with a grading `𝒜 : ι → Submodule k R` (`GradedAlgebra 𝒜`), and
`h𝒜 : IsRankOneGrading 𝒜`: every piece has rank at most one and every nonzero homogeneous
element is a unit. `IsRankOneGrading`, `support`, `radical`, `IsMulOrAntiMul` and the facts
used below are from the published module `RankOneGradedAlgebra`. `M` is a `k`-vector space
and `ρ : R →ₗ[k] Module.End k M` is linear with `hρ1 : ρ 1 = 1` and
`hρ : IsMulOrAntiMul ρ` (`ρ` is multiplicative or anti-multiplicative). From the section
`Stab` on, `R` is nontrivial.

In the application, `R = End(ind_{⁰G}^G ρ)` graded by `G/⁰G`, `M = Hom(ind ρ, π)`, and `ρ`
is the right action `α ↦ (φ ↦ α ≫ φ)`, which is anti-multiplicative.

## Definitions

- `stab ρ hρ1 hρ x : AddSubgroup ι`, for `x : M` (written `h𝒜.stab ρ hρ1 hρ x`). Its
  carrier is the set of degrees `a` with `𝒜 a ≠ ⊥` such that every `u ∈ 𝒜 a` satisfies
  `ρ u x = c • x` for some `c : k`. The proof that this is a subgroup uses that `𝒜 0`
  consists of scalars and that `ρ w` is a multiple of `ρ u * ρ v` when `w` has degree
  `a + b` and `u`, `v` are nonzero of degrees `a`, `b`. For `x ≠ 0`, `stab x` is the set
  of degrees whose piece stabilizes the line `k x`.
- `perp 𝒜 ρ K : Set ι`, for `K : AddSubgroup ι`. It is the set of degrees `a` with
  `𝒜 a ≠ ⊥` such that `ρ u * ρ v = ρ v * ρ u` for all `b ∈ K`, `u ∈ 𝒜 a` and `v ∈ 𝒜 b`.

`mem_stab_iff` and `mem_perp_iff` unfold these definitions.

### Provenance

Both are derived definitions, not stated in the source. They abstract the groups of Renard
2026, VI.4.4, preliminary remarks and Lemma (printed pp.155–158 / PDF pp.161–164). For
`x = e⁻¹(j)`, where `j : ρ → π` is an embedding with image `W`, `stab x` is the image in
`G/⁰G` of `H = {g | π(g) W = W}`. `perp (stab x)` corresponds to `H̃`, the normalizer of
`ρ_H`. Renard's choice of `W` with `H = H̃` corresponds to the condition
`perp (stab x) ⊆ stab x`. These identifications are proved in `NormalHeckeLineStabilizer`.

## Results

Elementary facts:

- `isUnit_map`, `map_injective`: a nonzero homogeneous element acts by an invertible,
  hence injective, operator.
- `exists_map_eq_smul_mul`: for nonzero `u ∈ 𝒜 a`, `v ∈ 𝒜 b` and any `w ∈ 𝒜 (a + b)`,
  `ρ w = c • (ρ u * ρ v)` for some `c`.
- `exists_map_mul_eq_smul`: for nonzero `u ∈ 𝒜 a` and any `v ∈ 𝒜 b`,
  `ρ v * ρ u = c • (ρ u * ρ v)` for some `c`.
- `exists_mem_map_mul_left`, `exists_mem_map_mul_right`: for nonzero `u ∈ 𝒜 a` and any
  `u' ∈ 𝒜 a'`, there is `w ∈ 𝒜 (a' - a)` with `ρ w * ρ u = ρ u'`, respectively
  `ρ u * ρ w = ρ u'`. The proof multiplies `u'` by the inverse of `u`, which is homogeneous.
- `exists_map_map_eq_smul`: if `b ∈ stab x`, `u ∈ 𝒜 a` is nonzero and `v ∈ 𝒜 b`, then
  `ρ v (ρ u x) = c • ρ u x` for some `c`.

Line stabilizers:

- `stab_le_support`: `stab x ≤ support`.
- `radical_le_stab` (for surjective `ρ`): `radical ≤ stab x`. Central elements act by
  scalars (`exists_eq_algebraMap_of_mem_center`).
- `commute_of_mem_stab`: for `x ≠ 0`, the pieces of degrees in `stab x` act by commuting
  operators. By `exists_map_mul_eq_smul`, `ρ v * ρ u = c • (ρ u * ρ v)`. Evaluating at `x`
  gives `e d x = c d e x`, where `e`, `d` are the eigenvalues of `ρ u`, `ρ v` on `x`. These
  are nonzero because the operators are injective, so `c = 1`.

**`relIndex_stab_support`** (`M` finite-dimensional, `ρ` surjective, `x ≠ 0`,
`perp 𝒜 ρ (stab x) ⊆ stab x`): `(stab x).relIndex support = finrank k M`.

Proof. Let `S = stab x` and `Q = support / S`. For each `q : Q` choose a representative
degree `r q`, a nonzero `u q ∈ 𝒜 (r q)` and set `y q = ρ (u q) x`; then `y q ≠ 0`.

1. The operators `ρ v`, for `v` homogeneous of a degree in `S`, commute pairwise
   (`commute_of_mem_stab`). Each `y q` is a common eigenvector (`exists_map_map_eq_smul`),
   with a character `χ q`.
2. `χ` is injective. Suppose `χ q = χ q'`. Take `w ∈ 𝒜 (r q' - r q)` with
   `ρ w * ρ (u q) = ρ (u q')`, so `y q' = ρ w (y q)` and `w ≠ 0`. For `v` of degree in `S`,
   `ρ w * ρ v = c • (ρ v * ρ w)`. Applying both sides to `y q` gives `c = 1`, because `y q`
   and `y q'` have the same eigenvalue for `ρ v` and that eigenvalue is nonzero. So
   `r q' - r q ∈ perp S ⊆ S`, that is, `q = q'`.
3. The `y q` are linearly independent. Common generalized eigenspaces of a commuting family
   for distinct characters are independent (Mathlib's
   `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo`, then
   `iSupIndep.linearIndependent`).
4. The `y q` span `M`. Choose a functional `φ` with `φ x = 1`. Since `ρ` is surjective,
   every `z ∈ M` is `ρ t x` with `ρ t = φ(·) z`. Decompose `t` into homogeneous components.
   For `m` of degree `i` in the support, let `q` be the class of `i`. Then
   `ρ m = ρ (u q) * ρ w` with `w` of degree `i - r q ∈ S`. So `ρ w x` is a multiple of `x`,
   and `ρ m x` is a multiple of `y q`.

So the `y q` form a basis of `M` indexed by `Q`, and `Nat.card Q = finrank k M`.

**`relIndex_radical_stab`** (also `CharZero k`, same hypotheses):
`radical.relIndex (stab x) = finrank k M`. The published `finite_cosets_and_card_eq` gives
`radical.relIndex support = (finrank k M)^2`. Then `AddSubgroup.relIndex_mul_relIndex` and
`relIndex_stab_support` give the result after cancelling `finrank k M ≠ 0`.

**`exists_stab_gt`** (`IsAlgClosed k`, `x₀ ≠ 0`, `a ∈ perp 𝒜 ρ (stab x₀)`): some `y ≠ 0`
satisfies `stab x₀ ≤ stab y` and `a ∈ stab y`. Let `E` be the common eigenspace of the
operators of degrees in `stab x₀` for the eigenvalues they have on `x₀`. `E` contains `x₀`.
For a nonzero `u ∈ 𝒜 a`, `ρ u` commutes with these operators, so it preserves `E`. An
eigenvector `y ∈ E` of `ρ u` works, since `𝒜 a` is spanned by `u`.

**`exists_perp_subset_stab`** (`IsAlgClosed k`, `CharZero k`, `M` finite-dimensional and
nontrivial, `ρ` surjective): some `x ≠ 0` satisfies `perp 𝒜 ρ (stab x) ⊆ stab x`. Every
`stab x` has nonzero index in the support: it contains the radical, whose index is
`(finrank k M)^2 ≠ 0`. Take `x₀ ≠ 0` minimizing this index (`Nat.find`). If some
`a ∈ perp (stab x₀)` were not in `stab x₀`, `exists_stab_gt` would give `y` with
`stab x₀ < stab y`. Then the index of `stab y` would be strictly smaller (by
`relIndex_mul_relIndex`), contradicting minimality.

## Relation to the source

Renard proves `[H : T] = m` by inducing `ρ_T` to `H` and uses the duality between tori and
lattices. He chooses `W` with `H = H̃` by successive replacement. Here both are replaced by
the linear algebra above. The algebra acts on `M = Hom(ind ρ, π)` of dimension `m` through
all of `End(M)`, and the radical has index `m²` in the support. A line whose stabilizer
contains its `perp` gives a basis of `M` indexed by `support / stab x`. The existence of such
a line uses a minimal-index argument in place of Renard's replacement procedure.
