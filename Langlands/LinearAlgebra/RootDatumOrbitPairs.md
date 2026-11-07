# Orbits of pairing-preserving actions on simple roots

This module is an internal prerequisite for the quasi-split Steinberg quotient
task. It describes the orbits of a group that acts on the simple roots of a
root datum and preserves the integral pairing. Each simple root is orthogonal
to every other root in its orbit, with at most one exception. If an exception
`c` exists, then `a` and `c` form an `A₂` pair: both pairings are `-1`, the
group element moving `a` to `c` swaps them, and `a + c` is a root. In
Steinberg's construction, ordinary products work for orthogonal orbits. In type
`A_n` with `n` even, the two middle simple roots form such an `A₂` pair, and
the modified products are used for it. The module uses no classification of
Dynkin diagrams.

## Setting

All results are in the namespace `Langlands.LinearAlgebra.RootDatumOrbitPairs`.
`P : RootDatum ι M N` is a Mathlib root datum, that is, a root pairing over `ℤ`.
Its index type `ι` is finite and `M` and `N` are arbitrary additive commutative
groups. The roots need not span `M`, and `P` need not be reduced. `b : P.Base`
is a base, `Γ` is a group and `ρ : Γ →* Equiv.Perm b.support` is a group action
on the simple roots.

`IsPairingCompatible b ρ` states that for every `γ : Γ` there is a permutation
`e` of all root indices with two properties. It preserves the pairing,
`P.pairing (e i) (e j) = P.pairing i j` for all `i j`, and it extends the action,
`(ρ γ a : ι) = e a` for every simple root `a`. Such an `e` exists, for example,
when `ρ γ` is the restriction of the index permutation of a root-datum
automorphism (`RootPairing.Hom.pairing`). `IsPairingCompatible.pairing_apply`
records that the action preserves the pairing of simple roots.

`P.IsOrthogonal i j` is Mathlib's orthogonality: both pairings
`P.pairing i j` and `P.pairing j i` vanish.

## Results

Each of the following theorems assumes `hρ : IsPairingCompatible b ρ` and
fixes a simple root `a : b.support`.

- `eq_of_not_isOrthogonal`: let `γ δ : Γ` with `ρ γ a ≠ a` and `ρ δ a ≠ a`.
  If `a` is orthogonal neither to `ρ γ a` nor to `ρ δ a`, then
  `ρ γ a = ρ δ a`. In words, `a` has at most one non-orthogonal companion in
  its orbit.
- `pairing_eq_neg_one_of_not_isOrthogonal`: if `ρ γ a ≠ a` and `a` is not
  orthogonal to `ρ γ a`, then `P.pairing a (ρ γ a) = -1` and
  `P.pairing (ρ γ a) a = -1`.
- `apply_apply_eq_of_not_isOrthogonal`: under the same hypotheses,
  `ρ γ (ρ γ a) = a`.
- `exists_root_eq_add_of_not_isOrthogonal`: under the same hypotheses, some
  root index `k` has `P.root k = P.root a + P.root (ρ γ a)`.
- `isOrthogonal_of_forall_pairing_ne_neg_one`: assume that
  `P.pairing a (ρ γ a) ≠ -1` whenever `ρ γ a ≠ a`. Then
  `a ≠ ρ γ a` implies `P.IsOrthogonal a (ρ γ a)`. The conclusion has the shape
  of the Library's `SplitPinning.OrthogonalSimpleOrbits`.

## Proof as implemented

Choose a `Fintype` structure on `ι`. Let `B = P.RootForm` be Mathlib's
canonical form `B(x, y) = Σ_k ⟨x, α_k^∨⟩ ⟨y, α_k^∨⟩`. The private lemmas prove
the following properties of `B`.

- On roots, `B(α_i, α_j) = Σ_k ⟨α_i, α_k^∨⟩ ⟨α_j, α_k^∨⟩`. It is symmetric, and
  a pairing-preserving permutation `e` of the indices leaves it unchanged after
  reindexing the sum by `e`. In particular, all roots in one orbit have the
  same length `ℓ = B(α_a, α_a)`.
- `2 B(α_i, α_j) = ⟨α_j, α_i^∨⟩ B(α_i, α_i)`. This follows by applying
  `α_j` to Mathlib's `rootForm_self_smul_coroot`, the identity
  `B(α_i, α_i) α_i^∨ = 2 Polarization(α_i)`.
- `B(x, x) > 0` for every nonzero `x` in the integral root span. The form is a
  sum of squares. If it vanished at `x`, every coroot would vanish on `x`, so
  `x` would lie in the kernel of `B`. Mathlib's
  `disjoint_rootSpan_ker_rootForm` then gives `x = 0`.

The main step works with the finite orbit `O` of `a`. For `i ∈ O` it considers
the set of companions of `i`: the other elements `j ∈ O` with
`⟨α_j, α_i^∨⟩ ≠ 0`.

1. Elements of `Γ` map companions of `i` injectively to companions of the image
   of `i`, because they preserve the orbit and the pairing. Hence every element
   of the orbit has the same number `d` of companions.
2. Let `x = Σ_{i ∈ O} α_i`. The vector `x` is nonzero by linear independence of
   the base, so `B(x, x) > 0`. By the two formulas above,
   `2 B(x, x) = ℓ · S` with `S = Σ_{i, j ∈ O} ⟨α_j, α_i^∨⟩`, and therefore
   `S > 0`.
3. Distinct simple roots have nonpositive pairing (Mathlib's
   `pairingIn_le_zero_of_ne`), so each nonzero term is at most `-1`. For each
   `i` this gives `Σ_{j ∈ O} ⟨α_j, α_i^∨⟩ ≤ 2 - d`, hence
   `S ≤ |O| (2 - d)`. Together with `S > 0`, this forces `d ≤ 1`, which gives
   `eq_of_not_isOrthogonal`.

The remaining results follow from this bound.

- **`A₂` pairs.** Let `c = ρ γ a ≠ a` be non-orthogonal to `a`. The length
  formula with equal lengths gives `⟨α_a, α_c^∨⟩ = ⟨α_c, α_a^∨⟩ = m`. Here
  `m ≤ 0` and `m ≠ 0`. The vector `α_a + α_c` is nonzero, because distinct
  simple roots are not negatives of each other (`root_ne_neg_of_ne`).
  Positivity `B(α_a + α_c, α_a + α_c) = (2 + m) ℓ > 0` gives `m > -2`, so
  `m = -1`.
- **Swap.** `ρ γ c` is a companion of `c`, because `ρ γ` preserves the pairing.
  So is `a`. Uniqueness of companions gives `ρ γ c = a`.
- **Root sum.** The reflection in `α_c` sends `α_a` to
  `α_a - ⟨α_a, α_c^∨⟩ α_c = α_a + α_c`. Hence `a + c` is a root, namely
  `P.reflectionPerm c a`.
- **Orthogonality.** If `a ≠ ρ γ a` were not orthogonal, the `A₂` result would
  give pairing `-1`, contrary to the hypothesis.

## Scope

The module is pure root-datum combinatorics. It does not show that the ordinary
Galois action of a quasi-split group is pairing-compatible, does not decide
which orbits contain `A₂` pairs, and constructs no Steinberg cross-section.
Those remain obligations of the host task.
