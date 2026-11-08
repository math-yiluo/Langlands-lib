# Simple roots reversed along a path

This module is an internal prerequisite for the quasi-split Steinberg quotient
task, specifically for the even type `A` case (Steinberg 1965, §9.10–9.19). It
proves the following without a classification of Dynkin diagrams. Suppose a
group acts on the simple roots by pairing-preserving permutations, and some
element moves a simple root `a` to a simple root that is not orthogonal to
`a`. Then
the connected component of `a` in the Dynkin diagram is a simply-laced path
`β 0, …, β (2m - 1)` of even length, that is, a diagram of type `A_{2m}`. The
element reverses this path, and `a` is the vertex `β (m - 1)`. Reversal then
gives `ρ γ a = β m`, so the swapped pair is the middle edge of the path. The
host task intends to index the even type `A` substitute products and the
fundamental representation of the `A_{2m}` factor by this path.

## Setting

All results are in the namespace `Langlands.LinearAlgebra.RootDatumReversedPath`.
The setting is that of `Langlands.LinearAlgebra.RootDatumOrbitPairs`.
`P : RootDatum ι M N` is a Mathlib root datum (a root pairing over `ℤ`). Its
index type `ι` is finite and `M`, `N` are arbitrary additive commutative
groups. The roots need not span `M`, and `P` need not be reduced. `b : P.Base`
is a base, `Γ` is a group and `ρ : Γ →* Equiv.Perm b.support` acts on the simple
roots. `IsPairingCompatible b ρ` (from `RootDatumOrbitPairs`) states that each
`ρ γ` is the restriction of a permutation of all root indices preserving
`P.pairing`. `P.IsOrthogonal i j` is Mathlib's orthogonality: both pairings
vanish. `Fin.rev` is the order-reversing involution `i ↦ 2m - 1 - i` of
`Fin (2m)`.

## Definition

`IsReversedPath σ β`, for a permutation `σ : Equiv.Perm b.support`, a natural
number `m` (implicit) and `β : Fin (2 * m) → b.support`, is a structure in `Prop`
with the following fields.

1. `pos`: `0 < m`. `injective`: `β` is injective.
2. `pairing_eq`: the pairings along the path are those of the Cartan matrix of
   type `A_{2m}`. `P.pairing (β i) (β j)` is `2` if `i = j`, `-1` if
   `i + 1 = j` or `j + 1 = i`, and `0` otherwise.
3. `apply_eq_rev`: `σ (β i) = β (Fin.rev i)` for all `i`, so `σ` reverses the
   path.
4. `isOrthogonal`: every simple root `z` outside the range of `β` is orthogonal
   to every `β i`.

Fields 2 and 4 together say that the range of `β` is a connected component of
the Dynkin diagram of the base, that this component is of type `A_{2m}`, and
that `β` lists its vertices in path order. Field 2 makes the component
simply-laced: both pairings along each edge are `-1`.

## Result

`exists_isReversedPath`: assume `hρ : IsPairingCompatible b ρ`, `γ : Γ` and a
simple root `a` with `ρ γ a ≠ a` and `¬ P.IsOrthogonal a (ρ γ a)`. Then there
are `m : ℕ` and `β : Fin (2 * m) → b.support` with `IsReversedPath (ρ γ) β` and
`β i = a` for the index `i` with `i + 1 = m`. In particular `β` enumerates
the connected component of `a`.

## Proof as implemented

Choose a `Fintype` structure on `ι` and let `σ = ρ γ`. Let `B = P.RootForm` be
Mathlib's canonical form. As in `RootDatumOrbitPairs`, private lemmas (re-proved
here because the originals are private) give the following.

- `B` is symmetric, and it is invariant under a pairing-preserving permutation
  of the indices. Hence `σ` preserves both the pairing and `B` on simple roots.
- `2 B(α_u, α_v) = ⟨α_v, α_u^∨⟩ B(α_u, α_u)`.
- `B(x, x) > 0` for nonzero `x` in the integral root span.
- For distinct simple roots, pairings and values of `B` are `≤ 0`. A nonzero
  pairing `⟨α_v, α_u^∨⟩` gives `2 B(α_u, α_v) ≤ -B(α_u, α_u)`.

**Test vectors.** For disjoint finite sets `W`, `E` of simple roots with `E`
nonempty and `c ∈ ℤ`, the vector `c Σ_W α + Σ_E α` is nonzero by linear
independence of the base, since its coefficient at an element of `E` is `1`.
So its norm is positive. The module uses this with
`E = {x}`, `E = {x, y}` (`c = 1, 2`) and `E = {x, y, z, w}` (`c = 2`),
after expanding the norm bilinearly.

`RootDatumOrbitPairs` gives `P.pairing a (σ a) = P.pairing (σ a) a = -1` and
`σ (σ a) = a`. Write `n = B(α_a, α_a)`.

**Half paths.** A half path of length `k ≥ 1` is a sequence `p 0 = a, …,
p (k - 1)` together with the finite set `W = {p i, σ (p i) : i < k}`, subject to
the following conditions (the private structure `IsHalfPath`).

- `σ (σ (p i)) = p i` and `B(α_{p i}, α_{p i}) = n`.
- `P.pairing (p i) (p j)` follows the path pattern `2, -1, 0`.
- `P.pairing (p i) (σ (p j))` is `-1` for `i = j = 0` and `0` otherwise.
- `B(S, S) = n` for `S = Σ_{u ∈ W} α_u`.
- Every simple root `z ∉ W` is orthogonal to `p i` and `σ (p i)` for
  `i + 1 < k`, and `B(S, α_z) = B(α_{p (k-1)}, α_z) + B(α_{σ (p (k-1))}, α_z)`.

The initial half path is `p ≡ a`, `W = {a, σ a}`.

**Extension step.** Let `p = p (k - 1)`, `q = σ p`, and let `x ∉ W` with
`P.pairing x p ≠ 0`. Put `y = σ x`. The private lemma `neighbour` derives the
following facts.

- (a) `x` is orthogonal to `q`. Otherwise the norm of `S + α_x` would be at
  most `n + n_x - n - n_x = 0`.
- (b) `y ∉ W`, since `σ` maps the complement of `W` into itself.
- (c) `y` is not orthogonal to `q`, `y` is orthogonal to `p`, and `x ≠ y`.
- (d) `P.pairing x p = P.pairing p x = -1` and `n_x = n`. If the first pairing
  were `≤ -2`, the norm of `2 S + α_x + α_y` would be `≤ 0`. If the second were
  `≤ -2`, the norm of `S + α_x + α_y` would be `≤ 0`.
- (e) `x` and `y` are orthogonal, since otherwise the norm of
  `S + α_x + α_y` would be `≤ 0`.

`neighbour_unique` shows the outside neighbour of `p` is unique. For a second
one `z ≠ x`, the four roots `x, y, z, σ z` are distinct and outside `W`, and the
norm of `2 S + α_x + α_y + α_z + α_{σ z}` is at most `4n - 8n + 4n = 0`.
Consequently `σ (σ x) = x`, because `σ (σ x)` is again an outside neighbour of
`p`. `outside_ortho` shows that every other outside root is orthogonal to both
`p` and `q`. `extend` then checks all conditions for the half path
`Function.update p k x` of length `k + 1` with set `insert x (insert y W)`.
For instance, the new sum `S + α_x + α_y` has norm `n - n - n + n + n = n`.

**Termination.** The vertices `p i` are distinct, since equal ones would have
pairing `2`, which the pattern excludes. So `k ≤` the number of simple roots.
Induction on a fuel bound (`exists_terminal`) yields a half path without
outside neighbours of its last vertex. `terminal` shows that every simple root
outside `W` is then orthogonal to all of `W`. The end `σ (p (k - 1))` has no
outside neighbour either, because `σ` would map one to a neighbour of
`p (k - 1)`.

**The path.** With `m = k`, put `β i = p (m - 1 - i)` for `i < m` and
`β i = σ (p (i - m))` for `i ≥ m`. The pairing pattern follows from the two
half-path patterns by case analysis on the indices. Pairings
`⟨σ u, v⟩` are rewritten as `⟨u, σ v⟩` using `σ (σ v) = v`. Injectivity follows
from the pattern. Reversal `σ (β i) = β (rev i)` follows from
`σ (σ (p j)) = p j`. The range of `β` is `W`, so the terminal orthogonality gives
the field `isOrthogonal`. Finally `β (m - 1) = p 0 = a`.

## Scope

The module is pure root-datum combinatorics. It does not identify the path
with a factor of the group, and it does not treat other group elements, which
may move the component to another component. It constructs no Steinberg
cross-section. Those remain obligations of the host task.
