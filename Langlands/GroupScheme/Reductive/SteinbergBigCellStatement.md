# Big-cell and Steinberg data for simply connected groups

`Langlands.GroupScheme.SteinbergBigCellStatement` is an open proposition. It is
not an assumed theorem, and nothing in this file proves it.

## Statement

Fix a field `k : Type u`, algebraically closed and of prime characteristic `p`.
Fix an actual group scheme `G` over `Spec k` with affine structure morphism
that is simply connected (`IsSimplyConnected`, which includes semisimplicity).
The proposition asserts that there exist:

- an abelian group `Λ : Type u` and an actual homomorphism
  `j : D(Λ) → G` from the diagonalizable group;
- an actual group scheme `H` with affine structure morphism and an actual
  homomorphism `i : H → G`;
- a rational point `n` of `G`, giving the conjugate homomorphism
  `i' = i ≫ inn(n)`, so `i'(h) = n i(h) n⁻¹` on every test scheme;
- a coordinate `χ` of `H` and a coordinate `d` of `G`.

All points below are points with values in an arbitrary relative test scheme
`T` over `Spec k`; `T` need not be affine or reduced. Values of coordinates
are taken with `AffineCoordinates.pointAlgebraHom`, so they lie in the global
sections of `T`. The data must satisfy seven conditions.

1. Left covariance: `d ∈ leftCovariantSubspace i χ`, that is,
   `d(i(h) g) = χ(h) d(g)`, expressed with the coaction.
2. Right covariance for the conjugate: `d(g · i'(h)⁻¹) = χ(h) d(g)` for all
   `h ∈ H(T)` and `g ∈ G(T)`. The same coordinate `χ` appears on both sides.
3. Normalization: `d(1) = 1` at the identity rational point.
4. `d` is a nonzerodivisor of the coordinate algebra of `G`.
5. Decomposition: if `g ∈ G(T)` and `d(g)` is a unit, then
   `g = i(b) · i'(b')⁻¹` for some `b, b' ∈ H(T)`.
6. Intersection: if `c, c' ∈ H(T)` and `i(c) = i'(c')`, then
   `i(c) = j(t)` for some `t ∈ D(Λ)(T)`.
7. Cofinal irreducibility: for every `e` there are `e' ≥ e` and `m` such that
   `leftCovariantSubspace i (χ ^ e')` has a basis indexed by `Fin m`, and the
   finite regular representation of `G` on this space, by right translation,
   is rationally irreducible. The representation is the published
   `Chevalley.affineRegularRepresentation`; its stability hypothesis is supplied
   by the published `AffineCoordinates.rightAct_mem_leftCovariantSubspace`.
   Irreducibility is that of its `rationalRepresentation`, which is basis
   independent.

Conditions 5 and 6 are formulated on all test schemes, so they are
scheme-theoretic: condition 5 says that the principal open set `D(d)` lies in
the image of `(b, b') ↦ i(b) i'(b')⁻¹`, and condition 6 says that the
fibre product of `i` and `i'` over `G` maps into `j`.

## Intended witnesses

The file does not construct the following witnesses. They are recorded to
explain why the proposition should hold.

Let `T₀` be a maximal torus, split over the algebraically closed field `k`, and
take `Λ = X*(T₀)` (lifted to `Type u`) with `j : D(Λ) ≅ T₀ → G`. Let `B` be a
Borel subgroup containing `T₀`, with positive roots those of `B`, take `H = B`
with `i` its inclusion, and let `n` represent the longest Weyl element, so
`i'` is the inclusion of the opposite Borel subgroup `B⁻ = n B n⁻¹`. Since `G`
is simply connected, `ρ`, half the sum of the positive roots, is a character
of `T₀`. Take `χ` to be the character of `B` extending `-ρ`.

- For `d`, take the matrix coefficient `g ↦ ξ(g v)`, where `v` spans the
  lowest weight space, of weight `-ρ`, in a rational `G`-module of highest
  weight `ρ`, and `ξ` is the projection onto that weight space. Since the
  unipotent radical of `B` raises weights, `d(b g) = (-ρ)(b) d(g)`. Since `B⁻`
  stabilizes the line through `v`, `d(g b⁻) = μ(b⁻) d(g)` for the character
  `μ` of `B⁻` extending `-ρ`. For `b⁻ = (n h n⁻¹)⁻¹` with `h ∈ B` one has
  `μ(b⁻) = χ(h)` because `w₀ ρ = -ρ`; this is condition 2.
- By the Bruhat decomposition and regularity of `ρ`, `d` vanishes nowhere on
  the big cell `B B⁻` and everywhere off it. The published opposite-cell
  theorem (`Langlands.GroupScheme.oppositeCellStatement`) makes the big cell an
  open subscheme isomorphic to `U × B⁻`, which gives conditions 5 and 6, with
  `B ∩ B⁻ = T₀` scheme-theoretically. `G` is a connected smooth group over a
  field, so its coordinate algebra is a domain and condition 4 follows from
  `d ≠ 0`.
- `leftCovariantSubspace i (χ ^ e)` is the coordinate model, via inversion, of
  the section module that the source writes `H⁰(G/B, L(eρ))`, up to the sign
  conventions for line bundles on `G/B`. At `e = p^s - 1` it is the Steinberg
  module, which is irreducible. This gives condition 7.

## Intended use

The proposition is meant to be the remaining structural and
representation-theoretic input for the published
`SteinbergTensorEmbeddingStatement`, through a reduction that is not part of
this file. In that reduction, conditions 1 to 6 give injectivity of
multiplication of covariant coordinates and the exhaustion of left
`j`-invariant coordinates by products of covariant coordinates of weights
`χ ^ e` on both sides. Translation of covariant coordinates by `n`, which
exchanges covariance for `i` and for `i'` with the same weight, gives the two
factors equal dimension, and
condition 7 gives irreducibility of the first factor.

## Provenance

The proposition is an internal interface for the proof sketch of Theorem
A.1.0, (a) implies (b), in Mumford, Fogarty and Kirwan, *Geometric Invariant
Theory*, third enlarged edition (1994), Appendix to Chapter 1, Section A,
printed p.192. The registered source is `mumford-fogarty-kirwan-1994-git-3rd`,
SHA-256 `25b78ea299e007fbabefb23e9dd7d30beba86c5c1eaa9718b8cc3f98f54932b2`.

That page fixes a maximal torus `T`, a Borel subgroup `B ⊃ T` and `ρ`, sets
`W_(mρ) = H⁰(G/B, L(mρ))`, and states, citing Steinberg, that `W_(mρ)` is
irreducible for `m = p^s - 1`. Condition 7 is this irreducibility assertion,
read in left-covariant coordinate form and weakened to cofinally many
exponents of a single coordinate `χ`.

Conditions 1 to 6 are the author's own reconstruction. They are not stated on
that page, which does not mention the big cell. They are the geometric input
from which the page's assertion that the right-`T`-invariant regular functions
form an increasing union of copies of `W_(mρ) ⊗ W_(mρ)` is intended to be
derived, together with the facts used to show that these copies are embedded.

Compared with the source, the proposition is weaker. It does not require `j`
to be a maximal torus, `i` a Borel subgroup or `n` a Weyl element. It allows
any subgroup map, rational point and coordinates satisfying the listed
conditions. It omits self-duality and the dimension of the Steinberg module.
Side conventions differ from the source: the Library uses right translation and
left covariance, which inversion exchanges with the source's conventions.

The binder `[IsAffineHom G.X.hom]` is redundant for simply connected `G`.
