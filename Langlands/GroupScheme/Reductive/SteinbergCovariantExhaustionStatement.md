# Covariant exhaustion by Steinberg-type products

`Langlands.GroupScheme.SteinbergCovariantExhaustionStatement` is an open
proposition. It is not an assumed theorem, and nothing in this file proves it.

## Statement

Fix a field `k : Type u`, algebraically closed and of prime characteristic `p`.
Fix an actual group scheme `G` over `Spec k` with affine structure morphism
that is simply connected (`IsSimplyConnected`, which includes semisimplicity).
The proposition asserts that there exist:

- an abelian group `Λ : Type u` and an actual homomorphism
  `j : D(Λ) → G` from the diagonalizable group;
- actual group schemes `H` and `H'` with affine structure morphisms, actual
  homomorphisms `i : H → G` and `i' : H' → G`, and coordinates `χ` of `H` and
  `ψ` of `H'`.

Write `X_e = leftCovariantSubspace i (χ ^ e)` for the coordinates `f` of `G`
with `f(i(h) g) = χ(h)^e f(g)`, expressed with the coaction, and
`Y_e = leftCovariantSubspace i' (ψ ^ e)` likewise. These data must satisfy four
conditions.

1. The difference comorphism of the actual pullbacks of `i` and `i'`,
   `Chevalley.differenceComorphism`, is injective. This is the comorphism of
   `(p, q) ↦ i(p) i'(q)⁻¹`. Injectivity says these products are schematically
   dense in `G`.
2. `1 ∈ X_1 * Y_1`, where `*` is the product of submodules of the coordinate
   algebra.
3. Every coordinate `w` that is left `j`-invariant on all test schemes, meaning
   `w(j(h) g) = w(g)` for all relative test schemes `T`, all `h ∈ D(Λ)(T)` and
   all `g ∈ G(T)`, lies in `X_e * Y_e` for some `e`.
4. For every `e` there is `e' ≥ e` and `m` such that `X_e'` and `Y_e'` have
   bases indexed by `Fin m`, and the finite regular representation of `G` on
   `X_e'`, by right translation, is rationally irreducible. Irreducibility is
   that of `rationalRepresentation` in the published
   `Chevalley.affineRegularRepresentation`, which is basis independent.

The binder `[IsAffineHom G.X.hom]` is redundant for simply connected `G`. The
reduction obtains it from `IsSimplyConnected` before applying the
proposition.

## Provenance

This is an internal interface derived from the proof sketch of Theorem A.1.0,
(a) implies (b), in Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*,
third enlarged edition (1994), Appendix to Chapter 1, Section A, printed p.192.
The registered source is `mumford-fogarty-kirwan-1994-git-3rd`, SHA-256
`25b78ea299e007fbabefb23e9dd7d30beba86c5c1eaa9718b8cc3f98f54932b2`.

In that sketch `T` is a maximal torus inside a Borel subgroup `B`, `ρ` is half
the sum of the positive roots, and `W_(mρ) = H^0(G/B, L(mρ))`. The page states,
citing Steinberg, that `W_(mρ)` is irreducible and self-dual for `m = p^s - 1`.
It also states that the right-`T`-invariant regular functions form an increasing
union of copies of `W_(mρ) ⊗ W_(mρ)`. Conditions 3 and 4 correspond to these
two assertions. Condition 3 is the increasing-union assertion, read in
coordinate form. Condition 4 is the irreducibility assertion, weakened to the
first factor and to equal dimensions.

Conditions 1 and 2, and the identifications below, are the author's own
reconstruction. They are not stated on that page. The reduction uses them to
derive the injectivity behind the word "copies" and the directedness of the
union.

The intended witnesses, which this file does not construct, are as follows:
`j` a split maximal torus, `i` and `i'` the inclusions of a Borel subgroup `B`
containing it and of the opposite Borel subgroup `B⁻`, and `χ`, `ψ` characters
extending `±ρ` with signs fixed by the left-covariance convention. Then:

- `X_e` and `Y_e` are coordinate models of section modules on `G/B` and `G/B⁻`;
- condition 1 should follow from density of the big cell `B B⁻`, using the
  published opposite-cell theorem;
- condition 2 should come from a bi-covariant function `c` with `c(1) = 1`,
  through `1 = Σ c₁ S(c₂)`;
- condition 4 at `e = p^s - 1` is Steinberg's irreducibility, and both spaces
  should have dimension `p^(sN)`, where `N` is the number of positive roots.

Simple connectedness is what makes `ρ` a character of `T`.

The published `SteinbergBigCellStatement` records big-cell and Steinberg
data, in the form `i' = i ≫ inn(n)` and `ψ = χ`, from which this proposition
is intended to be derived. That derivation is not part of this file.

Compared with the source, the proposition is weaker in several ways. It does
not fix a maximal torus or Borel subgroups. It allows any subgroup maps and
coordinates. It does not ask for self-duality or for the factors to be equal.
It asks only for cofinal irreducibility of the first factor and equal
dimensions. Side conventions also differ: the Library uses right translation
and left invariance, which inversion exchanges with the source's conventions.
