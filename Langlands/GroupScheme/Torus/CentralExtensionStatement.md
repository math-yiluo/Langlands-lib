# A central extension of a torus by a torus is a torus: statement

Worker 1395.

`CentralTorusExtensionStatement.{u}` concerns a field `k : Type u`, a
group scheme `E` over `Spec (CommRingCat.of k)`, a commutative group
scheme `Z` over `Spec k` and a homomorphism `z : Z.toGrp ⟶ E`, with these
hypotheses:

- `IsTorus Z.toGrp`;
- `IsClosedSubgroup z`: the underlying morphism of schemes is a closed
  immersion;
- `IsCentral z`: every point of `Z`, over every test scheme, maps into the
  centre of `E` (the Library's `center E` from `Rational.Characters`).

Let `T` be a commutative group scheme over `Spec k` with `IsTorus T.toGrp`,
and let `p : E ⟶ T.toGrp` be a homomorphism with these hypotheses:

- `IsAffineHom p.hom.hom.left`: the underlying morphism of schemes is
  affine;
- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) p`: the
  underlying morphism of schemes is flat, surjective and locally of finite
  presentation, and the range of the scheme-theoretic kernel `kernelι p` is
  `SubgroupFunctor.range z`.

The statement asserts `IsTorus E`.

`E` is not assumed smooth, connected or commutative, and `E` itself is not
assumed affine over `k`: only the morphism `p` is.

This file only defines a proposition and proves nothing. It is a premise
of [`CentralMaximalTorusQuotientReductionStatement`](CentralMaximalQuotientReduction.md).

## Source

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`.
The statement is derived from results of Chapter 12; it is not a numbered
result of Milne in this form.

- Corollary 12.41, printed p.244 (one-based PDF p.260): "Let N be a normal
  subgroup of an algebraic group H such that N and H/N are of
  multiplicative type. Every action of a connected algebraic group G on H
  by group homomorphisms preserving N is trivial."
- Corollary 12.22, printed p.239 (one-based PDF p.255): "An extension of
  algebraic groups of multiplicative type is of multiplicative type if and
  only if it is commutative."
- Corollary 12.42, printed p.244 (one-based PDF p.260), which combines the
  two: "An extension of algebraic groups of multiplicative type is of
  multiplicative type if it is connected."
- After Definition 12.14 and its consequences, printed p.240 (one-based PDF
  p.256): "The tori are the groups G of multiplicative type such that
  X*(G) is torsion-free."

## Derivation

`z` is a closed immersion whose range is the kernel of the fppf quotient
map `p`, so `Z` is the kernel of `p` and `p` identifies `T` with `E/Z`.
Fppf-locally on `T`, `E` is isomorphic to `T × Z`, so `E` is an algebraic
group (of finite type over `k`). Since `T` is affine and `p` is affine, `E`
is affine. Thus `E` is an extension of the torus `T` by the torus `Z`.

Milne's 12.42 assumes `E` connected; here centrality of `Z` replaces
connectedness. Since `Z` is central, the action of `E` on itself by inner
automorphisms is trivial on `Z` and factors through an action of
`T = E/Z`, by group homomorphisms preserving `Z`. The torus `T` is
connected, so Corollary 12.41, with `G = T`, `H = E` and `N = Z`, makes
this action trivial. Hence `E` is commutative, and by Corollary 12.22 it is
of multiplicative type. The character groups give an exact sequence
`0 → X*(T) → X*(E) → X*(Z) → 0`, so `X*(E)` is torsion-free and `E` is a
torus.

The centrality hypothesis is what the reduction can supply: there `E` is
the inverse image of a torus under a quotient map by a central torus, and
connectedness of `E` would be harder to prove than centrality.

## Correspondence with the source

- `IsTorus` is the Library's definition from `Torus.Lattice`: split after
  base change to some field extension of `k` (Milne, Definition 12.14,
  printed p.236, one-based PDF p.252).
- Tori are commutative, so letting `Z` and `T` range over commutative
  group schemes loses no torus.
- The hypothesis `IsClosedSubgroup z` makes `Z` itself the kernel of `p`,
  as in Milne's setting of a normal subgroup `N` and its quotient. The
  statement's consumer supplies it.
- The hypothesis `IsAffineHom p.hom.hom.left` follows from the other
  hypotheses, so it does not restrict the source's setting: `p` is a
  torsor under the affine group `Z`, so `p` is affine by fpqc descent of
  affineness. Neither Mathlib nor the Library
  has that descent, so the statement assumes it. The consumer
  [`CentralMaximalTorusQuotientReductionStatement`](CentralMaximalQuotientReduction.md)
  supplies it, because there `p` is a base change of an affine morphism.
