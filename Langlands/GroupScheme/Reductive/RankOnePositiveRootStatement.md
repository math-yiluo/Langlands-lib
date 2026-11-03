# Statement: in semisimple rank one, a cocharacter is positive on at most one root

`Langlands.GroupScheme.RankOnePositiveRootUniquenessStatement` is an unproved
proposition at arbitrary universe `u`. Nothing is proved in this module.

## The statement

Let `k : Type u` be a field and `G` a group scheme over `Spec k` satisfying the
published `IsConnectedReductive G`. Let `T` be a commutative group scheme with
`IsSplitTorus T.toGrp`, and let `i : T.toGrp ⟶ G` satisfy `IsMaximalTorus i`.
These are the hypotheses of `RootReducednessStatement` in
`Langlands.GroupScheme.Reductive.RootReducednessStatement`. The instance
`IsAffineHom G.X.hom`, which `roots i` needs, comes from `hG.isAffineHom`, as in
that statement.

The rank-one hypothesis: for all `α β ∈ roots i`, the pair `![α, β]` is not
linearly independent over `ℤ` in `characterLattice T`.

The conclusion: for every cocharacter `ν : cocharacterLattice T` and all
`α β ∈ roots i`, if `0 < latticePairing T α ν` and `0 < latticePairing T β ν`,
then `α = β`.

Here `roots i` is the published set of nonzero characters of `T` with a nonzero
weight space in the actual Lie algebra `Lie(G)(k)` (`Langlands.GroupScheme.roots`,
in `Langlands/GroupScheme/Torus/Weights.lean`). `latticePairing T` is the
published pairing `⟨χ, ν⟩ = gmEndEquiv k (ν ≫ χ)` between characters and
cocharacters (`Langlands/GroupScheme/Torus/Lattice.lean`).

## Relation to the source

This is a derived statement. Milne does not state it as a numbered result. It is
the rank-one content of Theorem 21.11(b) that does not involve negation of roots.

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`
(printed page = PDF page − 16):

- Theorem 21.11(b), printed p.428 (PDF 444), proof printed p.429 (PDF 445):
  for a split reductive group `(G, T)` over `k` and a root `α` of `(G, T)`, the
  only rational multiples of `α` in `Φ(G, T)` are `±α`.
- Definition 21.10 and the remarks after it, printed p.428 (PDF 444): the root
  group `U_α = U_{G_α}(λ)` for any cocharacter `λ` with `⟨α, λ⟩ > 0`. Its Lie
  algebra has as weights the positive rational multiples of `α` in `Φ` (16.64).
- §20.e, Theorem 20.16 and the discussion after it, printed pp.412–413
  (PDF 428–429): for a connected reductive group of semisimple rank one over an
  algebraically closed field, `T` lies in exactly two Borel subgroups,
  `dim(G/B) = 1`, and the unipotent part `B⁺_u` of a Borel subgroup containing
  `T` is a one-dimensional group isomorphic to `𝔾_a`.

The author's errata page (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists no correction to
pp.412–413 or pp.428–429. Its p.449 entry names "Proposition 21.11", but it
concerns the appeal to 21.67 in the proof of Proposition 21.77 on printed
p.449, not Theorem 21.11.

Milne's split reductive group `(G, T)` is a reductive group `G` with a split
maximal torus `T`, and `Φ(G, T)` is the set of nonzero weights of `T` on
`Lie(G)`. These are the hypotheses above and the published `roots i`.

### Derivation from Theorem 21.11(b)

Let `α` and `β` be roots with `⟨α, ν⟩ > 0` and `⟨β, ν⟩ > 0`. By the rank-one
hypothesis `![α, β]` is linearly dependent over `ℤ`: `m • α + n • β = 0` with
`(m, n) ≠ (0, 0)`. Roots are nonzero by definition, and the character lattice of
a split torus is torsion-free, so `m ≠ 0` and `n ≠ 0`. Hence `β` is a rational
multiple of `α`. Theorem 21.11(b) gives `β = α` or `β = -α`. The second case
would give `⟨β, ν⟩ = -⟨α, ν⟩ < 0`. So `β = α`.

### The rank-one hypothesis

The hypothesis says that all roots lie on one line of `X*(T) ⊗ ℚ`. Milne's
rank-one groups in the proof of 21.11 satisfy it. There `G_α = C_G(T_α)` with
`T_α = (Ker α)°_red`, and by 10.34 the weights of `T` on
`Lie(G_α) = 𝔤^{T_α}` are the weights trivial on `T_α`. These are the
rational multiples of `α`. A group with no roots satisfies the hypothesis
vacuously, and then the conclusion is vacuous too.

## Role

The statement isolates the geometric core of the rank-one case of
`RootReducednessStatement`. Negation stability of the roots is the separate
published statement `RelativeRootNegationStatement`
(`Langlands.GroupScheme.Rational.RelativeRootNegationStatement`). It applies
here because a split maximal torus is a maximal split torus
(`IsMaximalTorus.isMaximalSplitTorus`) and `relativeRoots_eq_roots`. With both,
let `α` and `β` be dependent roots. The lattice pairing of a split torus is
perfect (`IsSplitTorus.isPerfPair_latticePairing`), so some `ν` has `⟨α, ν⟩ > 0`. Then
`⟨β, ν⟩ ≠ 0`. If it is positive, this statement gives `β = α`. If it is
negative, `-β` is a root positive on `ν`, so `-β = α`.

The intended proof follows Milne §20.e and 21.11(b): the subgroup `U_G(ν)` is
smooth and connected with Lie algebra the sum of the weight spaces of the
characters positive on `ν` (the published dynamic Lie algebra results), and in
rank one it has dimension at most one. That bound needs the properness of the
flag variety and the count of torus-fixed points (Milne 20.11–20.12, 20.16).

## Scope

The statement asserts only uniqueness. It does not assert that some root is
positive on `ν`, that `dim 𝔤_α = 1`, that `-α` is a root, or anything about
coroots or reflections. It assumes no root datum and no classification of
rank-one groups.
