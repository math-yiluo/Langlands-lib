# Simplicity of a nonzero compact-open fixed space over the Hecke corner

This module states a proposition. It proves nothing.

## The statement

`Langlands.Hecke.CornerFixedVectorsSimplicityStatement.{uG,uV}` is a `Prop`
quantifying over all of the following:

- a group `G : Type uG` that is a Hausdorff, locally compact, totally disconnected
  topological group, with its Borel measurable structure;
- a left Haar measure `μ` on `G` (`μ.IsHaarMeasure`);
- a bundled smooth complex representation `A : SmoothRep.{0, uG, uV} ℂ G`, which is
  irreducible (`A.IsIrreducible`);
- an open subgroup `K` of `G` with `hK : IsCompact (K : Set G)` and a nonzero
  `K`-fixed space: `fixedVectors A.representation K.toSubgroup ≠ ⊥`.

It asserts `IsSimpleModule (HeckeAlgebra.Corner μ K hK) (fixedVectors
A.representation K.toSubgroup)`. Here the module structure is exactly the published
`cornerModule μ A.representation A.isSmooth K hK`. So the fixed space is a nontrivial
module over the corner, and its only corner-submodules are `⊥` and `⊤`.

The objects in the statement are the Library's existing constructions, unchanged:

- `HeckeAlgebra.Corner μ K hK` is the unital algebra of `K`-bi-invariant, locally
  constant, compactly supported complex functions. Its product is convolution
  with respect to `μ`, and its unit is the normalized indicator `μ(K)⁻¹ 1_K`.
- `cornerModule` lets `f` act on a `K`-fixed vector `v` by the integrated
  operator `∫ f(g) • A(g) v dμ(g)`. It is the module structure induced by the
  published algebra homomorphism `cornerAction`.
- `fixedVectors A.representation K.toSubgroup` is the existing submodule of
  `K`-fixed vectors of the carrier.
- `A.IsIrreducible` is Mathlib's `Representation.IsIrreducible` for the
  underlying representation. That means the lattice of subrepresentations is a
  simple order: the representation is nonzero and has no subrepresentations
  other than `0` and the whole space.

The universes `uG` of the group and `uV` of the representation carrier are
independent. The coefficient ring `ℂ` lives in `Type 0`.

No other hypotheses are assumed. In particular, the statement does not assume:

- admissibility or finite dimension of any fixed space;
- compact matrix coefficients;
- sigma-compactness or countability at infinity;
- unimodularity;
- finite generation.

The nonzero hypothesis on the fixed space is necessary, because the zero module
is not simple.

## Source and provenance (derived)

This is the forward implication of Bernstein–Zelevinsky (1976), Proposition
2.10(a), printed pages 17–18 (PDF page index equals printed page). The source is
registered as `bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`, retained at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.

Proposition 2.10(a) says that `π` is irreducible if and only if `π ≠ 0` and, for
every open compact subgroup `N`, either `E^N = 0` or `π_N` is irreducible. This
module states only the following consequence of the "only if" direction: for an
irreducible `π` and one compact open subgroup with `E^N ≠ 0`, `π_N` is
irreducible.

The translation of the source's notions:

- **Group.** In the source `G` is an l-group (1.1, p. 6). That is a topological
  group with a fundamental system of compact open subgroups at the identity. By
  the remark in 1.1, this is the same as being an l-space: Hausdorff, locally
  compact and zero-dimensional. The Lean hypotheses `T2Space`,
  `LocallyCompactSpace` and `TotallyDisconnectedSpace` express this setting.
- **Representations.** The source's representations in `Alg G` are the algebraic
  ones (2.1, p. 15): every vector has an open stabilizer. In Lean these are the
  objects of `SmoothRep`. A `G`-module is irreducible in the source (p. 15) when it
  is nonzero and has no `G`-submodules except `0` and `E`. This is
  `A.IsIrreducible`.
- **Corner algebra.** The source sets `ℋ_N = ε_N * S*_c(G) * ε_N`, a convolution
  algebra of compactly supported distributions with unit `ε_N` (2.10, p. 17).
  Here `ε_N` is the normalized Haar measure of `N` (1.26, p. 13). By 1.28–1.30
  (p. 14), the locally constant compactly supported distributions are exactly
  the `f · μ` with `f` a locally constant compactly supported function. Under
  this identification, convolution of distributions becomes `μ`-convolution of
  functions. So `ℋ_N` is the algebra of `N`-bi-invariant compactly supported
  locally constant functions, and `ε_N` becomes `μ(N)⁻¹ 1_N`. This is the
  published `HeckeAlgebra.Corner μ K hK` for the chosen Haar measure `μ`. The
  statement quantifies over every Haar measure.
- **Action.** For `T = f · μ`, the source's operator
  `π(T)ξ = ∫ π(g)ξ dT(g)` (2.3, p. 15) is `∫ f(g) π(g)ξ dμ(g)`. This is the
  operator of `cornerAction`, with the same positive `π(g)` convention. The
  source's "natural representation `π_N` of `ℋ_N` in `E^N`" is therefore the
  published `cornerModule` on `fixedVectors`. Its irreducibility as an algebra
  representation is `IsSimpleModule`. Scalars act through the unit, so the
  `ℋ_N`-invariant subspaces are exactly the corner-submodules.

The statement does not ask for:

- the converse direction of 2.10(a);
- the condition over all compact open subgroups;
- clause 2.10(b), detecting equivalence through `π_N`;
- clause 2.10(c), realizing every simple `ℋ_N`-module.

## Source proof idea

This is not part of the statement. Let `V` be an `ℋ_N`-invariant subspace of
`E^N`, and let `E'` be the `G`-submodule it generates. Then
`E'^N = π(ε_N) E'`. This space is spanned by the vectors
`π(ε_N * T * ε_N) v` with `v ∈ V`, so it equals `V`. Irreducibility of `E` then
forces `V = 0` or `V = E^N`.

## Related Library result

The published theorem `Langlands.CompactCoefficientClass.isSimpleModule_fixedVectors`,
in `Langlands/Representation/CompactCoefficient/FixedLevelFiniteness.lean`, has the
same conclusion for an unbundled irreducible smooth representation. Its hypotheses
on the group are weaker: any topological group with a Borel left Haar measure. This
statement module does not import it.
