# Finite-surjective descent of finite-set affine neighborhoods

Authors: Worker 139 (formulation and source audit) and Worker 1038
(recheck against the Library definitions and the source, and submission).

This module states a derived affine-base specialization of Philipp Gross,
*Tensor generators on schemes and stacks*, Theorem 1.2. It uses only existing
definitions and proves no descent or representability theorem.

## Exact proposition

In namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`, the Prop-valued
definition is
`FiniteSurjectiveFiniteAffineNeighborhoodsDescentStatement.{u}`.

For every commutative ring `R : Type u`, put `S = Spec (CommRingCat.of R)`.
The proposition quantifies over an actual scheme `U : Over S`, an actual
algebraic space `Y : AlgebraicSpace S`, and an actual morphism
`f : (schemeToSpace S).obj U ⟶ Y`. Its hypotheses are:

- `IsQuasiCompact Y`, the existing absolute predicate: there is a
  geometrically surjective etale scheme atlas whose source is topologically
  quasi-compact;
- `IsQuasiSeparated Y`, the existing predicate that the relative diagonal
  over `S` is representable and that every represented scheme pullback of
  that diagonal is a quasi-compact morphism;
- `PointTopology.HasFiniteAffineNeighborhoods U.left`, the existing AF
  predicate on an actual scheme: every finite set of its underlying points
  is contained in a single actual affine open;
- `IsFinite (hom f)` and `IsSurjective (hom f)`, the existing scheme-test
  predicates for the underlying presheaf transformation. They require
  representability and test every represented scheme pullback projection
  for finiteness and geometric surjectivity, respectively.

The conclusion is

```lean
∃ P : Over (Spec (CommRingCat.of R)),
  PointTopology.HasFiniteAffineNeighborhoods P.left ∧
    Nonempty ((schemeYoneda _).obj P ≅ Y.presheaf)
```

Thus it asserts an actual representing scheme over the original base,
with AF on its underlying scheme, and an actual natural isomorphism on
all scheme tests over that base. Geometric surjectivity is not
componentwise surjectivity of a map of presheaves. All schemes and rings
remain in universe `u`, and the existing presheaf values are in
`Type (u + 1)`.

There is no finite-type, noetherian, reducedness, normality,
finite-presentation, flatness or projectivity premise. The source `U`
is not required to be affine, and `Y` is not assumed to be represented by
a scheme. The quasi-compactness and quasi-separatedness premises on `Y`
are retained.

## Original source and derived specialization

The registered source is `gross-tensor-generators-schemes-stacks-2017`,
Philipp Gross, *Tensor generators on schemes and stacks*, Algebraic
Geometry **4** (2017), no. 4, 501–522,
[DOI 10.14231/AG-2017-026](https://doi.org/10.14231/AG-2017-026).
The retained publisher PDF is
`literature/Philipp Gross - Tensor generators on schemes and stacks (Algebraic Geometry 4 no.4, 2017).pdf`,
SHA-256
`fa20fe6fff07a861f93d6640e553f2cc8f48b694487c49e257a089ce52b45e8b`.

Theorem 1.2, printed p. 502 / PDF p. 2, asserts that for a
quasi-compact, quasi-separated algebraic space `X` and a finite
surjection from an algebraic space to `X`, the target is an AF scheme
exactly when the source is. Definition 3.1, printed p. 510 / PDF p. 10,
defines AF using affine Zariski-open neighborhoods of every finite set of
points. The conventions on printed p. 503 / PDF p. 3 retain
quasi-separatedness, in the sense of a quasi-compact, quasi-separated
diagonal. These passages and all of Section 3, printed pp. 510–512 /
PDF pp. 10–12, were read.

Match Gross's target `X` with `Y`, and his source with the algebraic
space associated to `U`. The present proposition uses only the descent
direction. The scheme AF predicate is exactly the finite-set condition,
and the existential conclusion expresses that condition for a scheme
representing the target. Source and target morphisms are actual
algebraic-space morphisms, with finite and surjective interpreted by the
published scheme-test definitions.

The affine base is a deliberate specialization needed for the existing
relative quasi-separatedness interface. In ordinary algebraic geometry,
the relative diagonal of `Y` over `S` followed by the base change of the
diagonal of `S` over `Spec ℤ` is the absolute diagonal. Since `S` is
affine, its diagonal over `Spec ℤ` is a closed immersion. Composing with
it preserves quasi-compactness. The relative quasi-separatedness premise
therefore supplies the source theorem's absolute quasi-separatedness.
Diagonals of algebraic spaces are representable monomorphisms, hence are
separated and in particular quasi-separated, covering the second part
of Gross's convention. Absolute quasi-compactness is supplied directly
by `IsQuasiCompact Y`. These are the semantic reasons for this derived
formulation; this statement module proves no relative-to-absolute
comparison.

Gross's conclusion initially gives an absolute representing AF scheme.
Composing its isomorphism to the target with the target's given
structure morphism supplies its structure map to `S` and the displayed
relative Yoneda isomorphism. This transport is also a future proof
obligation.

No source-specific errata note was present in the checked workspace,
project and supplied Library `notes/errata` locations. Focused searches
for an exact-title erratum or corrigendum found none. This records the
search scope, rather than an exhaustive absence claim.

## Proof boundary

The proof on printed p. 512 uses Corollary 3.8, which shrinks around the
inverse image of a finite set and applies Proposition 3.5 to a
quasi-affine source. The proof of Proposition 3.5 on pp. 511–512 uses
approximation, a normal case, normalization and conductor induction,
Ferrand's AF pushout theorem, and finite-surjective descent of
affineness. None of these steps is supplied by this statement.

The separately published `FiniteSurjectiveAffineDescentStatement` has
an affine source and an affine conclusion; it does not directly handle
an AF source. The separate
`FiniteAffineNeighborhoodsPushoutStatement` concerns AF of a supplied
scheme pushout. The present proposition does not construct that pushout
or a conductor square. It supplies no actual-family comparison, Picard
space, abelian-scheme representer or proof of the parent finite-type
existence theorem. Its exact proof requires a separate successor after
independent statement acceptance and Library publication.
