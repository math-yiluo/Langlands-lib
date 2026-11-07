# AF representability from a finite surjection with quasi-affine source

Author: Worker 133.

This module states a derived specialization of Philipp Gross,
*Tensor generators on schemes and stacks*, Proposition 3.5. It is a
substantial prerequisite for the proof of finite-surjective AF descent.
The module proves no representability or descent theorem.

## Exact proposition

`Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveQuasiAffineSourceAFStatement.{u}`
is a Prop-valued definition. For every commutative ring `R : Type u`, with
`S = Spec (CommRingCat.of R)`, it quantifies over an actual scheme
`U : Over S`, an actual algebraic space `Y : AlgebraicSpace S`, and an
actual morphism `f : (schemeToSpace S).obj U ⟶ Y`. The hypotheses are:

- `IsQuasiCompact Y`, the existing absolute compact-atlas predicate;
- `IsQuasiSeparated Y`, the existing predicate on the relative diagonal;
- `U.left.IsQuasiAffine`, Mathlib's quasi-affine scheme predicate;
- `IsFinite (hom f)` and `IsSurjective (hom f)`, the existing represented
  scheme-test finiteness and geometric-surjectivity predicates.

Mathlib's quasi-affine predicate includes quasi-compactness and an immersion
into the spectrum of global sections; its accompanying results show that
this canonical map is an open immersion. Thus the source here is an actual
quasi-compact quasi-affine scheme, and in particular is separated.

The conclusion is an actual scheme `P : Over S` satisfying
`PointTopology.HasFiniteAffineNeighborhoods P.left`, together with
`Nonempty ((schemeYoneda S).obj P ≅ Y.presheaf)`. The finite-set condition
includes all finite subsets of the underlying points, including nonclosed
points. The natural isomorphism is on every scheme test over the original
base, with the existing presheaf universe convention.

There is no noetherian, reducedness, normality, finite-type, finite-presentation,
flatness, projectivity or target-representer premise. The target
quasi-compactness and relative quasi-separatedness hypotheses are retained.
The conclusion asserts AF for the representing scheme and does not assert
quasi-affineness.

## Source and derived formulation

The registered source is `gross-tensor-generators-schemes-stacks-2017`,
Philipp Gross, *Tensor generators on schemes and stacks*, Algebraic
Geometry **4** (2017), no. 4, 501–522,
[DOI 10.14231/AG-2017-026](https://doi.org/10.14231/AG-2017-026).
The retained publisher PDF has SHA-256
`fa20fe6fff07a861f93d6640e553f2cc8f48b694487c49e257a089ce52b45e8b`.

Proposition 3.5, printed p. 510 / PDF p. 10, says that an integral
surjective image of a quasi-compact quasi-separated scheme admitting an
ample invertible sheaf is represented by a quasi-compact separated AF
scheme. Apply its first assertion to Gross's `Z = U` and `X = Y`.
A finite morphism is integral; the trivial invertible sheaf on a
quasi-affine scheme is ample. The quasi-affine source is quasi-compact and
separated under Mathlib's convention. The conclusion above retains only
the AF part of Gross's conclusion.

Remark 3.6, printed p. 511 / PDF p. 11, explicitly warns that a quasi-affine
source need not have a quasi-affine target. Corollary 3.8, printed p. 512 /
PDF p. 12, applies Proposition 3.5 precisely to a quasi-compact quasi-affine
source obtained by shrinking inside an affine source open. That use is the
reason for isolating this statement. Definition 3.1, printed p. 510, supplies
the finite-set meaning of AF.

The relative formulation follows the existing published
`FiniteSurjectiveFiniteAffineNeighborhoodsDescentStatement`, formulated by
Workers 139 and 1038. Gross's conventions on printed p. 503 / PDF p. 3
use an absolute quasi-compact and quasi-separated diagonal. Over the affine
base `S`, the absolute diagonal factors through the relative diagonal
followed by a base change of the closed diagonal of `S` over `Spec ℤ`.
Consequently the retained relative quasi-separatedness supplies absolute
quasi-compactness of the diagonal; representable diagonal monomorphisms are
separated and hence quasi-separated. An absolute representing scheme
acquires its structure map to `S` by composing with the target's structure
map. These comparisons explain the derived formulation and remain proof
obligations if the eventual proof uses this absolute route.

The original source pages 510–512 were read in full. No source-specific
errata note was found in the checked workspace, project or supplied Library
notes; this records the search scope.

## Proof boundary

The proof of Proposition 3.5 on printed pp. 511–512 uses approximation,
the normal noetherian case, normalization, conductor induction, an AF
scheme pushout and finite-surjective descent of affineness. This statement
supplies none of those constructions or their proofs. In particular it does
not follow merely by applying affine-source descent to an open subscheme
of an affine source.

A separate exact proof successor is required after independent statement
acceptance and Library publication. The full AF-source descent task still
needs the shrinking, point and gluing arguments reducing its source to
this special case. No adjacent ring, scheme-pushout, AF-preservation,
Picard, actual-family comparison or representability task is discharged here.
