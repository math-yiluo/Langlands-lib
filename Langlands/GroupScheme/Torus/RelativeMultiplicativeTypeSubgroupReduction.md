# Closed subgroups of multiplicative-type groups: a Hopf-algebra reduction

This module introduces the derived proposition
`Langlands.GroupScheme.FlatGroupLikeHopfMultiplicativeTypeStatement` and proves
that it implies the unchanged published
`Langlands.GroupScheme.RelativeMultiplicativeTypeClosedSubgroupStatement`.
The Hopf proposition is **not proved here**, and the implication does not
constitute an unconditional proof of the closed-subgroup statement.

## The algebraic proposition

For every commutative ring `R` and every commutative Hopf `R`-algebra `A`, assume
that `A` is flat as an `R`-module, finitely presented as an `R`-algebra, and
spanned as an `R`-module by its group-like elements. The proposition concludes
that the actual group scheme `(hopfSpec R).obj (op A)` is of multiplicative type
in the relative Library sense: it has an fppf cover of `Spec R` on which it is
isomorphic to a diagonalizable group with finitely generated abelian character
group. The Lean declaration is a `Prop`-valued definition, with one universe
parameter `u`; the rings, algebras, schemes and character groups have the
corresponding universe size. There are no domain, reducedness, local-ring,
finite-module, or smoothness hypotheses.

Finite presentation in this proposition is `Algebra.FinitePresentation R A`.
It is not the stronger assertion that `A` is finite as an `R`-module. The
spanning condition involves actual group-like elements of the given Hopf
algebra, not an abstract character group supplied as additional data.

## Provenance and source comparison

The proposition is an internal algebraic prerequisite motivated by Brian
Conrad, *Reductive group schemes* (2014), Corollary B.3.3, printed/PDF p.290,
using Definition B.1.1, p.280. Registered source:
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
It is not a verbatim formulation of a separate assertion in that source.

The source says that flat, locally finitely presented closed subgroups of
groups of multiplicative type are of multiplicative type. The algebraic
criterion isolates the coordinate-algebra step of an alternative route to
that result. Its mathematical motivation is as follows. A finite set of
algebra generators of `A` can be expressed using finitely many group-like
elements when the spanning hypothesis holds. Group-like elements of a Hopf
algebra are units. These elements therefore give a surjective Hopf map from
the group algebra on a finitely generated free abelian group to `A`. On
spectra, this presents the given group as a flat, locally finitely presented
closed subgroup of a split torus, to which Corollary B.3.3 applies. This
motivation is not implemented here as a converse or as a proof of the
criterion. The formal result in this module is the implication in the other
direction described below.

Conrad's own proof passes to a complete local base and uses Theorem B.3.2.
The module neither proves that deformation theorem nor assumes it as an
axiom. The new proposition remains an explicit premise of every theorem
using it.

## Implemented reduction

`RelativeMultiplicativeType.IsMultiplicativeType.of_fppfCover` composes a given
fppf cover with a splitting cover on each of its members. The cover `bind`
construction gives a cover of the original base. `baseChangeCompIso` identifies
the two successive base changes with the composite base change, and
`IsDiagonalizable.of_iso` transports the diagonalizable models. The open-cover
version changes the open cover to an fppf cover and applies this result.

`AffineCoordinates.finitePresentation_hopfAlgebra` uses the actual affine
coordinate comparison `AffineCoordinates.hopfSpecIso`. The structure map of
its source is the spectrum map of the coordinate algebra's `algebraMap`.
Local finite presentation is preserved when the original structure map is
precomposed with this isomorphism. `LocallyOfFinitePresentation.SpecMap_iff`
and `RingHom.finitePresentation_algebraMap` then give algebra finite
presentation of the actual coordinate Hopf algebra.

The remaining theorems perform these steps:

1. For a closed homomorphism `H → Diagonalizable.groupScheme R Λ`, closedness
   and affineness of the target make `H` affine. The published
   `Diagonalizable.flat_hopfAlgebra`, the new finite-presentation bridge, and
   `Diagonalizable.span_groupLike_of_closedSubgroup` verify all the hypotheses
   of the Hopf criterion for `AffineCoordinates.hopfAlgebra H`.
   `AffineCoordinates.hopfSpecIso H` transports its conclusion back to `H`.
2. A diagonalizable ambient group over `Spec R` is compared with that
   ring-level model using its given isomorphism and
   `Diagonalizable.baseChangeIso`. Composing the closed inclusion with this
   isomorphism preserves closedness.
3. For a diagonalizable ambient group over an arbitrary scheme, pull back
   along the affine open cover. Closedness, flatness and local finite
   presentation survive base change. The result over `Spec R` applies to each
   member, and open-cover locality gives the conclusion over the original
   base.
4. For an ambient group of multiplicative type, use its defining fppf
   splitting cover. Apply step 3 to every pulled-back subgroup and then
   fppf-cover locality.

The final theorem is
`Langlands.GroupScheme.relativeMultiplicativeTypeClosedSubgroup_of_flatGroupLikeHopf`.
Its only premise is
`Langlands.GroupScheme.FlatGroupLikeHopfMultiplicativeTypeStatement.{u}`;
its conclusion is exactly the published
`Langlands.GroupScheme.RelativeMultiplicativeTypeClosedSubgroupStatement.{u}`.
The statement module and its import closure are unchanged.

The shared fppf-locality and commutativity declarations are provided by
`RelativeMultiplicativeTypeLocality`; this module imports and reuses them.
