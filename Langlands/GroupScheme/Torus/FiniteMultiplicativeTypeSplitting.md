# Finite separable splitting of finite multiplicative-type field groups

Author: Worker 626.

This internal construction proves that a finite group scheme of absolute
multiplicative type over an arbitrary field admits a finite separable
splitting field. Here absolute multiplicative type means the published
`IsMultiplicativeType` predicate, given by a finitely generated abelian
character group and an actual diagonalizable presentation after some field
extension. The conclusion uses the separate relative predicate
`RelativeMultiplicativeType.IsDiagonalizable`: an actual isomorphism with
the split model obtained from the integral diagonalizable group.

All fields, character groups and group schemes lie in one arbitrary
universe `u`. Finiteness is the geometric condition `IsFinite H.X.hom`.
Smoothness, perfectness and a torsion-free character group are not assumed.
In particular, finite nonsmooth diagonalizable factors are included.

## Algebraic extension and separably closed fields

The existing `MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic k L H hH` proves that
absolute multiplicative type persists under an algebraic extension `L/k`.
Unpack a splitting of `H` over a field `K`. Its algebraic closure `E`
receives a `k`-algebra embedding of `L`, since `L/k` is algebraic. The
field-tower base-change isomorphisms compare `H_E` obtained through `L`
and through `K`. Base change of the original presentation, followed by
the diagonalizable base-change comparison, gives a presentation over `E`.
The theorem requires algebraicity of `L/k`; it makes no more general
extension assertion.

`IsMultiplicativeType.isDiagonalizable_of_isSepClosed hH` assumes in
addition that the ground field is separably closed and `H` is finite.
Multiplicative type supplies affineness; flatness over the field is
automatic. Write `A` for the actual affine Hopf coordinates of `H`.
The scalar-extension coordinate comparison converts the given splitting
into a Hopf-spectrum presentation over its splitting field. The
diagonalizable group algebra is spanned by its group-like elements, and
`SplittingAssembly.span_of_hopfSpecIso` transports this spanning to the
actual scalar extension of `A`.

The published pure-coalgebra theorem
`CoalgebraDescent.separablyClosedGroupLikeSpanning` descends this
spanning to `A` over the separably closed ground field. The finite flat
local reconstruction theorem
`Diagonalizable.isDiagonalizable_of_groupLike_span` then gives the
actual relative diagonalizable presentation of `H`.

## Finite separable splitting

`IsMultiplicativeType.exists_finiteSeparable_splitting hH` proves the
existence of `K : Type u`, field and `k`-algebra structures on `K`,
`FiniteDimensional k K`, `Algebra.IsSeparable k K`, and relative
diagonalizability of the actual base change `H_K`.

Apply the two preceding results to the separable closure `L` of `k`.
Unpack its relative diagonalizable presentation with finitely generated
abelian character group `Λ`. The diagonalizable base-change comparisons
identify the target with the base change of the ring-based model
`D_k(Λ)`. This model is locally of finite presentation over `k`.
The finite group `H` is quasi-compact and quasi-separated over `k`.

The public helper `exists_finiteIntermediateField_iso`, added to the
existing `FiniteSeparableSplitting` module in this same contribution,
therefore descends the actual isomorphism `H_L ≅ D_k(Λ)_L` to a finite
intermediate field `E` of `L/k`. Separability is inherited from the
separable closure. At `E`, the same base-change comparisons convert
the descended isomorphism back into a relative diagonalizable
presentation. This proves the existential result without requiring a
smooth splitting model.

## Chosen data

`FiniteMultiplicativeTypeSplittingData k H` stores an actual carrier
field, its `k`-algebra structure, finite-dimensionality, separability,
and a relative diagonalizable presentation of the actual base change
of `H`. Its field, algebra, finite-dimensional and separability
projections are instances.

`IsMultiplicativeType.finiteSeparableSplitting hH` chooses this data
from the preceding existential theorem through `Classical.choice` on
the nonempty data type. No uniqueness, canonicity, minimality or
Galois property is claimed.

## Provenance and scope

This is an internal derivation from the published actual-group
coordinate comparisons, pure-coalgebra descent over separably closed
fields, finite flat local reconstruction, and finite-stage descent
of group-scheme isomorphisms. The extension in
`FiniteSeparableSplitting` merely exposes its existing general
finite-stage proof, with the same hypotheses and unchanged proof.
No additional literature claim is transcribed.

This unit supplies a field splitting construction. Lifting this
extension to a faithfully flat algebra over an Artinian local base,
centrality descent, and the full reductive fibrewise central-isogeny
criterion remain further steps.
