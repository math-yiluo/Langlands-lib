# Finite flat local lifting of diagonalizability through nilpotent ideals

This is an internal derivation from the Library's affine Hopf coordinates,
scalar-extension comparison, finite flat local group-like reconstruction,
and nilpotent coalgebra lifting. No external theorem is asserted as a
new source translation.

All declarations are in `Langlands.GroupScheme.Diagonalizable` and use
one arbitrary universe `u`. Let `R : CommRingCat.{u}`. The helper
`span_groupLike_of_diagonalizable_hopfSpec` starts with an actual
commutative Hopf algebra `A` over `R` whose Hopf spectrum is relatively
diagonalizable. It proves that the elements satisfying the actual
`IsGroupLikeElem R` predicate span `A` as an `R`-module. The proof chooses
a diagonalizable presentation, compares the relative and ring-based
diagonalizable groups, and uses the full faithfulness of the Hopf spectrum
functor to obtain a coalgebra equivalence from the group algebra to `A`.
Group-algebra generators are group-like and span; their images retain
these properties. No localness or finiteness hypothesis is used by this
helper.

For the remaining declarations, assume `R` is local and `H` is a group
scheme over `Spec R` with affine total scheme and finite flat structure
morphism. Write `A = AffineCoordinates.hopfAlgebra H` for its actual Hopf
coordinates.

`finiteFlatLocalIsoOfGroupLikeSpan` takes the hypothesis that all group-like
elements span `A` and constructs an actual group-scheme isomorphism

\[
H \simeq D_R\bigl(\operatorname{Additive}(\operatorname{GroupLike}_R(A))\bigr).
\]

Here `D_R` denotes the ring-based `groupScheme R` construction. The
existing finiteness and flatness comparison theorems give finite flat
coordinates. `finiteFlatLocalBialgEquiv` reconstructs them as the monoid
algebra on all group-like elements. Because `A` is a commutative Hopf
algebra, its group-like elements form a commutative group. Conversion to
the additive group algebra and the affine Hopf spectrum isomorphisms give
the displayed isomorphism. No chosen character indexing is supplied as
an input.

`isDiagonalizable_of_groupLike_span` proves relative diagonalizability
from the same spanning hypothesis. The existing finite-flat local
coalgebra theorem proves that the group of all group-like elements is
finite. Its additive form is therefore finitely generated, as required
by `RelativeMultiplicativeType.IsDiagonalizable`. Composing the preceding
isomorphism with the relative base-change comparison gives the required
presentation over `Spec R`.

`span_groupLike_of_diagonalizable_reduction` takes an ideal `I` of `R`,
a proof that `I` is nilpotent, and relative diagonalizability of the actual
base change of `H` to `Spec (R/I)`. It proves that all group-like elements
of the original coordinates `A` span over `R`. A nilpotent ideal in the
nontrivial local ring is proper, so `R/I` is again a nontrivial local ring.
`HopfCoordinates.baseChangeSpecIso`, followed by base change of the actual
coordinate isomorphism for `H`, identifies the Hopf spectrum of
`(R/I) \otimes_R A` with this reduced group scheme. The first helper
therefore gives group-like spanning in the actual scalar-extended
coalgebra. Finite flatness persists under scalar extension, so the
finite-flat local basis theorem selects a finite group-like basis there.
`CoalgebraBaseChangeDual.span_groupLike_eq_top_of_reduced_basis` lifts
spanning to the original coalgebra through the nilpotent ideal. It uses
the previously constructed convolution-dual idempotent lifting, without
requiring the chosen lifted basis to have the same indexing as this
reduced basis.

Finally, `isDiagonalizable_of_nilpotent_reduction` composes this spanning
result with `isDiagonalizable_of_groupLike_span`: every finite flat affine
group over a local ring with diagonalizable actual nilpotent reduction
is itself relatively diagonalizable. These results do not require
smoothness of `H` or of its character group. They assume a split
(diagonalizable) reduction; constructing a splitting cover for a nonsplit
multiplicative-type residue group and the full reductive fibrewise
central-isogeny criterion remain further obligations.
