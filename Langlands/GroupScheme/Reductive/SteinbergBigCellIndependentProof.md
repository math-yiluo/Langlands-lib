# Steinberg big-cell data from the rank-one central cover

`Langlands.GroupScheme.steinbergBigCellIndependent` proves
`Langlands.GroupScheme.SteinbergBigCellStatement.{u}` for every universe `u`
under its published hypotheses. The proof composes Library constructions for
the actual group scheme, torus, root groups, and covariant coordinate spaces.

## Structural inputs

The theorem `rankOneCentralCover` supplies the compatible central isogeny
from `SL₂ × C` for a prescribed split maximal torus with nonempty,
pairwise dependent actual roots over an algebraically closed field. Its
proof obtains a bound on the dimension of an ordinary Borel quotient using
torus limits, the fixed points of the torus, and Hartogs extension. General
curve lemmas then yield the local Lie lines used in constructing the root
cell and the central isogeny.

`rankOneRootReducedness_of_centralCover` transports the explicit root
opposition in `SL₂ × C` through the compatible cover and reflects it by
base change. `rootDatumExistence_of_rankOneReducedness` constructs the
root datum on the actual character and cocharacter lattices. In parallel,
`splitRankOneRootCell_of_centralCover` gives split rank-one root cells,
and `splitRootLieLine_of_centralCover` gives root Lie lines through
cocharacter centralizers and weight-space comparison over the algebraic
closure.

`splitSimplyConnectedCorootSpan_of_corootSpanLineInputs` uses these three
results to obtain integral coroot generation for simply connected groups.
`algClosedOppositeFactorPairs_of_structuralStatements` obtains the
opposite factor pairs from the same three results. This fills the five
fields of `IndependentSteinbergInputs`.

## The seven laws

`IndependentSteinbergInputs.to_statement` chooses an actual split maximal
torus and constructs a pinning with full simple-root coordinates. Its
opposite-pair argument supplies the Bruhat covering for the polarized-rho
dynamic subgroup. The geometric construction uses a highest-weight
representation of weight rho. It gives the diagonalizable torus map, the
dynamic subgroup inclusion, the opposition point, the negative-rho
character coordinate, and the normalized extremal matrix coefficient.
These witnesses satisfy the two covariance laws, the normalization and
nonzerodivisor laws, and the factorization and intersection laws on
arbitrary relative test schemes.

For exponents `p^r - 1`, the supplied-root Frobenius argument compares
the finite covariant space with a highest-weight module and transfers
rational irreducibility to that space. The cofinality of these exponents
gives the seventh law for the same subgroup and character. The resulting
data are projected to the existential witnesses of the original proposition.

## Provenance

This is an internal assembly of the Library's structural reductions and
seven-law construction. The ordinary Borel geometry used in the cover and
the highest-weight construction enters through ordinary Borel quotient
properness. The covering used for the seven laws comes from the supplied
opposite pairs. The construction of the polarized-rho subgroup uses its
dynamic group-scheme representative.
