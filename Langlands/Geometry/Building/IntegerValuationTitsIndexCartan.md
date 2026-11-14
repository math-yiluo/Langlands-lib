# Actual integer-valuation apartments and absolute affine Cartan extensions

`integerValuationTitsIndexCartanExtension` chooses a matrix on
`Option d.Vertex` using the ordinary affine roots of supplied actual
`IntegerValuationBuildingData B` for `G_L`. Here `d` is actual Tits-index
data for `G` over `k`, and `L/k` embeds compatibly in `SeparableClosure k`.
The explicit integer valuation of `L` has an order-one unit. The maximal
split torus of `B` must also be a maximal torus.

The remaining chamber inputs are a regular point, nonempty irreducible
ordinary affine roots, transitivity of the actual chamber Cartan matrix,
and transitivity of simple affine roots by root-preserving affine
pullbacks. The construction retains these as explicit hypotheses.

The specification proves the exact absolute Cartan block on `some`,
diagonal entries two, nonpositive off-diagonal entries, a symmetric zero
pattern, a strictly positive integral left-kernel vector, and vertex
transitivity by entry-preserving permutations.

The proof derives three inputs of `TitsIndexAffineCartanExtension` from
the supplied actual apartment. The published integer-valuation
affine-system theorem supplies the corrected affine-root-system axioms;
this is the only step using the order-one-unit premise. Actual
root-datum existence on the split maximal torus gives a reduced integral
root datum on its character and cocharacter lattices. The
`ReducedRelativeApartmentRoots` adapter excludes doubled relative roots,
proves the entire ordinary derivative set equals the actual relative
root-form range, and gives indivisible ordinary affine lifts of every
derivative. The two latter conclusions are also exported as
`IntegerValuationBuildingData.derivativeRoots_affineRoots_of_maximalTorus`
and `hasIndivisibleDerivativeLifts_of_maximalTorus`; they need no
order-one-unit premise and apply to any supplied integer-valuation
building data over a field, without a field tower. Applying the imported absolute Cartan construction
then proves existence, and classical choice defines the matrix with its
full specification.

This is internal infrastructure obtained by composition of the imported
constructions. It has no characteristic restriction. It supplies no
splitting, integer-valuation apartment existence, nonemptiness,
irreducibility or chamber-transitivity result under local anisotropy.
The local anisotropic affine-diagram target remains open until those
inputs are constructed from its unchanged hypotheses.
