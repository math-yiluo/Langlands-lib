# Bundled witnesses for the complete Steinberg big-cell conclusion

`SteinbergBigCellData G` packages the actual witnesses and the entire conjunction
in the existential conclusion of `SteinbergBigCellStatement`, for an affine group
scheme `G` over a field `k : Type u`. It contains a lattice in the same universe,
its additive group structure, its diagonalizable group map to `G`, an affine
group scheme `H` and map to `G`, the conjugating rational point, the weight
coordinate of `H`, and the chosen coordinate of `G`.

The stored laws are precisely left covariance, inverse right covariance with
the same weight, value one at the identity, the nonzerodivisor property,
factorization on every relative test where the coordinate is a global unit,
a diagonalizable lift for every common test point of the two subgroup maps,
and cofinal finite bases of the entire covariant spaces with irreducible actual
Chevalley regular representations. Both geometric laws use the original test
scheme; there is no restriction to affine or reduced tests and no passage to
a cover. The second subgroup map is the supplied map followed by conjugation
by the same rational point throughout.

`SteinbergBigCellData.exists_data` simply unpacks the bundle into the exact
existential conclusion. It is proved by destructing the record and returning
all its fields, so it adds no assumption or structural-existence assertion.
This is an internal data interface derived directly from the existing target;
it does not establish the existence of a bundle for arbitrary groups. Neither
algebraic closure, positive characteristic nor simply connectedness is needed
to define the interface. Those hypotheses remain in the general existence
target and must be used in its proof.
