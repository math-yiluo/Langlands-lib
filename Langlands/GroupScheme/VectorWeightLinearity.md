# Positive scalar weights and linear vector-group maps

This internal adapter supports linear transitions between local quotient charts
for the finite vector-bundle filtrations of supplied relative radicals. It concerns the actual finite free polynomial vector groups over an
arbitrary commutative ring. Source and target have independent finite ranks,
including rank zero. It imposes no field, reducedness, characteristic, locality,
connectedness or noetherian hypothesis.

`HasScalarWeight f d` states that an additive natural transformation from
`VectorGroup.functor R n` to `VectorGroup.functor R m` commutes with scaling by
the `d`th power of every unit on every commutative coefficient algebra.
The degree must be positive in the linearity results.

`coordinateLineOperation` restricts the transformation to one input coordinate
line and takes one output coordinate. It is an instance of the existing
`NaturalLine.Operation`. The existing arbitrary-ring theorem
`NaturalLine.Operation.eq_mul_of_laurent` proves this operation is multiplication
by its value at one over the base. The needed Laurent equation is obtained by
scaling the input coordinate vector by the unit `T` in the Laurent polynomial
algebra and using naturality for the coefficient map from the base ring.
The polynomial-substitution proof of that existing theorem is reused.

`weightMatrix` collects those base-ring values into a rectangular coefficient
matrix. Additivity and the finite decomposition of a vector into its coordinate
lines prove `additiveApp_eq_weightMatrix` on every coefficient algebra.
`linearAppOfWeight` constructs the resulting linear map over each coefficient
algebra; its function is exactly the original additive map. If the natural
transformation is an isomorphism, `linearEquivAppOfWeight` uses its actual inverse
to produce a linear equivalence on each coefficient algebra. Scalar equivariance
of the inverse need not be supplied.

`groupSchemeMap_eq_matrixHom` identifies the actual represented group-scheme
map with the existing matrix homomorphism, using the Library's all-test
corepresented-point comparison. Thus the matrix formula holds on all scheme
tests, including non-affine and nonreduced tests.

For an actual group-scheme morphism `φ`, `pointTransformation φ` is its affine
point transformation from the existing `Corepresented.pointsTrans`.
`eq_matrixHom_of_hasScalarWeight` applies the preceding theorem and the existing
recovery identity `Corepresented.groupSchemeMap_pointsTrans` to identify `φ`
itself with that matrix homomorphism. `coordinates_of_hasScalarWeight` states
the resulting formula on arbitrary scheme tests. `linearMapOfWeight` gives the
actual linear map over each coefficient algebra; at the coefficient algebra
`R` itself this is the extracted `R`-linear map.

`pointTransformationIso` sends an actual group-scheme isomorphism to its
natural point isomorphism. Its inverse equations follow by postcomposing points
with the original inverse maps. `linearEquivOfWeight` consequently extracts
linear equivalences from actual isomorphisms. The input ranks are independent;
no rank equality or extra inverse-linearity premise is assumed.

The argument is derived internal content from the existing rank-one rigidity,
finite additive decomposition and actual vector-group matrix construction.
It supplies a linearity ingredient. It does not construct the quotient charts,
prove their scalar equivariance, or assemble the parent radical filtration.
