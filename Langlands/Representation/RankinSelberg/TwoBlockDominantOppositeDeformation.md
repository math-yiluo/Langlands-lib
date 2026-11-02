# Entire inverse Whittaker deformation for opposite complex twists

This internal deduction extends the literal real family used by the Jacquet
convergence theorem to the complex parameter. Its blocks are the original
representations on their original dependent carriers, twisted respectively by
`|det|^(-u)` and `|det|^u`. Their normalized lower induction is the actual
canonical section representation. At a real parameter this is definitionally
the published opposite real twist family; at zero the blocks are unchanged.

`oppositeTwistComparison` constructs an actual equivalence from the ambient
twist `|det|^u` of the first-block family at `-2*u`. The determinant of each lower
parabolic element is the product of the determinants of its ordered Levi
blocks. Combining the first-block determinant powers gives `-u` on that block
and `u` on the second. The proof applies the smooth induction twist equivalence
and an identity equivalence of the full lower covariance actions on the
original dependent tensor carrier. It does not identify inductions by product
commutativity.

`exists_oppositeWhittakerFamily` applies the published
`twoBlockWhittakerDeformation` theorem, with the supplied inverse functional and
vector transported to the first-block family at zero. At each parameter it
transports the functional and vector through `oppositeTwistComparison` and
multiplies the coefficient by the ambient determinant power. The resulting
functions satisfy inverse Whittaker equivariance. The starting coefficient is
exactly the supplied model vector. Intersecting the original common right level
with the determinant-norm kernel gives one compact open level for the entire
family. The determinant power and linear reparametrization are entire, so every
point value is entire. `OppositeWhittakerFamilyData` records these actual
coefficient realizations, the common level and pointwise analyticity.

The only representation hypothesis is full Whittaker type of each input block;
reducibility is allowed. The supplied initial functional is nonzero, while its
model vector may be zero. There is no premise of ordinary Jacquet convergence
or analyticity of an integral. This is an internal adaptation of the published
first-block deformation and smooth twist equivalences. It proves neither
final dominant-rank factor theorem.
