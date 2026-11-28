# Density of twisted Galois values

`Langlands.GroupScheme.GaloisTwistedPointDensityStatement` concerns a
connected reductive group `G` over an infinite field `K`, a finite Galois
extension `M/K` with `M` algebraically closed, and a nonidentity
automorphism `σ`. For any point `y` of `G` over `M`, the values
`f⁻¹ y σ(f)` as `f` varies over the `M`-points are Zariski dense in
the scalar extension of `G` to `M`.

`galoisTwistedPointDensity_of_isGalois` proves the density for every
finite Galois `M/K`. Normality splits the tensor product over `M`,
and the finite separable Weil restriction theorem gives connected
reductivity over `K`.

Take the affine Weil restriction of that scalar extension. Over `M`
it is the product indexed by the embeddings of `M` over `K`.
Unirationality and the infinitude of `K` give density of the
Weil restriction's ground-field points. Extending these sections
to `M` preserves their density.

On the geometric Weil restriction, use the inverse of the identity
coordinate, multiplication by the constant point `y`, and the
coordinate for `σ`. This morphism has a section obtained by varying
only the `σ` coordinate. Applied to an extended ground-field point,
the coordinate for an embedding is the image of the point under that
embedding, by the compatibility of the Weil product decomposition
with pullback evaluation. The image of the dense set of extended
ground-field points therefore consists of twisted values.

The density theorem proves `GaloisCocycleStronglyRegularValueStatement` by
meeting the nonempty strongly regular open. The point chosen in the image
of a twisted value lies in that open, so the entire image of its spectrum
lies there. In characteristic zero the base field is infinite. The
companion theorem `quadraticToralRepresentatives` applies the quadratic
reduction to obtain a cocycle of a maximal torus over the base.

The same coefficient projections also work when the coefficient field is
finite Galois and the polynomials split in that field. The preimage of a
nonempty open under the twisted-value morphism is nonempty because the two
coordinates vary independently. Its image under the scalar-extension
projection is a nonempty open in the Weil restriction. At a rational point
the fibre of that projection consists of a single point, so membership in
this open controls the twisted value of the corresponding cochain. The
cochain equivalence is the tensor-unit point comparison for Weil restriction
followed by the ordinary point comparison for the base-changed group.
For topological fields with the module topology on the extension, both
comparisons are homeomorphisms for the evaluation topologies on affine points.
