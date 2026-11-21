# A proper flat DVR model of the generic abelian variety

`ProperDvrModel p` gives a proper flat scheme over the DVR and a
Cartesian square identifying its generic fibre with the supplied
scheme `p : X ⟶ Spec K`. This implements the projective closure
used to start the local construction in Bosch, Lütkebohmert and
Raynaud, *Néron Models* (1990), §1.3, printed p. 16.

`ProperDvrModel.ofEmbedding` takes the schematic image of an integral
generic scheme in projective space over the DVR. Flat base change for
the kernel ideal identifies the restriction of this image to the
generic point with the supplied projective embedding. The image is
closed in proper projective space and is integral. Its structure map
is dominant because its generic fibre is nonempty. On nonempty
affine opens, dominance makes the coordinate ring an extension
domain of the DVR. Such a ring is torsion-free as a module over the
DVR, hence flat.

`Langlands.AbelianScheme.properDvrModel` uses the Library's ample
line bundle existence theorem and the theorem that ampleness on a
proper scheme over a field gives a closed projective embedding. It
then applies the schematic image construction with the actual
abelian variety as the generic fibre.
