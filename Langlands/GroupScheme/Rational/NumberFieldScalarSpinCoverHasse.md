# The Hasse kernel of simply connected scalar spin covers

`NumberFieldScalarSpinCoverHasseStatement` concerns a central isogeny from a simply connected group to the actual semisimple norm-one isometry group of a regular scalar quadratic presentation. Suppose that the dimension is at least four and the kernel has two points over an algebraically closed coefficient field. Then over a number field, every locally trivial cocycle in the simply connected source is trivial on its original finite Galois cover.

`CliffordSpin.exists_iso_of_simplyConnected_scalarCover` compares the given cover with the affine Clifford lift group. The latter is semisimple by connectedness transfer and its full scalar kernel is μ₂, which has two points in characteristic zero. The common semisimple central refinement and the geometric kernel cardinality criterion give an isomorphism of the actual covers over the ground field. `numberFieldScalarSpinCoverHasse` transports the cocycle and its local trivializations along the isomorphism, applies the Clifford spinor-norm Hasse result, and returns the global coboundary using the inverse isomorphism.

The scalar spin Hasse principle and the role of the central double cover are in Kneser, *Lectures on Galois Cohomology of Classical Groups*, §5.11, p. 99. This transfer uses the actual group scheme and geometric kernel of the supplied cover.
