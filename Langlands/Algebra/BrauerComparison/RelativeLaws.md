# Matrix stability and tensor addition for relative Brauer classes

Relabeling rows and columns gives a ring equivalence of matrix algebras and
therefore an equivalence of their invertible matrices. It commutes with
coefficient automorphisms and sends each scalar matrix to the scalar matrix
of the same unit. Thus relabeling preserves the factor set. Comparing
matrix dimensions supplies the relabeling between the index types of any
two charts on the same split algebra. A ground-field algebra equivalence
commutes with the coefficient actions after tensoring, so transport of a
chart through such an equivalence also preserves the class.

For the actual tensor chart, the invertible Kronecker products lift the
tensor action. Their factor set is the product of the two factor sets, so
its cohomology class is their sum. The published splitting criterion
identifies vanishing of a finite Galois relative class with the existence
of a splitting over the base. Applying tensor addition to the algebra of
matrices over the ground field proves invariance under stabilization. The
result applies directly to Mathlib's `IsBrauerEquivalent` relation when
both algebras are supplied with charts over a common extension.

These are consequences of Serre's descent factor construction in
*Local Fields* (1979), Chapter X, §5, printed pp. 158–159, in the Library's
arbitrary-index chart and actual tensor product interfaces.
