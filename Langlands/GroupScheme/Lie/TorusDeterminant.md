# Weight bases and determinants of actual split-torus Lie actions

This internal development uses natural finite coordinates and the actual Lie weight decomposition, without any local finite-type assumption. Finite coordinates make the base Lie kernel finite-dimensional. Independence of its split-torus character weight spaces then makes their support finite, and hence makes the set of nonzero roots finite.

The collected basis consists of a finite basis in each nonzero weight space; its indices record the actual character and a basis index in that weight space. The scalar-extension equivalence from natural finite coordinates extends this basis to every test algebra. The defining all-test-algebra weight equation proves that the actual differential is diagonal in this extended basis.

Taking the determinant of this diagonal matrix gives the product of the character values over the collected basis index. The equality holds in the unit group of every test algebra and uses the determinant of the actual differential, independent of the original coordinate basis. The result includes zero-dimensional Lie kernels and empty basis index types.

This is an internal linear-algebra construction derived from the published finite-coordinate scalar-extension and split-torus weight-decomposition interfaces. It supplies a basis and pointwise determinant calculation; converting the product into the algebraic root-character sum is a separate step.
