# Split-place test functions with prescribed supports

`splitOrbitCutoff` proves `SplitOrbitCutoffStatement`. At a completely
split place, take a matrix `δ` in the cyclic product algebra, an
open neighbourhood of its tuple of coordinates, and an open
neighbourhood of their ordered product. For compatible split Haar
measures, the theorem constructs a split tensor and its concordant
convolution. Their closed supports lie in the respective
neighbourhoods. The tensor is one at `δ`, and the convolution is
nonnegative and positive at the ordered product.

The ordered product is continuous by `splitProductFiberChart`. The
proof picks a product of compact clopen sets inside the prescribed
tuple neighbourhood and the inverse image of the prescribed product
neighbourhood. Its coordinate indicators give the factors of the
tensor and of the convolution. In the product-fiber chart the
convolution is the product Haar measure of the fiber cut out by
these sets. The fiber over the ordered product of the original
tuple is compact and open and contains the free coordinates of
that tuple, so its measure is positive and finite. Fibers over
points outside the prescribed product neighbourhood are empty.
The Library's `splitMatching` theorem gives exact concordance.

This is the local test-function construction used to shrink support
at the split auxiliary place in Arthur–Clozel, Chapter 1, pp. 43
and 46, and Henniart–Lemaire, I.6.8, pp. 49–50 (PDF pp. 57–58).
The neighbourhoods are inputs so that they can come from rational
orbit separation and from bounds on an initial adelic support.
