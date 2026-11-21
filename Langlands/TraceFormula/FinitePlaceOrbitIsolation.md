# Split-place orbit isolation in the actual point groups

`finitePlaceOrbitIsolation` proves `FinitePlaceOrbitIsolationStatement`.
For a finite completion of a cyclic number-field extension with a
supplied cyclic splitting, the theorem constructs matching split tests
for a chosen rational norm-associated pair. The base matrix of this
pair is regular semisimple, so its characteristic polynomial over the
base number field is separable. The supplied open neighbourhoods
contain the localized split tuple and its ordered product, respectively.
The tests are evaluated on the actual local point groups of `GL_n` and
its Weil restriction. Their closed supports in split coordinates lie
in the supplied neighbourhoods. In each supplied finite list, a local
orbit with nonzero test value comes from the corresponding chosen
rational class.

The algebra splitting gives a multiplicative homeomorphism of
the local matrix groups and intertwines the local Galois action
with cyclic shift. It commutes with the cyclic norm and with
base scalar extension, so rational associations localize to
associations for the split shift. The comparison uses the base
completion topology and `IsSplitProductHaar`, which makes the upper
ambient Haar the product of the lower Haar in split coordinates.

The proof applies `splitRationalOrbitIsolation` to the rational matrix
images of the two lists. The ordinary and twisted local calculations
use the actual rational and local point comparisons. Conjugators
found in rational matrix coordinates are carried back to rational
point groups. The split tensor is one at the chosen upper point and
the convolution is nonnegative and positive at its ordered product.

This is an internal specialization of the support refinement at an
auxiliary split place in Arthur–Clozel, Chapter 1, pp. 43 and 46,
and Henniart–Lemaire, I.6.8, pp. 49–50 (PDF pp. 57–58).
