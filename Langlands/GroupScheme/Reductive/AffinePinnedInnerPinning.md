# Actual inner representatives and pinning equations

This internal bridge extracts the actual adjoint permutation equation from a
comparison preserving the supplied pinning on local coefficient tests. The
original model, its pullback, and every pinning vector are the existing concrete
objects; no abstract substitute for the differential is introduced.

`coefficientTestIso` identifies an actual affine test over the common scheme
with that same spectrum over the model's original coefficient base, using the
specified equality of base maps. `coefficientTestPointsEquiv` composes this
identification with the pullback adjunction, multiplicatively projecting points
to the original affine group. Its underlying scheme map is the pullback's first
projection. The accompanying lemmas establish compatibility with the normalized
torus inclusion, constant dual-number points, and the actual supplied pinning
vectors. `dualNumber_test_base` records the coefficient identity on the
dual-number refinement.

`torusPermutesSimpleVectorsAt_of_representsIso` assumes a self-comparison
preserving local pinning, a local coefficient ring with its actual affine test,
and a point of the normalized torus whose image represents that comparison on
every refinement. It evaluates the representing equation on the dual-number
refinement and each supplied simple vector. Pinning preservation gives a
bijection of the simple roots. Applying the multiplicative point projection,
and its constant-point and root-vector identities, yields exactly the original
model's `TorusPermutesSimpleVectorsAt` equation over the coefficient ring.

`mem_center_coefficientTest_of_representsIso` applies the existing
coefficient-test rigidity theorem, using the nontriviality of a local ring.
The conclusion is
membership in the original group's full centre functor on the coefficient test,
including commutation after every further relative refinement. Local rings may
have nilpotents; the argument uses dual-number points and retains those
coefficients.

These are derived internal results from the existing pullback adjunction,
pinning-point construction, representation predicate and coefficient-test
centrality. They do not yet prove comparison uniqueness or the host existence
statement.
