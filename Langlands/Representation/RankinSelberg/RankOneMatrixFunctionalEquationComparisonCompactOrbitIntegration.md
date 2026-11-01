# Compact parameter integration of the Fourier and block orbits

This internal derived prerequisite integrates the actual same-test identity of
WeylOrbitBlocks against one compact Schwartz kernel in a continuous family of
right translates. It proves convergence on both full parameter products before
exchanging their integrals. It does not assert the model-vector dual comparison
or the final gamma equation.

For a parameter space `X`, its given measure `μ` is s-finite and finite on compact
sets. A continuous map `U : X → GL_(m+2)` and a Schwartz kernel `κ` are fixed.
The normalized determinant norm of `U x` must be one whenever `κ x` is nonzero;
no condition is imposed at the other parameters.

The general lemma `integrable_compact_locallyConstant_family` proves joint
integrability of a uniformly locally constant, compactly supported family of
complex integrands whose every section is integrable for an s-finite section
measure. The published finite
Schwartz expansion expresses the entire family as a finite sum of products
of an integrable parameter Schwartz function and an integrable sampled section.
Thus the proof does not infer joint integrability from sectional convergence
alone.

For the actual Fourier orbit, the matrix Fourier transform of the same test is
Schwartz by the supplied self-duality. Uniform local constancy of its right
translates follows from MatrixTestTranslates. Evaluating each translated matrix
function on the fixed inverse-transpose, signed-Weyl, scalar-diagonal argument
preserves uniform local constancy. For the block orbit the same argument uses
the original test and the continuous map `x ↦ inverseTranspose (U x)`.
Multiplication by `κ` gives compact support for both families.

At parameters where `κ` vanishes, both sections vanish. At every other parameter,
the published fixed-translate WeylOrbitBlocks theorem gives both genuine
integrabilities and the integral equality. The finite-family lemma supplies
the two joint integrabilities. Fubini then puts the parameter outside each
orbit integral, and the fixed-parameter equality proves equality of the two
full product integrals.

The theorem retains every canonical p-adic field, every nontrivial bundled
additive character, the supplied self-dual scalar Haar measure `ν`, the actual
integral-normalized upper-unipotent Haar, and the product rectangular block
measure formed from that same `ν`. The size is `m+2`, including `m=0`.
The signed representatives, inverse character, inverse transpose and the
literal complementary block matrix are exactly those of WeylOrbitBlocks.
The kernel, parameter measure and translate map are identical on both sides.
No representation, rational continuation, analytic functional equation or
additional normalization is assumed or concluded.

The definitions `compactSignedWeylOrbitFourierAverage` and
`compactSignedBlockOrbitAverage` name the actual compact parameter integrals
of the two kernels. The `_averaged` consequence moves the compact parameter inside the unipotent
integral and then puts the scalar outside on both sides. On the block side
it also places the rectangular block integral between the scalar and unipotent
integrals. Repeated applications of Fubini to the proved full product
integrabilities justify each order, and prove integrability of both resulting
scalar or scalar/block averages. This allows subsequent model integration to
use exactly the same compact kernel and translate map.
