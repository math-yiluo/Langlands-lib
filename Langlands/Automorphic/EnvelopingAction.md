# Genuine differential action on finite-smooth adelic functions

This internal construction descends the genuine archimedean enveloping algebra
action to actual finite-smooth rational-invariant adelic functions over any
number field `K : Type u` and every natural rank, including zero. The coefficient
field is complex, and archimedean smoothness is real smoothness. All operators
come from the actual matrix derivative in the imported construction.

`finiteSmoothSlice` extracts each smooth infinite slice from the function.
Equality of all slices implies equality of the original functions by the adelic
product decomposition. `slicesAtLevel` packages those slices at any specified
open finite subgroup fixing the function. Its covariance identity is
`F(gamma_f * b)(gamma_infinity * a) = F(b)(a)` for rational gamma.

`differentiateSliceFamily` applies the same genuine enveloping operator to every
slice. It preserves the specified finite level pointwise. To prove rational
covariance, express the original identity as equality of smooth functions under
the pullback `L(c)s(a) = s(c * a)`, and use the published identity
`D(u)(L(c)s) = L(c)(D(u)s)`. This step uses the proved compatibility law; it is
not an additional input hypothesis.

`finiteSmoothDifferential` chooses an open finite stabilizer from the function's
membership proof and reconstructs the differentiated family. The reconstruction
API proves joint continuity, rational-left-invariance and finite smoothness.
`finiteSmoothSlice_differential` identifies every slice of the output with the
original genuine archimedean differential. This identity proves independence
of the chosen stabilizer and identifies the result with reconstruction at any
other specified stabilizing open subgroup.

`finiteSmoothEnvelopingAction` bundles these operators as a complex algebra
homomorphism into endomorphisms of the actual finite-smooth function space.
Linearity, the unit, multiplication, zero, addition and scalar compatibility
are checked on every smooth slice, using the faithful slice map and the
published archimedean algebra homomorphism. Thus multiplication acts by operator
composition in the same order as in the archimedean action.

The evaluation formula at `pair(a,b)` is exactly `D(u)(slice_b f)(a)`.
`finiteSmoothEnvelopingAction_preserves_level` retains every specified open
finite subgroup fixing the original function. Consequently an existing compact
finite level is retained with the same subgroup and compactness proof; no
existence theorem for compact open subgroups is asserted. On a real Lie
generator, the displayed evaluation is the actual real coordinate derivative
of the original slice at the coordinate matrix of `a`, in direction `a * X`.
`finiteSmoothCenterAction` restricts the algebra homomorphism to the actual
complex enveloping center and retains the same slice formula.

The provenance is internal and derived from `Automorphic.FiniteLevelSlices` and
`Global.ArchimedeanEnvelopingLawsProof`, together with the existing smooth
ambient spaces. This unit constructs an action on the common-open-stabilizer
space. It does not assert differential preservation of every slice-wise locally
constant smooth function without such a stabilizer, or preservation of growth,
compact-type finiteness, center finiteness, or cuspidality. These further
conditions and their representation-theoretic compatibility remain separate.
