# Renard II.3.10: convolution laws and concrete comparisons

This unit states nine closed targets, and their conjunction `Statements`, in
`Langlands.HarmonicAnalysis.Distribution.RenardConvolution`. It supplies no
proofs or new algebra instances. Every operation is the published one on the
original algebraic distribution, compact-support submodule, scalar test or
locally constant function carrier. All groups have their supplied Hausdorff,
locally compact, totally disconnected group topology, without countability or
unimodularity assumptions.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Locators: II.3.10 definitions, Proposition (i)–(v) and following algebra
paragraph, printed p.50 / PDF p.56; its Dirac Lemma, printed p.51 / PDF p.57.
The final Hecke compatibility specializes Proposition (iv) and supplies the
concrete bridge used in II.3.12 Remark 3 and (II.3.12.1), printed p.52 / PDF p.58.

- `AmbientTensorStatement` identifies the implemented support-descent
  convolution with extended evaluation of the ambient tensor on
  `(x,y) ↦ f(xy)`. Its compact-support witness is for that actual ambient tensor,
  and its value is the published `compactSupportPairing`. The existing
  `Distribution.TensorProductStatements` contains the general tensor-support
  and compactness targets; the extra obligation here is the convolution
  comparison, not a replacement tensor product.
- `RegularityStatement` asserts local constancy of all four scalar kernels,
  compact support when both inputs have compact support, and equality of the
  smooth and test kernel definitions on the identical test function. This
  supplies the regularity deliberately left open in `Distribution.Convolution`.
- `AssociativityStatement` is Proposition (ii), using the published
  `convolution` on `compactlySupported`.
- `MixedAssociativityStatement` is Proposition (iii). Four existential locally
  constant intermediate functions are fixed by equality of their underlying
  functions with the actual kernels. The three concluding identities express
  `(T*S)*f=T*(S*f)`, `T*(f*S)=(T*f)*S`, and
  `(f*T)*S=f*(T*S)`. These witnesses do not assume any identity being proved.
- `HaarDensityStatement` is Proposition (iv). The two compact distributions are
  constrained to be the actual test densities. The test witnesses equal the
  left and right convolution kernels everywhere. The conclusions compare
  actual distribution convolutions with those test densities. On the right,
  finiteness on compact sets and right invariance suffice, so every right Haar
  measure is covered without incorrectly requiring it to be a left Haar measure.
- `EvaluationStatement` is Proposition (v) for the full algebraic dual, with
  the inverted test evaluated through either kernel at the group identity.
- `BilinearUnitStatement` states complex bilinearity and the two unit
  identities for the original `compactDirac 1`. Together with associativity
  these are the laws for the source's unital associative complex algebra E′;
  no unproved algebra structure is installed.
- `DiracStatement` is the Lemma on p.51. Right multiplication by `δ_g` is
  `r(g⁻¹)`, preserving the source's inverse in the right point action, and
  the product of the two Diracs is `δ_(g*g')`.
- `HeckeCompatibilityStatement` specializes the density formula to two tests
  against the same left Haar measure and compares with
  `Langlands.Hecke.TestFunction.convolution μ`. It is the bridge to the
  existing function realization of the Hecke algebra, not a new Hecke carrier.

Proposition (i) is already proved for this very operation by
`Distribution.support_convolutionDistribution_subset`; the definition
`convolution` includes the resulting compactness proof. No duplicate unproved
support target is introduced. The Library's test-function convolution laws do
not by themselves prove the laws for arbitrary compact algebraic distributions;
this unit states those remaining obligations explicitly.
