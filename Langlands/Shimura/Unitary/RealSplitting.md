# Harris charts on the actual real scalar extension

This module assembles the real-place charts of the given CM algebra into an
isomorphism on its rational real scalar extension. It transports the corrected
complex homomorphism through that isomorphism and proves that the existing
rational chart action is the actual diagonal real action.

## Hypotheses and provenance

The general construction uses a totally real number field `E`, a totally complex
number field `K`, a quadratic `E`-algebra structure on `K`, a ring `A` with
`E`-, `K`- and rational algebra structures, and `IsScalarTower ℚ E A`.
It takes a second-kind involution `σ`, a finite basis `b : Basis ι E A`, and
`C : HarrisSignatureCharts σ n Φ`. The fields, algebra and basis index may
have different universes. The chart input includes rank greater than one,
a distinguished real embedding, actual real algebra isomorphisms at each
embedding, their involution identities and their specified CM-center action.
The assembly does not assume a global real matrix isomorphism or a complex
homomorphism into the real scalar extension.

The construction is internal. Its mathematical inputs are the tensor assembly
`Langlands.Global.TotallyReal.algebraEquiv`, the existing chart definitions and
corrected matrix homomorphism in `HarrisLevels` and `Domain`, and the transport
of similitudes in `InvolutionBaseChangeTower`. The Harris signature convention
and its original-source provenance are those of the imported modules; this
module introduces no new source-dependent assertion. All new compatibility
identities are proved directly from the imported constructions.

The central-simple specialization additionally uses `IsScalarTower E K A` and
`D : CentralSimpleUnitaryData E K A n`. Its optional signature constructor takes
`HasHarrisSignature D.toSecondKindInvolution n` and `IsCMSection E K Φ`.
These are retained hypotheses about the given algebra and CM section; this
module does not assert existence of such an algebra or signature for arbitrary
number fields.

## Matrix algebra and involution

In the namespace `Langlands.Shimura.HarrisSignatureCharts`, `realMatrixEquiv`
is the composite

\[
\mathbb R\otimes_{\mathbb Q}A
\simeq_{\mathbb R}
\prod_{\tau:E\to\mathbb R}(\mathbb R\otimes_{E,\tau}A)
\simeq_{\mathbb R}
\prod_{\tau:E\to\mathbb R}M_n(\mathbb C).
\]

The second arrow applies `C.equiv τ` in each factor.
`realMatrixEquiv_tmul` proves that its component at `τ` sends `r ⊗ a` to
`C.equiv τ (r ⊗ a)`, with the target tensor taken over `E` through `τ`.
`realMatrixEquiv_one_tmul` identifies the image of `1 ⊗ a` with the existing
`C.evaluation a`.

`realMatrixEquiv_involution` intertwines
`σ.rationalInvolution.baseChange ℝ` with `harrisArchimedeanInvolution`.
Tensor induction reduces the proof to the compatibility of each chart on pure
tensors and additivity. Thus the involution on the actual tensor algebra is
identified with signature `(n-1,1)` at `C.distinguished` and the definite
signature at every other real embedding.

`realSimilitudesEquiv` transports the actual similitude groups along this
involution-compatible algebra isomorphism. Its multiplier theorem says the
real scalar multiplier is preserved. `realSimilitudesEquiv_diagonal` proves
that composing this equivalence with `σ.rationalInvolution.diagonalPoints ℝ`
is exactly `C.rationalMap`. The proof compares the underlying algebra units
using `realMatrixEquiv_one_tmul` and compares the scalar units definitionally.

## Constructed complex homomorphism

`realComplexHom` composes the corrected `harrisArchimedeanHom` with the inverse
of `realMatrixEquiv`. It therefore has target the actual algebra
`ℝ ⊗[ℚ] A`. Its star-compatibility follows by applying the injective matrix
isomorphism and using the involution comparison and the existing corrected
homomorphism's compatibility.

`realComplexHom_matrix` identifies the component at `τ` with
`correctedComplexHom n p z`, where `p = n-1` at the distinguished embedding
and `p = n` elsewhere. In the convention of the imported corrected matrix
homomorphism, the first `p` diagonal entries are `conj z` and the remaining ones
are `z`. `realComplexHom_similitudes` proves equality of the induced
homomorphisms on complex units after applying `realSimilitudesEquiv`.
Their multiplier is the common real norm square supplied by `ComplexHom`.

## Actual central-simple specialization

In `Langlands.Shimura.CentralSimpleUnitaryData`, `totallyRealBasis` derives
finite dimensionality of `K` over `E` from the quadratic degree, uses
`D.finite` for `A` over `K`, and applies transitivity to obtain a finite
basis of `A` over `E`. No basis is supplied separately in this specialization.
The `central`, `simple` and exact dimension fields of `D` remain part of the
input but are not needed for this finite-dimensional assembly argument.

`D.realMatrixEquiv C` and `D.realComplexHom C` use that derived basis.
`D.realComplexHomOfSignature h hΦ` first invokes the existing
`HarrisSignatureCharts.ofSignature` constructor and then constructs the
complex homomorphism. It assumes only the retained signature and CM-section
hypotheses in addition to the actual algebra data, rather than taking the
resulting homomorphism as an extra input.

This unit constructs the real algebra and group identification and the
complex homomorphism. It does not yet package this constructed homomorphism
as a morphism to the real pullback of the rational group scheme, nor establish
smoothness, reductivity, PEL representability or canonical scheme levels.
Those remain separate parts of the geometry task.
