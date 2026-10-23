# Constructed Harris map to the rational group's real pullback

This module constructs the Deligne group-scheme homomorphism for the given
central simple CM algebra, using the complex homomorphism constructed from
its actual real-place signature charts. Its target is the categorical real
base change of the algebra's rational similitude group scheme.

## Hypotheses, provenance and scope

All declarations lie in `Langlands.Shimura.CentralSimpleUnitaryData`.
The inputs are totally real `E` and totally complex `K`, both number fields,
a quadratic algebra structure `E → K`, and a ring `A` with compatible
`E`, `K` and rational algebra structures. The tower assumptions are
`IsScalarTower E K A`, `IsScalarTower ℚ E A` and `IsScalarTower ℚ K A`.
The carriers are in `Type`, as required by the existing scheme construction.
The central-simple input is `D : CentralSimpleUnitaryData E K A n`.
The chart input is `C : HarrisSignatureCharts D.toSecondKindInvolution n Φ`.
The two purely pointwise lemmas do not need the rational-to-`K` tower.

This is an internal specialization of `RealSplitting` and
`RationalScalarExtension`, with the existing algebraic point constructions
from `Deligne` and `DeligneGroupScheme`. The first import constructs the
actual matrix assembly and complex homomorphism, with their proven
compatibilities. The second identifies the real pullback of the rational
group scheme with the scalar-extended coordinate model and transports Deligne
maps across that isomorphism. No new external theorem is invoked here.
The corrected Harris and Kottwitz conventions inherit their source provenance
from `Domain`, `Positivity` and `Deligne`; both conjugation and inversion are
retained explicitly.

No complex homomorphism, output group scheme, or comparison theorem is an
additional input. The rational group scheme, its pullback, its comparison
isomorphism and the complex homomorphism are all the existing constructions
on the actual algebra and involution. Existence of the prescribed signature
remains a hypothesis. This unit does not prove smoothness, reductivity, PEL
representability, canonical-model descent or existence of scheme levels.

## Actual group-scheme maps

Write `σ = D.toSecondKindInvolution.rationalInvolution`,
`h = D.realComplexHom C`, and `e = D.realGroupSchemeIso`.
`harrisDeligneMap` is the composite

\[
\mathbb S \xrightarrow{h} G(\sigma_{\mathbb R})
\xrightarrow{e^{-1}} G(\sigma)\times_{\operatorname{Spec}\mathbb Q}
\operatorname{Spec}\mathbb R.
\]

Here `D.rationalBasis` supplies the rational coordinate model and its real
base change supplies the middle model. The result is a morphism of group
schemes, including compatibility with multiplication, unit and inversion.
`harrisDeligneMap_comparison` proves that composing with `e` recovers
`h.deligneGroupSchemeMap`.

`harrisInverseDeligneMap` uses `h.inverseDeligneGroupSchemeMap` before
transport. Its comparison theorem recovers exactly that inverse-convention
map. This auxiliary inverse of the Harris map is distinct from the Kottwitz
construction below, which also uses complex conjugation.

`harrisDeligneMapOfSignature hsig hΦ` obtains `C` using
`HarrisSignatureCharts.ofSignature hsig hΦ` and applies `harrisDeligneMap`.
Thus the actual group-scheme map is constructed from the signature predicate
and CM-section predicate without supplying charts separately.

## Affine test schemes and real matrix coordinates

For every commutative real algebra `S` and affine Deligne point `f`,
`harrisDeligneMap_affinePoints` proves that the point obtained after composing
with `e` corresponds to

\[
h_S\bigl(\operatorname{affinePointsEquiv}(f)\bigr).
\]

The target equivalence is `similitudeAffinePointsEquiv`, so the expression is
an actual unit in `S ⊗[ℝ] (ℝ ⊗[ℚ] A)` with its multiplier.
`harrisInverseDeligneMap_affinePoints` has the same formula at the inverse
Deligne point. These identities follow from the published rational-to-real
transport formulas.

`harrisDelignePoints_real_matrix` evaluates the point construction at a
complex unit `z`. It uses the actual complex-to-quadratic-algebra map at `ℝ`,
removes the outer tensor factor with `Algebra.TensorProduct.lid`, and applies
`D.realMatrixEquiv C`. The component at a real embedding `τ` is
`correctedComplexHom n p z`, where `p = n-1` at the distinguished embedding
and `p = n` elsewhere. Its first `p` diagonal entries are `conj z`, with
remaining entries `z`.

`harrisDeligneMap_real_matrix` proves this formula for the actual scheme
morphism: it takes the affine Deligne point corresponding to `z`, composes it
with the constructed map and `e`, and applies the target affine point
equivalence before the tensor cancellation and matrix chart. Its proof first
uses `harrisDeligneMap_affinePoints`, cancels the source point equivalence,
and then applies the preceding point formula.

`harrisDelignePoints_multiplier` identifies the multiplier with the Deligne
norm on every real algebra. The displayed tensor point formula and multiplier
use the constructed `h`; neither is a supplied comparison assumption.

## Kottwitz convention

`kottwitzDeligneMap` transports the inverse group-scheme map of `h.conj`, where
`h.conj` is `h` precomposed with complex conjugation. This is the same
conjugate-then-inverse convention as `kottwitzHom` and
`kottwitzDeligneGroupSchemeMap` on the standard archimedean matrix model.
`kottwitzDeligneMap_comparison` recovers the inverse group-scheme map of
`h.conj` after composing with `e`. `kottwitzDeligneMap_affinePoints` gives
`h.conj.delignePoints S` evaluated at the inverse affine Deligne point.
These formulas preserve both operations explicitly.
