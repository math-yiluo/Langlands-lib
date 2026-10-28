# Reversed inverse-transpose Langlands data

Author: Worker 111.

This internal construction specializes the published inverse-transpose
transport to a genuine `TemperedLanglandsDatum`. The field universe and block
carrier universe remain independent.

`inverseTranspose` reverses the actual block shape. At index `i`, its block is
the original block at `i.rev`, on the original carrier, with action pulled back
through `GeneralLinear.inverseTranspose`. Its real exponent is the negative
of the original exponent at `i.rev`. Irreducibility follows from the published
continuous group equivalence transport. Temperedness follows from
`T.isTempered_comp_continuousMulEquiv`, which retains admissibility for every
open subgroup and the coefficient bounds for every Haar measure on the
central quotient. `Parabolic.reverseNegateStrictAnti` proves strict decrease.
The component formulas are definitional.

`inverseTransposeTwistedBlockIso` compares pullback of an original determinant
twist with the corresponding twist of the reversed datum. It uses the
published equality `Parabolic.inverseTransposeDeterminantTwist` and the
identity linear equivalence on the original block carrier.

`inverseTransposeProductEquiv` first compares the explicit raw normalized
products on the original block carriers. For positive ambient rank,
`Parabolic.normalizedProductInverseTranspose` compares pullback of the original
upper normalized induction with upper normalized induction of the reversed
pulled-back twisted blocks. Its published proof uses the actual opposite
parabolic and block-reversal map on smooth covariant functions, retaining
uniform open stabilizers. The determinant-twist identity gives an equality of
the target representation families. The proof applies `congrArg` to the
family-dependent equivalence type and transports the selected equivalence
through that equality with `Eq.mp`. It does not change the carriers.

`inverseTransposeStandardModuleEquiv` is then an actual complex-linear
equivariant bijection from inverse-transpose pullback of
`d.standardModule.representation` to
`d.inverseTranspose.standardModule.representation`. A private generic helper,
`productPullbackBundledEquiv`, rebundles the two raw product actions by the
definitional description of `normalizedProductInductionFunctor`. The two
families of bundled raw blocks equal the actual twisted-block families by
reflexivity; applying the induction functors gives equalities with the two
standard modules. `congrArg₂` on their equivalence type followed by `Eq.mp`
transports the rebundled equivalence to the stated endpoints. This explicit
transport keeps Lean from repeatedly unfolding the full tensor and induced
function carriers when comparing the endpoint types.

Both standard modules act on the original `GeneralLinear n F.Carrier`, and
their carriers have universe `max uF uV`. There is no universe lift, supplied
representation equivalence, or additional analytic hypothesis.

The provenance is internal: `LanglandsData` supplies the genuine datum and its
actual twisted blocks, `CompactCoefficient.GroupTransport` supplies bundled
smooth pullback and irreducibility transport, `InverseTransposeAnalyticProof`
supplies analytic temperedness transport, and `InverseTransposeProductProof`
supplies the normalized-product, determinant-twist and finite-order
compatibilities. This construction
does not identify pullback with a smooth contragredient and supplies no
Whittaker assertion or L-polynomial existence or product theorem.
