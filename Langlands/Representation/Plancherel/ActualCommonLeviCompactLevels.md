# Actual compact product models and subgroup levels

This internal adapter identifies the actual positive-Levi coefficient fibers
with the published product compact picture and retains literal subgroup-fixed
levels, inclusion maps and refinement squares. Its provenance is the composition
of `LeviNormalizedProductCoefficients`, `ProductCompactPicture`,
`EquivalencePullback` and `Smooth.FixedVectors.Definitions`. It adds no analytic
extension assertion and no alternative coefficient normalization.

## Setting

The actual specialization uses an arbitrary nonarchimedean local field `F` in
universe `u`, an affine locally finite type connected reductive group scheme
`G/F`, a cocharacter `χ`, and `A : SmoothRep.{0,u,uV} ℂ (levi χ)`.
The inducing-carrier universe `uV` is independent of `u`. It uses an open
subgroup `K` with its displayed compactness proof. Each
`ActualCommonLeviCoherence.ParabolicPresentation χ K` supplies a cocharacter,
equality of its actual centralizer functor with that of `χ`, and the actual
rational-point factorization `G(F) = P(F) K`. The module proves no existence of
these presentations for an arbitrary compact open subgroup.

No splitness, characteristic-zero, quasi-splitness, positive-rank,
admissibility, irreducibility or unitary-character assumption is imposed on
these algebraic adapters. In particular this unit does not assert that the
subgroup-fixed spaces have finite dimension without further admissibility
input.

## Specified compact comparison

`positiveToProduct` is exactly the inverse of the published
`productInducedCoefficientLeviEquiv`. Its preliminary general-group setting
retains local compactness, the nonarchimedean group condition, second
countability, a semidirect decomposition, a closed radical and its actual
unimodular-modulus proof.

`normalizationEquiv` specializes that inverse to the actual coefficient fiber
of `ActualCommonLeviTensor`. `productCompactEquiv` first restricts its
representation equivalence to `K × K` using `equivComp`, then composes it with
`productInducedCompactEquiv` at the full actual unramified parameter transported
by `parameterTransport χ`. The resulting fixed space `productCompact` and
representation `productCompactAction` are the existing
`ProductInducedCompactPicture` and its actual right compact-group action.
The construction uses the actual smooth contragredient of the twisted object;
the published compact comparison removes its twist using
`productCompactTwistTensorEquiv`, retaining the underlying linear functionals.
It is not a supplied coefficient equivalence.

This is an algebraic carrier comparison. It introduces no Haar measure,
formal degree, integral or rescaling. Consequently it does not replace the
compact-probability coefficient maps or the source inverse-formal-degree forms.
New specialized evaluation identities are not exported here; the construction
is defined as the displayed composition of the published comparisons.

## Maps and refinement proofs

`compactMap` takes an explicitly displayed actual coefficient intertwiner `T`,
restricts its equivariance to `K × K`, and conjugates it by the two specified
`productCompactEquiv` maps. This helper does not assert that an arbitrary input
`T` is a normalized standard comparison. `compactMap_square` proves the square
on every coefficient vector: its proof applies the target comparison and `T`
to the source comparison's inverse identity.

For an open subgroup `H` of `K × K`, `level` is the literal submodule of vectors
fixed by `H`. For `H' ≤ H`, `levelInclusion` is the submodule inclusion from
`H`-fixed to `H'`-fixed vectors. The proof simply restricts the original
fixed-vector assertion to the smaller subgroup. `levelInclusion_val` records
that every vector is unchanged, and `levelInclusion_trans` proves that two
successive refinements equal the direct inclusion by linear-map extensionality.

`levelMap` applies the published `fixedVectorsMap` to the specified
`compactMap`. `levelMap_inclusion` is the commuting square with the actual
submodule inclusions into the full compact pictures. `levelMap_refinement`
proves the square for each `H' ≤ H`; both paths have the same underlying
vector, so extensionality and reflexivity establish it. These are algebraic
inclusion/refinement laws for any displayed intertwiner, available in particular
when the later closed targets specify the actual standard comparison.

No generic nonemptiness, denominator, rationality, unitary regularity, cocycle,
Weyl descent or smooth coherent-section comparison is concluded by this unit.
Those remain distinct targets of the host task. The unit exports no additional
axiom or unfinished proof.
