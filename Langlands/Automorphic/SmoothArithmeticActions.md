# Rational automorphism and CM actions on smooth adelic functions

Author: Worker 2.

For an actual number field in any universe and every natural matrix rank,
including zero, this internal construction restricts the actual arithmetic
function pullbacks to both existing smooth spaces. The coefficient field is
the usual complex field, and complex values are fixed. The first space uses
real smoothness of infinite slices and local constancy of finite slices. The
second uses real smoothness and a common open finite stabilizer.

`smoothGaloisAut` and `finiteSmoothGaloisAut` are monoid homomorphisms from
the actual rational field automorphism group to continuous complex-linear
automorphisms of these spaces. An automorphism acts by pullback along its
inverse. The intrinsic identity and contravariant composition laws of the
actual smooth arithmetic equivalences prove the homomorphism laws.
`smoothGaloisAction` and `finiteSmoothGaloisAction` are installable additive
left actions; no global action instance is installed.

The underlying functions agree with the existing ambient `galoisAut`.
Evaluation uses the actual inverse arithmetic matrix map. Both actions
intertwine full right translation with the displayed inverse arithmetic
transport of the group argument. The existing inclusion of the
common-stabilizer space into the slice-wise smooth space commutes with the
actions. `smoothGaloisCentralCharacterEquiv` restricts to the actual smooth
specified-character spaces and transforms the character by the existing
Hecke-character Galois action. Existence of compact open finite level is
preserved and reflected for smooth functions.

For an actual CM field, `smoothComplexConj` and `finiteSmoothComplexConj`
are direct pullbacks by the actual CM involution on the adelic matrix group.
Their underlying functions agree with ambient `complexConj`. They are
involutive and agree with the rational inverse-pullback action after
restricting the CM automorphism to rational scalars. Their evaluation and
full right-translation equations use the existing `CMConjugation.adelicConj`.
They commute with the same actual inclusion.

`smoothCMCentralCharacterEquiv` carries the character to the existing
`HeckeCharacter.complexConj`, whose value is
`chi (ideleClassComplexConj x)`. Compact open finite level is preserved and
reflected on the smooth space. Finiteness of the orbit span under the actual
`standardInfiniteCompact` is also preserved and reflected. The latter uses
the ambient proof that the CM preimage of that particular subgroup is
itself; it does not assert that identification for arbitrary field
isomorphisms.

Provenance is internal restriction and specialization of
`SmoothArithmeticTransport` and `AmbientArithmeticTransport`. All action,
involution, covariance and invariant-condition laws follow from their proved
intrinsic laws on the actual spaces, rather than supplied preservation
hypotheses. Continuity refers to the subspaces' inherited compact-open
topology. This file introduces no derivative-topology assertion, growth or
enveloping-center finiteness result, cuspidality preservation, automorphic
occurrence, spectral existence or classification theorem.
