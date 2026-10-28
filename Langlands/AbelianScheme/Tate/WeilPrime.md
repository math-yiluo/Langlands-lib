# The actual prime-adic Weil pairing

This internal construction takes the prime-power coordinates of the intrinsic
finite Weil pairing already transported by `finiteWeilLevelBilinearMap`.
It retains all the geometric inputs of `WeilIntegral`: an actual abelian
scheme over a quasi-separated base, its specified dual construction, the
seven tensor/Picard prerequisites, and the inverse Poincare line bundle
with its evaluation isomorphism. The relative finite transition proposition
`RelativeFiniteWeilTransitionStatement` remains an explicit argument.
This file does not prove that proposition.

For a prime natural number `p`, `primeWeilValue` pairs actual
`GroupScheme.Tate.PrimeAdic.Integral` coordinates of the abelian scheme and
its constructed dual. At coordinate `n` it uses the original finite
pairing of order `p ^ n`, including order one at `n = 0`. The conditional
finite transition lemma and the two input coherence equations show that
the output belongs to `TateTwist.Integral` of the global sections of the
test scheme. Thus its target is the actual inverse limit of roots of
unity under the p-th power transitions.

`evaluation_primeWeilValue` is the defining coordinate formula.
`primeWeilBilinearMap` bundles the same value as a bilinear map over
the actual p-adic integer ring. The additive laws follow from the finite
pairing. The scalar laws use `ZMod.map_smul` with the residue
`PadicInt.toZModPow n a`, which defines the p-adic scalar action on all
three coordinate groups. The `_apply` lemma identifies the bundled map
with `primeWeilValue`.

`primeWeilValue_unique` proves uniqueness among functions having that
coordinate formula by function and subtype extensionality.
`continuous_primeWeilValue` proves joint continuity for the existing
inverse-limit topologies. A private lemma first combines the two
continuous evaluations into a pair of discrete finite-order coordinates.
Continuity then follows from the product and subspace topology on the
root families. No finiteness assertion about the torsion groups is needed
for this argument.

`toPrime_integralWeilValue` proves compatibility with extracting
prime-power coordinates from any selected divisibility system that
contains every `p ^ n`. Its full and away specializations are
`fullToPrime_integralWeilValue` and `awayToPrime_integralWeilValue`.
The latter assumes that the prime is coprime to the excluded modulus.
All three identities are definitional, since both sides use the same
finite pairing in every prime-power coordinate.

The provenance is the internal derivation from the finite pairing,
the named relative transition hypothesis, the existing prime-adic Tate
modules and roots-of-unity twist, and the canonical coordinate maps.
The pairing keeps the finite convention `beta(y)(x)` and chooses no
roots-of-unity basis. This unit asserts no perfectness, alternation,
nondegeneracy, geometric monodromy equivariance, polarization
specialization, or rational pairing.
