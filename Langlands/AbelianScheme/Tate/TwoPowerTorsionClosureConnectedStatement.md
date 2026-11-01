# Connectedness of the actual two-power torsion closure

`TwoPowerTorsionClosureConnectedStatement` asserts that, for every algebraically
closed characteristic-zero field `K : Type u` and every actual bundled abelian
scheme `A` over `Spec K`, the Zariski closure of `twoPowerTorsionLocus A` is
connected. The universe `u` is arbitrary.

The imported locus consists of underlying scheme points represented by actual
sections over the identity test scheme whose `2^n`-th power is the identity for
some natural number `n`. The closure and connectedness are taken in the actual
scheme's Zariski topology. Connectedness includes nonemptiness.

This is a derived intermediate statement, motivated by the torsion-closure
argument in Edixhoven, van der Geer and Moonen, *Abelian Varieties*, Chapter V,
section 3, Theorem (5.30), printed page 84 / PDF page 88, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`. It is not a transcription
of a separate assertion in that source. Its derivation uses multiplication
invariance, finiteness of connected components in a Noetherian space, and the
fact that iterating multiplication by two sends each actual two-power torsion
point to the identity.

The declaration defines a proposition. This module supplies no proof of that
proposition, no density theorem, no numerical torsion formula, and no closed
subgroup scheme construction.
