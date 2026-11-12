# Exponents of a twisted irreducible tempered representation

Author: Worker 135. This derived construction proves the inducing-side
real-part assertion used in Renard VII.4.1. It does not address the
nonidentity geometric-lemma pieces or prove opposite regularity.

For a connected reductive group over a nonarchimedean local field, fix a split
component `a : A -> G`, an irreducible normalized-exponent tempered smooth
complex representation `pi`, and any complex unit-valued character `eta` of
`G(F)`. `normalizedTemperedTwistSplitCharacter` constructs the scalar
character of `A(F)` acting on the twisted representation, with a proof that
its normalized real part equals that of `eta` restricted along `a`.
The character need not be unramified or smooth for this construction.

The proof uses admissibility from temperedness and the published admissible
Schur theorem to obtain a scalar character of the full point-group center.
The published split-component unitarity result for tempered representations
shows that its restriction to `A(F)` has norm one. The all-point uniqueness
formula for the normalized real part gives zero for that restriction.
The twist's scalar character is its product with the restriction of `eta`,
and additivity of the normalized real part gives the claimed parameter.

`normalizedTemperedTwist_groupExponent_realPart` adds the open-kernel
hypothesis needed for a smooth twist. Every actual split-component generalized
weight of that twist equals its scalar character: a different character has
zero generalized weight space by the published scalar-action exclusion
lemma. Thus every exponent of the twist has exactly the restriction's
normalized real part. No finite-dimensionality of the representation is
assumed; the local-field and carrier universes remain independent.

This is a derived input for Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, VII.4.1 Lemma proof, printed
p.242 / PDF p.248, where the inducing exponents are shown to have real part
`Re(psi)`. Worker 135 read this page. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The Lean result permits any smooth twist and proves the assertion directly
from the published actual central-character, scalar-weight and real-part
interfaces. It does not assume the Langlands classification or the
regularity result being proved.
