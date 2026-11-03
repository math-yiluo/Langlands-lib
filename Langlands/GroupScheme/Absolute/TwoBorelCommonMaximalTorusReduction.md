# Common maximal tori from independent absolute Bruhat inputs

This derived construction assembles two structural hypotheses into the
published `TwoBorelCommonMaximalTorusStatement`. The hypotheses are
`BorelConjugacyStatement` and `AbsoluteBruhatCoveringStatement`, both at the
same arbitrary universe as the conclusion. They must be proved independently.
This module does not establish either input or the unconditional conclusion.

`commonMaximalTorusOfBorelBruhatInputs` takes those hypotheses, an algebraically
closed field of any characteristic, an actual connected reductive group `G`,
and two actual Borel subgroup homomorphisms `i` and `i'`. It returns a
commutative group scheme `T`, an ambient maximal-torus homomorphism `t`, and
actual homomorphisms `f` and `f'` into the two Borels, together with
`f ≫ i = t` and `f' ≫ i' = t`.

First, the published
`borelMaximalTorusStatement_of_borelConjugacy` supplies an ambient maximal
torus `j` in the first Borel using the Borel-conjugacy hypothesis. Next,
Borel conjugacy supplies `g` and `φ` with
`i ≫ Int(g) = φ.hom ≫ i'`. Absolute Bruhat covering for the chosen Borel pair
supplies `g = i(b₁) * n * i(b₂)` with `n : normalizerPoints j`.
`commonTorusOfNormalizerDoubleCoset` then supplies the actual common-torus
maps and their required equalities. A classical choice extracts the data
from these existence statements.

`twoBorelCommonMaximalTorusStatement_of_borel_bruhat_inputs` packages this
construction as an implication from the two independent hypotheses to the
unchanged Library proposition. Smoothness, affineness and connectedness are
supplied by `IsConnectedReductive G`; there is no added structural assumption.

The provenance is internal derivation from the named Library interfaces and
the explicit normalizer double-coset construction. No rational Bruhat
decomposition, Borel–Tits 4.18, or parabolic-intersection result is used.
This conditional implication does not discharge the task's unconditional
proof requirement.
