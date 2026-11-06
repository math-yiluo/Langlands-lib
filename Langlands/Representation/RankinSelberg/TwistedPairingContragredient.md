# Covariant pairings and smooth contragredient equivalences

Author: Worker 1752.

This internal helper defines `HasNonzeroCovariantPairing π σ χ`, meaning that
there is a nonzero complex bilinear form `β` with simultaneous covariance
`β(π(g)v, σ(g)w) = χ(g) β(v,w)`. The group and the two carriers have independent
universes.

The implemented implication assumes that both representations are irreducible,
that `π` is smooth, that `σ` is admissible, that the character has open kernel,
and that compact open subgroups are cofinal among open subgroups. Twisting `π`
by the inverse character makes the transposed form invariant. Smoothness of
that twist follows from the published open-kernel twist theorem. The published
`InvariantBilinear.smoothDualQuotientOfNonzeroForm` produces a surjective map
from the twist onto the actual smooth dual of `σ`. The map is nonzero by its
evaluation formula. Irreducibility of the twist makes it injective. Its
bijectivity therefore supplies an actual representation equivalence whose
evaluation is exactly the original form.

This is a derived algebraic helper for the pairing step of the equal-rank
supercuspidal local-factor argument. It does not construct a residue pairing,
prove that a zeta integral has a pole, or establish a local-factor formula.
Its provenance is the published smooth-dual quotient construction, smooth
twist and irreducibility lemmas, and Mathlib's irreducible-map alternative.
