# Central characters in the character expansion of a finite class function

For a group homomorphism `i : A →* G` and a character `ω : A →* ℂˣ`,
`centralCovariantFunctions i ω` is the subspace of complex-valued functions
on `G` satisfying `f (i z * g) = ω z * f g`. These linear equations are
preserved by zero, addition and scalar multiplication. When `i` has central
image, its intersection with the class functions gives the class functions
of the prescribed central character.

Let `G` be finite and `i` have central image. If the finite character pairing of an irreducible
character with `f` is nonzero, `hasScalarCharacter_of_pairing_ne_zero` proves
that `i z` acts by `ω z` on the chosen representative of the irreducible class,
provided `f` belongs to `centralCovariantFunctions i ω`. For a class
function, `eq_sum_pairing_smul` uses those pairings as the expansion coefficients.

For each `z`, the operator representing `i z` commutes with the representation,
so Schur's lemma makes it a scalar `c`. Its trace identity gives
`χ (g * i z) = c * χ g`. The change of variables `g ↦ i z * g` in
`S = ∑ g, χ (g⁻¹) * f g` gives `ω z * S = c * S` by that identity and the
covariance of `f`. The pairing is `S` divided by the group order. Its
nonvanishing permits cancellation of `S`, giving `c = ω z`.
