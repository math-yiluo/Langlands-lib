# The rational determinant restriction and the Galois-fixed Lie weight sum

This is a derived internal construction from `Lie/ActionBaseChange`,
`Lie/DeterminantWeightCharacter`, and `Rational/CharacterBaseChange`. It uses the
actual algebraic action, its dual-number Lie kernels, its rational determinant
character, and the existing character-lattice transport. It introduces no new
structural theorem premise.

For an action of an affine group scheme `H` on an affine group scheme `U` over
`Spec k`, natural finite Lie coordinates `c`, and a morphism `j : T → H` from a
commutative group scheme, `AutomorphicAction.lieDeterminantCharacter` is the
restriction to `T` of the actual rational Lie determinant character. Its
definition requires only a commutative base ring; it does not require `T` to be
a torus or split. When `k` is a field and `T` is split, the comparison lemma
identifies it with the integral sum of actual Lie weights, repeated by their
weight-space dimensions.

For a commutative ring `k`, an extension field `K` with a `k`-algebra structure,
and any choice of natural finite coordinates on `U_K`,
`lieDeterminantCharacter_baseChange` identifies the pullback of this character
with the determinant restriction of the actual pulled-back action. The two
coordinate systems may have different ranks. The proof combines the actual
determinant-character base-change theorem with restriction compatibility.

If `T_K` is split, `lieWeightCharacter_eq_baseChange_lieDeterminantCharacter`
therefore identifies the actual dimension-weighted Lie character on `T_K` with
the base change of a character defined over `k`. Consequently
`transport_lieWeightCharacter` proves fixedness under canonical transport along
every endomorphism of `Spec K` over `Spec k`, and
`galoisRepresentation_lieWeightCharacter` proves fixedness for every algebra
automorphism in the existing Galois representation. Neither conclusion needs
the extension to be finite or Galois. These proofs use fixedness of an actual
base-changed character; they do not transport individual weight spaces.

Finally, `lieDeterminantCharacter_ne_zero_of_baseChange_pos` states that if the
actual extended Lie module is nonzero and a supplied cocharacter pairs strictly
positively with every nonzero actual weight space, then the original restricted
determinant character is nonzero. Otherwise its base change, hence the weighted
Lie character, would vanish, contrary to the existing positivity theorem.

The strict positivity condition is an explicit input. This file does not
construct root reflections, prove a geometric sign or containment assertion, or
prove the minimal-parabolic Levi centralizer theorem. The character comparisons
are equalities of actual group-scheme characters, not only equalities on
field-valued points.
