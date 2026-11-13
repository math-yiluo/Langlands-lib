# Compactness controls rational multipliers of actual Harris frames

This internal unit combines the actual frame multiplier comparison with
published idelic norm and compact subgroup results. It preserves the original
Harris group, level, compatible frame and rational self-isogeny.

`AlgebraInvolution.oppositeFiniteAdelicMultiplier` is the actual original
multiplier as a continuous character on the opposite finite adelic group.
Its values lie in the finite ideles of the rationals. Commutativity of the
target makes it multiplicative despite the opposite group convention, and
continuity follows from the original multiplier and `MulOpposite.unop`.

`Global.abs_rat_eq_one_of_compact_character` says that if a continuous character
on a compact subgroup takes an element to the diagonal image of `q : ℚˣ`,
then `|q| = 1`. The proof composes the character with the published normalized
finite idelic norm, which is a continuous positive-real unit character. The
published compact-subgroup theorem makes its value one. The norm of a diagonal
rational finite idele is the reciprocal of the rational absolute value; since
the field is the rationals, its field norm is the rational number itself.
Reflecting equality from the reals and removing the reciprocal proves the claim.
`abs_multiplier_eq_one_of_mem_compact` specializes this to the actual opposite
Harris multiplier character.

`abs_multiplier_eq_one_of_original_level_frame` uses the actual frame equation
to identify the multiplier with diagonal `q`. Original level membership and
the compactness carried by every Harris level then imply `|q| = 1`.
`abs_multiplier_eq_one_of_levelIso_fixed` extracts that frame equation from an
actual fixed invariant level orbit and obtains the same conclusion. Smallness,
finite order and faithfulness are not required for these conclusions.

`multiplier_eq_one_of_levelIso_fixed_of_pos` adds the explicit premise `0 < q`
and concludes `q = 1`, by removing the absolute value. Deriving this positivity
from the actual polarization remains an obligation, together with the finite
order and one-prime faithfulness steps of the exact rigidity theorem.

All content is an internal derivation from the imported actual constructions
and published norm/compactness theorems; no new external source attribution is
made. The final small-level rigidity statement remains open.
