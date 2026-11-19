# Real standard parameter uniqueness from the elliptic Cartan comparison

`RealStandardEllipticCartanComparisonStatement` concerns the actual
`O(n)`-finite real standard modules. It takes the ranks, positive induced
weights, irreducibility and bijective intertwiner from
`RealPositiveWeightStandardUniqueStatement`. It asks for enumerations of the
two kinds of blocks with common lengths and equal functions `numerator` on
the resulting Cartan coordinates. The enumerations may be permutations of
the given lists. The intertwiner acts on the original lists in their given
orders.

`realStandardEllipticCartanReduction` proves
`RealStandardEllipticCartanReductionStatement`, the implication from that
comparison to positive-weight uniqueness. A permutation sends every
enumerated induced block back to a member of the original list, so each
enumerated induced weight is positive. The finite numerator recovery
theorem gives separate permutations of the induced blocks' weight and
exponent pairs and the real characters' parity and exponent pairs.
The fields determine the actual character data through their signed-power
formulas. The list permutation lemmas then put the two comparisons together.

The reduction is internal. Its open input is the comparison of the
numerators for isomorphic modules. The numerator calculation itself is in
`RealStandardEllipticCartanNumerator`.

The intended proof of the comparison uses the induced trace formula and
its Cartan support in Knapp's *Representation Theory of Semisimple Groups*
(`provided-40cace9c0f8c2361e7b3d7459f7908362f819b68114945405f1c16d968b21855`),
Chapter X, (10.21) on p. 348, (10.27) on p. 352 and Proposition 10.19 on p. 353.
An inducing Levi with `r` blocks of size two meets regular Cartans with
at most `r` nonreal conjugate eigenvalue pairs. On a Cartan with exactly
`r` such pairs, each pair occupies one size-two block and each real eigenvalue
occupies one size-one block. The Weyl sum then gives the two slot permutations
of `numerator_apply`.

Knapp's Corollary 10.13, pp. 343–344, gives the elliptic character for the
sum of the two discrete series of `SL(2, ℝ)` with lowest absolute compact
weight `m + 1`. Restricting the size-two block in Knapp 1994, (2.1a) and
(2.2b), pp. 399–400, to `SL(2, ℝ)` gives this sum. The determinant twist adds
the radial exponential with exponent `2t`. Clearing the common Weyl factors
on each angle component leaves the signed difference of the modes `m`
and `-m`. The finite character calculation detects a nonzero coefficient
at the original positive tuple, so the character on this Cartan detects
`r`. The character equality is compared on the regular locus in each
sign component and extends to the finite numerators by continuity.

These formulas describe the intended application to the given real models.
The remaining proof needs trace character invariance under the actual
compact and Lie intertwiners and the specialization of the induction
formula to the possibly disconnected `GL_n(ℝ)` and its block Levis.
