# Actual level structure from divisor cardinalities

`levelTorsionKernelEquiv` identifies `GroupScheme.Tate.Level G T n`
with the actual kernel of multiplication by `n` on the additive section
group `Additive (T ⟶ G.X)`. Its maps retain the underlying section. The
published `mem_levelGroup` theorem identifies membership with the
annihilation equation. This works for every natural `n`.

For positive `n`, `levelLinearEquivOfDivisorCard` constructs a
`ZMod n`-linear equivalence from `Fin r → ZMod n` to the actual
`Level G T n`, assuming that every positive divisor `d` has
`Nat.card (Level G T d) = d^r`. It transports these cardinalities through
the preceding comparison and applies the proved generic torsion
classification. The resulting additive equivalence is linear by
Mathlib's `ZMod.map_smul`, which uses the integer-defined residue actions
already installed on both groups. No replacement module action is used.

This is an internal specialization of `FiniteTorsionClassification` to
the published actual-level definition and residue action in `Integral`
and `PrimeAdic`. It includes level one and zero coordinates. The
divisor-cardinality hypotheses are explicit; this module does not
establish the numerical geometric degree formula that supplies them for
abelian schemes.
