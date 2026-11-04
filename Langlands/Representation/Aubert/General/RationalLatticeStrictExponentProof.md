# Applying the literal valuation chamber condition to uniformizer rays

Author: Worker 19.

`rationalLatticeStrictExponent` proves the complete
`RationalLatticeStrictExponentStatement` at independent universes `u` and `v`.

The helper `isNoncentralNegativeTorusPoint_uniformizerSection` first proves
that the chosen field uniformizer has valuation below one. It uses
`FML.ord_lt_ord_iff` and `LocalField.ord_uniformizer`, so this concerns the
same canonical valuation as the target. Nonzeroness gives positive valuation.
`CocharacterUniformizer.rationalCharacterEval_cocharacterPoints` identifies
the actual simple-root value at a uniformizer cocharacter point with the
integer-pairing power of that uniformizer. Applying the valuation, the
standard inequalities for integer powers prove both parts of the literal
`IsNoncentralNegativeTorusPoint` predicate.

In the main proof, reductive smoothness supplies local finite type, and
`IsSplitTorus.finite_simpleRelativeRoots` supplies finiteness for the actual
root labels. The displayed `StandardCocharacterStatement` supplies the
standard witness for `J`. `uniformizerPowers_mem_levi` and
`commute_uniformizerPowers` then construct the same actual uniformizer power
as a point of the full center of the actual Levi. Applying the supplied
strict exponent condition at its actual torus preimage proves the bound
for every full-center exponent of the actual normalized Jacquet module.

The proof uses only the cited published evaluation, root-finiteness and
Levi-centrality declarations together with the statement's premises. It
uses no representation classification, geometric lemma, adjointness,
character independence, or cuspidal support result. No contraction,
coefficient, volume, or integrability assertion is inferred here.
