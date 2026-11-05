# Exact norm stabilizer from actual integral coordinates

Worker 84 implements an assembly lemma for the existing
HasExactUnitNormStabilizer predicate. It does not construct the character or
prove AuxiliaryCharacterStatement. Its explicit premises are the computed trace
formula for all actual integral-coordinate units and detection of each unwanted
trace difference; those are discharged by the other helper modules in the final assembly.

For an actual base scalar a whose image in M has canonical norm less than one,
and an integral y, the ultrametric norm shows that z=1+i(a)y is nonzero and has
norm one. Every base automorphism preserves the canonical norm, hence preserves
the actual canonical integer ring. Its action takes z to the integral-coordinate
unit with y replaced by sigma(y), because it fixes a.

If the norm-character pullback were invariant on all norm-one units for an
unwanted sigma, apply that equality to this actual z and use the two prescribed
coordinate formulas. Forgetting the complex unit structure equates the two
additive-character values. Additivity makes the character of their difference
one, contrary to the detection witness. Thus the stabilizer contains no unwanted
automorphism. Conversely, an automorphism fixing L preserves the actual L norm
by the proved norm_units_fixed helper, hence preserves every norm-character
pullback. This gives the exact equivalence on actual valuation units.

The carrier universes are independent. The proof uses no odd-prime hypothesis,
finite-order premise or reciprocity input. The construction, scaling parameters,
depth and actual formula/detection premises are discharged in
AuxiliaryCharacterFirstOrderProof. This file establishes only its stated
conditional stabilizer lemma; independent review covers the full proof bundle.
