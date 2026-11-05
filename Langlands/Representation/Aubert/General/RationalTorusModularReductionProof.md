# The ambient modular character on actual torus points

Authors: Worker 103 (proof and original exposition); Worker 1658 (verification
and submission).

The theorem `rationalTorusModularReduction` proves exactly
`RationalTorusModularReductionStatement` in every universe. Its explicit
structural inputs remain premises.

The proof uses the empty root face of the supplied simultaneous basis. It
identifies its Levi with the whole-torus centralizer through the
generic-centralizer statement. At the empty face of the reversed chamber,
the negative generic cocharacter itself is standard; the standard-cocharacter
statement and the negation/inverse comparison identify the basis's opposite
factor with `oppositeUnipotent i ν`. The affine dynamic intersection theorem
shows that factor is disjoint from the original standard parabolic.

Fix an actual torus point. Its inner conjugation restricts to the identity on
the Levi, because scheme centralization implies pointwise centralization.
On the two radicals it restricts to the actual normalizer-conjugation
automorphisms supplied by the standard and opposite semidirect decompositions.
Closedness supplies local compactness of all three factors. Apply the general
Iwahori Haar-product statement to this common basis and these compatible
automorphisms. Its middle factor is `1`, and actual opposite Haar reciprocity
cancels the two remaining factors. The published comparison of inner-conjugation
Haar modulus with Mathlib's modular character gives the conclusion.

The normalizer characters use the Borel measurable structure on each radical,
whereas the Haar-product interface uses the inherited subtype structure. A
private helper identifies the two Haar characters by replacing a Borel-space
measurable structure with the Borel structure before applying reflexivity.

No root-negation closure or relative-root-system statement is used. The proof
does not construct the basis or prove its explicit structural premises.

This is an internal deduction from the published statement and subgroup
comparisons named above. It adds no literature assertion or outer premise to
the target, and it leaves the target and all imported modules unchanged.
