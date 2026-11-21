# Quaternion conjugation in a two-by-two matrix chart

`QuaternionicSplitConjugationStatement` identifies standard quaternion conjugation, over any field extension admitting a two-by-two splitting chart, with the adjugate of a two-by-two matrix. The original central quaternion division algebra is over a field of characteristic zero. The formula holds for every element, including singular matrices. Multiplying the adjugate on the right by the standard alternating matrix gives the transpose multiplied by the same alternating matrix on the left.

The reduced norm is the determinant in the supplied chart. Apply the conjugate-product norm identity to an element and to the element plus one. The determinant of a two-by-two matrix plus one differs from its determinant by its trace plus one. Subtracting the two conjugate-product identities shows that the sum of the matrix and its conjugate is its trace times the identity. The entrywise adjugate formula identifies the conjugate.

This gives the split quaternion conjugation used in the matrix formula of Springer's appendix to Kneser's *Lectures on Galois Cohomology of Classical Groups* (1969), §1, equation (2), printed p. 106 (PDF p. 112).
