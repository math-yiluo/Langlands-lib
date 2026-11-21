# Compatible archimedean quotient measures

`archimedeanQuotientMeasureData` chooses ambient Haar measure, upper-unipotent Haar measure and a compatible quotient measure for the local Rankin–Selberg integral. It gives the existing `RealQuotientMeasureData` and `ComplexQuotientMeasureData` at every rank. The quotient measure is right invariant and satisfies the Weil formula for the chosen Haar measures.

The upper unipotent is unimodular. Multiplying its `(i,j)` entry by `z^(j-i)` for `i < j` is a continuous group automorphism when `z` is nonzero. Its inverse uses `z⁻¹`. The same entry formula extends continuously to `z = 0`, where it gives the identity matrix. The modular character is invariant under each automorphism and is continuous. Applying these facts along the nonzero powers of `1/2` shows that the character equals one. For the general linear group the proof uses the Library's characterization of a positive character trivial on scalar matrices. Scalar matrices act by identical left and right translations, so the modular character meets that hypothesis. The closed-subgroup quotient measure theorem then applies to the resulting regular two-sided Haar measures.

This supplies legitimate local measures for Jacquet (2009), §2, displays (2.4) and (2.6), p. 6 of the author-posted version. The construction uses Haar choices and the compatible quotient measure in the Library.

[Compatible quotient measures over locally compact fields](LocallyCompactFieldQuotientMeasures.md) proves existence over a locally compact, second-countable, nontrivially normed field.
