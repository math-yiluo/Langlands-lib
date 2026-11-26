# Compact rational quotients of Weil twisted centralizers

`generalLinearWeilTwistedCompactQuotient` proves
`GeneralLinearWeilTwistedCompactQuotientStatement`. The regular elliptic norm associate
`γ` and a rational twisted conjugation put the ordered norm into exact base-change form.
`exactRegularNormCentralizerEquiv` then identifies the upper twisted centralizer with the
ordinary centralizer of `γ` by extending coefficients. The fixed-coefficient hypothesis
comes from `adeleCoefficientAut_fixed_iff` on the actual adelic coefficient ring.

The determinant of a scalar-extended matrix is the scalar extension of its determinant.
The normalized absolute value on the included idele is the extension-degree power, by
`ideleNorm_ideleInclusion` and `full_ideleNorm`. That power preserves and reflects the
norm-one condition. The resulting map from the ordinary norm-one centralizer to the
original twisted centralizer is continuous and surjective. Its formula first extends
coefficients, then reverses the rational conjugation and applies inverse Weil coordinates.
Each step respects rational points. Therefore the induced map of rational left quotients
is a continuous surjection. `adelicRegularCentralizerCompactQuotient` gives compactness
of its source from the irreducible separable characteristic polynomial of `γ`.

This is the regular case of the centralizer comparison in Arthur and Clozel, *Simple
Algebras, Base Change, and the Advanced Theory of the Trace Formula* (1989), Chapter 1,
§1, Lemma 1.1, pp. 3–4, combined with the norm-one convention and twisted centralizer
volume in Getz and Hahn (2024), §§2.6 and 18.5.
