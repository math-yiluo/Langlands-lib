# A common actual term for rational Jacquet cancellation

This internal construction defines `rationalCommonJacquetTerm` on every Weyl
element `w` and finite target label `K`, for a fixed coarse target label `J`
and a specified section of the actual point-normalizer quotient. A label is
supported if there exists a source label `I` for which `w` is a minimum
representative for `J,I` and `simpleImage cs w I ∩ J = K`. The value is zero
outside that support.

For a supported label, the map is actual normalized induction inside the
target Levi, preceded by actual inverse-conjugation pullback and ambient
normalized Jacquet restriction to the standard Levi at
`simpleImage cs w⁻¹ K`. The target fine label is `K` read as a finite subset
of the subtype `J`. Thus the map itself retains only `w`, `K`, the fixed
ambient data and the specified normalizer section.

`commonJacquetConjugationMembership` derives the actual fine-Levi membership
equivalence from support, the root-length and positive-simple-reflection
comparisons, and `StandardLeviConjugationStatement`. Its proof takes any
witness `I` of support. The finite identity `simpleImage_inv_inter` identifies
the source label with `simpleImage cs w⁻¹ J ∩ I`. The root-set transport for
these intersection labels then gives actual conjugation of the standard
Levis by the specified normalizer lift. Equality of the target finite label
with its subtype image follows from its containment in `J`.

`rationalCommonJacquetTerm_of_supported` evaluates the supported branch
using any proof of that membership equivalence. Proof irrelevance removes
the choice of its witness. No representation identity is assumed in this
construction.

The field and representation universes are independent, with carriers in
`max (u + 1) v`. The ambient rational points have their actual point
topology and are locally compact and nonarchimedean. Closedness of standard
Levis and radicals and the explicit finite-length and short-exact
preservation premises for the ambient and literal restricted families are
retained. Root labels have an arbitrary supplied finite enumeration.
No scheme Coxeter realization is added to the point-Coxeter comparisons.

The construction is derived from the published actual Levi-conjugation,
parabolic and intersection-label modules. Its map follows the standard
conjugated term used in the survivor construction. The actual source and
target intersection identities, Jacquet restriction in stages, equality
with actual geometric terms, geometric expansion, longest-survivor
comparison and whole rational Jacquet compatibility remain separate
obligations.
