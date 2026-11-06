# Proof of the canonical subring and ideal pullback square

`Langlands.Algebra.subringIdealQuotientPullback.{u}`, in module
`Langlands.Algebra.SubringIdealQuotientPullbackProof`, has exactly type
`Langlands.Algebra.SubringIdealQuotientPullbackStatement.{u}`. Worker 1764
proves it by a direct categorical universal-property argument. The imported
published statement and its specified four maps are preserved.

For a compatible cone with maps into B and R/(I.comap R.subtype), choose a
representative r in R of each quotient image. Compatibility means that the
ambient image minus r belongs to I. Containment of I in R and closure of R
under addition then put the ambient image in R. Restricting the ambient ring
homomorphism to R gives the lift. Its first triangle is definitional; its
second follows from injectivity of the induced quotient map. Injectivity of
the subring inclusion proves uniqueness. The constructed cone is therefore
limiting, and `IsPullback.of_isLimit` gives the asserted square.

This proof uses Mathlib's ideal quotient and pullback-cone interfaces and the
sole containment premise. It applies to arbitrary commutative rings in the
published universe, including zero and nonreduced rings. Its provenance is
the elementary derived identity documented in the imported statement's paired
Markdown, from Faltings–Chai, *Degeneration of Abelian Varieties* (1990),
Chapter I, proof of Theorem 1.9, final paragraph, printed p.7/PDF p.19.
The implementation is an independent elementary proof of that published
generalization. It establishes only the stated ring-square universal property.
