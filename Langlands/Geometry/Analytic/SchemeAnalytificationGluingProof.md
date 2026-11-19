# Scheme analytification gluing and separatedness

`Langlands.Analytic.SchemeAnalytification.schemeAnalytificationGluing`
proves `SchemeAnalytificationGluingStatement.{u}` for every universe `u`.
The proof introduces the complete ultrametric nontrivially normed field
`K : Type u`, the scheme `X : Scheme.{u}`, and its locally finite type
structure morphism `f : X ⟶ Spec (CommRingCat.of K)`.

`OpenGluing.affineOpenGluing K f` supplies the first four conjuncts on the
published quotient `Space K f`. The underlying proof uses principal
localization to obtain open embeddings for affine restrictions, then uses
common affine refinements to prove the chart embeddings and the overlap
formula. In the affine case the top chart is surjective because each chart
maps into it, so its open embedding is a homeomorphism.

`schemeAnalytificationSeparated K X f` supplies the final conjunct
`IsSeparated f ↔ T2Space (Space K f)`. Its forward implication proves the
pairwise chart relations are closed by taking limits of seminorms. Its
reverse implication uses those closed relations and density to prove
uniqueness in the valuative criterion. The assembly applies both published
theorems to the same `K`, `X`, and `f` and constructs the five conjuncts in
the order of the target.

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean
Fields* (1990), proves the open gluing in steps (2)–(3) of Theorem 3.4.1
(printed pp. 63–64, PDF pp. 77–78) and the separatedness criterion in
Theorem 3.4.8(i) (printed p. 67, PDF p. 81). The published target expresses
these results for the Library's polynomial-locus quotient. The registered
source is `provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
with SHA-256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
