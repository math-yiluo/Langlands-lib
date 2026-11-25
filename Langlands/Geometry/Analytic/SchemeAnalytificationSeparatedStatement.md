# Statement: separatedness and Hausdorff scheme analytification

`Langlands.Analytic.SchemeAnalytification.SchemeAnalytificationSeparatedStatement`
states exactly the fifth clause of the published
`SchemeAnalytificationGluingStatement`, as a separate proof target. It retains
all the original quantifiers and hypotheses, in every universe: `K : Type u`
is a complete ultrametric nontrivially normed field, `X : Scheme.{u}`, and
`f : X ⟶ Spec (CommRingCat.of K)` is locally of finite type. The assertion is
`IsSeparated f ↔ T2Space (Space K f)` for the actual published quotient space.
It assumes neither quasi-compactness nor affineness, reducedness, or nonemptiness
of `X`.

The source is Berkovich, *Spectral Theory and Analytic Geometry over
Non-Archimedean Fields* (1990), Theorem 3.4.8(i), printed p.67/PDF p.81.
Section 3.4 begins on printed p.63/PDF p.77 with schemes locally of finite type
over a non-Archimedean field with nontrivial valuation. The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
Theorem 3.4.8(i) is stated for Berkovich's analytification. Its expression here
for the Library's glued polynomial-locus model is the same derived formulation
already used in the published gluing statement.

This module supplies no proof of the separatedness criterion;
`SchemeAnalytificationSeparatedProof` proves it as
`schemeAnalytificationSeparated`, and `SchemeAnalytificationGluingProof` uses
that proof for the fifth clause of the gluing statement. The supporting
theorem `separatedStatement_of_gluingStatement` only projects that clause from
a supplied proof of the full gluing statement. Separating this target does not
weaken or replace the original gluing target.
