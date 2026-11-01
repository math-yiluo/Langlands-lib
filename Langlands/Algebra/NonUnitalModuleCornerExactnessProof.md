# Exactness of the actual original-module corner functors

Worker 595 proves the two closed propositions in
`Langlands.Algebra.NonUnitalModuleCornerExactnessStatements`. The implementation uses
the original fixed-part subtype, its inherited additive group, the named
corner ring and the published original-action restriction functors.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The conventions at printed pages 5–7 / PDF pages 11–13, the unnumbered
I.3.1 proposition and proof at printed page 19 / PDF page 25, and A.VIII.1
at printed pages 265–266 / PDF pages 271–272 were read directly.
The registered supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF pages 1–2. Its I.3.2 corrections concern later induction
and quotient arguments. Both source files were checked against the hashes
above. No Renard-specific project errata note was present at the checked
project and Library locations.

The complete, unapplied theorem types are

```lean
Langlands.Algebra.nonUnitalModuleCornerExactness.{uA, uM} :
  Langlands.Algebra.NonUnitalModuleCornerExactnessStatement.{uA, uM}

Langlands.Algebra.nondegenerateModuleCornerExactness.{uA, uM} :
  Langlands.Algebra.NondegenerateModuleCornerExactnessStatement.{uA, uM}
```

They bind no additional hypotheses outside the published closed propositions.
The target Lean/Markdown pair and its import closure remain unchanged.

For an exact original triple, the published ambient range–kernel criterion
provides an original preimage of any fixed vector in the middle kernel.
The proof applies the published projection to that preimage. Intertwining
and the target vector's fixed-part membership show that its restricted image
is the required vector. Mathlib's element criterion for exact short complexes
of modules gives categorical exactness of the mapped triple.

Injectivity restricts to the fixed subtypes. Surjectivity follows by the same
projected-preimage argument. The published integer-unitization equivalence
identifies original categorical monomorphisms and epimorphisms with injective
and surjective module maps, respectively. These observations prove that the
actual corner functor preserves both classes. Together with arbitrary
triple preservation they give both full one-sided sequence tests in
`Langlands.Renard.SequenceExact`: each retains middle exactness, and the
left test retains monicity of the first map while the right test retains
epicity of the second. Neither test requires the other boundary condition.

For the nondegenerate category, the proof uses the published preservation
of homology by its actual inclusion into the ambient category. It maps an
exact triple through that inclusion and then through the ambient corner
functor. The same composite preserves monomorphisms and epimorphisms.
The selected abelian structure is exactly
`NondegenerateModuleCat.abelian A hA`.

The ambient theorem is an internal arbitrary-ring generalization of Renard's
argument; it assumes no idempotentedness or nondegeneracy. The nondegenerate
theorem retains the source's original modules under exactly `IsIdempotented A`.
Both use independent ring and carrier universes. Zero idempotents, zero rings,
trivial carriers and ambient zero actions are included. The comparison with
Renard's complex-linear module categories and I.3.2 remain separate.

Lean examples specialize each closed theorem to both unequal universe pairs
`(uA, uM) = (0, 1)` and `(1, 0)`. The proof uses exactly
`NonUnitalModuleCat.abelian A`, `NondegenerateModuleCat.abelian A hA`,
`Idempotent.Corner.ring e` and the inherited pointwise Hom addition.
Preservation certificates are conclusions of the proofs. They are not
assumptions on the ring, its original actions, or the functors.
