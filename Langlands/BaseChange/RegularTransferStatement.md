# Transfer of test functions with regular support

Module `Langlands.BaseChange.RegularTransferStatement`, namespace `Langlands.BaseChange`.
It states `RegularTransferStatement.{u, v} : Prop` (item 11 of the task). The statement is
not proved here.

## Source

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mém. SMF 124 (2011), source ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, I.2.5,
Proposition, printed p. 18 (PDF p. 26); HL prove it in I.2.6–I.2.8.

## Statement

For every nonarchimedean local field `F : Type u` of characteristic zero (`[Field F]
[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`), every
commutative `F`-algebra `E : Type v` with `[TopologicalSpace E] [IsTopologicalRing E]
[IsModuleTopology F E]`, every `σ : E ≃ₐ[F] E` and `l n : ℕ` with `IsCyclicAlgebra σ l`,
every Borel σ-algebra on `GL_n(F)` and on `GL_n(E)`, and all Haar measures `μF` on
`GL_n(F)` and `μE` on `GL_n(E)`:

- (1) for every `φ : SchwartzBruhat (GL_n(E))` with `IsSigmaRegularSupported σ l φ`, there
  is `f : SchwartzBruhat (GL_n(F))` with `IsRegularSupported f` and
  `AreConcordant σ l μF μE φ f`;
- (2) for every `f : SchwartzBruhat (GL_n(F))` with `IsRegularSupported f` and
  `VanishesOffNorms σ l μF f`, there is `φ : SchwartzBruhat (GL_n(E))` with
  `IsSigmaRegularSupported σ l φ` and `AreConcordant σ l μF μE φ f`.

`SchwartzBruhat X` is the Library's space of locally constant compactly supported complex
functions (`Langlands.HarmonicAnalysis.SchwartzBruhat`), HL's `C^∞_c(X)`; it is applied
to functions through its coercion. Since such functions are locally constant, the support
conditions are HL's "à support dans `G(F)_r`" and "à support dans `G(E)_{σ-r}`" (see the
Markdown of `Langlands.BaseChange.OrbitalIntegral`).

## Relation to HL's Proposition

**Characteristic zero.** The Library's `IsRegularSemisimple` asks for a separable
characteristic polynomial; this is HL's `G(F)'`. HL's regular elements, which define
`G(F)_r`, `G(E)_{σ-r}` and concordance, have a characteristic polynomial that is a product
of pairwise distinct irreducible polynomials, that is, squarefree (HL I.2.3, printed
p. 13, PDF p. 21). Over
a perfect field the two conditions agree (`PerfectField.separable_iff_squarefree`), and a
field of characteristic zero is perfect. Under `[CharZero F]` the support conditions,
`VanishesOffNorms` and `AreConcordant` are therefore HL's, and HL's Proposition applies
verbatim. In positive characteristic the separable notion is more restrictive, and the
statement is not asserted there.

**Hypothesis of (2).** HL assume `Λ^{G(F)}(f, γ) = 0` for every `γ` that is not a norm.
The statement assumes it only for regular semisimple `γ` (`VanishesOffNorms`). For `f`
supported in the regular set the two hypotheses agree: the orbit of a closed non-regular
`γ` consists of non-regular elements, on which `f` vanishes.

**Measures.** HL fix a Haar measure `dg` on `G(F)` and take for `dg_E` the product measure
`dg_{E₁}^r` on `G(E) = G(E₁)^r`, which is a Haar measure on `G(E)`. The statement
quantifies over all Haar measures `μF`, `μE`. Every Haar measure on `G(E)` is a positive
multiple of `dg_E`, and similarly on `G(F)`. Replacing `μE` by `c μE` (`c > 0`) multiplies
the compatible quotient measures on `G^σ_δ(F)\G(E)`, hence all σ-orbital integrals, by `c`,
and replacing `μF` by `c μF` does the same for the orbital integrals on `G(F)`. Rescaling
the function produced by the existential conclusion by the corresponding positive constant
restores concordance, and does not change the support conditions or `VanishesOffNorms`.
So the statement for all Haar measures is equivalent to HL's with their fixed measures.
The centralizer and quotient measures enter through `ConcordAt` and `VanishesOffNorms`,
which quantify over all of them; see the Markdown of `Langlands.BaseChange.OrbitalIntegral`.
These equivalences are mathematical remarks and are not formalized.

## Lean conventions

The left coset spaces carry the Borel σ-algebra through the local instances
`leftQuotientMeasurableSpace` (high priority) and `leftQuotient_borelSpace` of
`Langlands.BaseChange.OrbitalIntegral`, installed again in this module.

## Dependencies

`Langlands.BaseChange.OrbitalIntegral` (this task); through it Task 7402
(`Langlands.TraceFormula.TwistedOrbital`) and Task 7405 (`Langlands.BaseChange.Norm`:
`IsCyclicAlgebra`, `IsSigmaRegular`, `IsNorm`, `IsNormAssociated`); the Library's
`Langlands.HarmonicAnalysis.SchwartzBruhat`; Mathlib's `IsNonarchimedeanLocalField` and
`IsModuleTopology`.
