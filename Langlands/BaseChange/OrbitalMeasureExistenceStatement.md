# Existence of the measures entering concordance

Module `Langlands.BaseChange.OrbitalMeasureExistenceStatement`, namespace
`Langlands.BaseChange`. It states `OrbitalMeasureExistenceStatement.{u, v} : Prop`
(item 10 of the task). The statement is not proved here.

## Source

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mém. SMF 124 (2011), source ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
I.2.4, printed pp. 14–15 (PDF pp. 22–23), and I.2.5, printed p. 17 (PDF p. 25). HL
choose an invariant quotient measure `d̄g_γ` on `G_γ(F)\G(F)` and `d̄g^σ_δ` on
`G^σ_δ(F)\G(E)`, observing that `G_γ(F)` and `G^σ_δ(F)` are unimodular (p. 15, citing
their reference [57, 4.8.6], and the inner-form argument). For closed `γ` they write these
quotient measures as `dg/dg_γ` and `dg_E/dg^σ_δ` with associated Haar measures (p. 17).
The present statement records, for regular semisimple `γ`, the existence of these
measures in the form used by `Langlands.BaseChange.OrbitalIntegral`.

## Statement

For every nonarchimedean local field `F : Type u` (`[Field F] [ValuativeRel F]
[TopologicalSpace F] [IsNonarchimedeanLocalField F]`), every commutative `F`-algebra
`E : Type v` with `[TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]`,
every `σ : E ≃ₐ[F] E` and `l n : ℕ` with `IsCyclicAlgebra σ l`, every Borel σ-algebra on
`GL_n(F)` and on `GL_n(E)`, and all Haar measures `μF` on `GL_n(F)` and `μE` on `GL_n(E)`:

- (a) for every `γ : GL_n(F)` with `IsRegularSemisimple γ`, there is a measure on
  `glCentralizer γ` that is `IsHaarMeasure` and `IsMulRightInvariant`; and for every
  such right Haar measure `μγ` there is a measure `νγ` on `LeftQuotient (glCentralizer γ)`
  with `QuotientIntegration.IsCompatible (glCentralizer γ) μF μγ νγ`;
- (b) for all `δ : GL_n(E)` and `γ : GL_n(F)` with `IsNormAssociated σ l δ γ` and
  `IsRegularSemisimple γ`, and every right Haar measure `μγ` on `glCentralizer γ`, there
  is a right Haar measure `μδ` on `sigmaCentralizer σ n δ` with
  `IsAssociatedMeasure σ l δ γ μδ μγ`, together with a measure `νδ` on
  `LeftQuotient (sigmaCentralizer σ n δ)` with
  `IsCompatible (sigmaCentralizer σ n δ) μE μδ νδ`.

The statement makes the universal quantifiers over centralizer and quotient measures in
`ConcordAt` and `VanishesOffNorms` non-vacuous.

## Lean conventions

The instance binders `IsHaarMeasure` and `IsMulRightInvariant` of `μδ` in (b) are bound
by anonymous existentials `∃ (_ : μδ.IsHaarMeasure) (_ : μδ.IsMulRightInvariant), …`, so
that they are available as instances to `IsCompatible`, which requires
`[IsMulRightInvariant μδ]`. In (a) the existence of a right Haar measure is stated as a
conjunction `μγ.IsHaarMeasure ∧ μγ.IsMulRightInvariant`. The left coset spaces carry the
Borel σ-algebra through the local instances `leftQuotientMeasurableSpace` (high priority)
and `leftQuotient_borelSpace` of `Langlands.BaseChange.OrbitalIntegral`, installed again
in this module; see that module's Markdown. The σ-algebras on `GL_n(F)` and `GL_n(E)` are
universally quantified Borel σ-algebras.

## Mathematical remarks (not formalized)

Part (a): `G_γ(F)` is the group of units of the commutative `F`-algebra `F[γ]`, a closed
subgroup of `GL_n(F)`, hence locally compact; it is abelian, so its Haar measures are
right invariant. Both `GL_n(F)` and `G_γ(F)` are unimodular, so Weil's theorem gives a
quotient measure compatible with any pair of Haar measures. Part (b): when `γ` is regular
and `x⁻¹ N(δ) x = γ`, conjugation by `x` identifies `G^σ_δ(F)` with `G_γ(F)` (see the
Markdown of `Langlands.BaseChange.OrbitalIntegral`), so the image of `μγ` transported back
is a right Haar measure on `G^σ_δ(F)` associated with `μγ`, and Weil's theorem again gives
the quotient measure. These arguments are not formalized here.

## Dependencies

`Langlands.BaseChange.OrbitalIntegral` (this task); through it Task 7402
(`Langlands.TraceFormula.TwistedOrbital`) and Task 7405 (`Langlands.BaseChange.Norm`:
`IsCyclicAlgebra`, `IsNormAssociated`); the Library's `QuotientIntegration.IsCompatible`,
`LeftQuotient` and `JacquetLanglands.IsRegularSemisimple`; Mathlib's
`IsNonarchimedeanLocalField` (`Mathlib.NumberTheory.LocalField.Basic`) and
`IsModuleTopology`.
