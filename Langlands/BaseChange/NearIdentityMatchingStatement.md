# Matching of test functions near the identity for cyclic base change

Module `Langlands.BaseChange.NearIdentityMatchingStatement`, namespace `Langlands.BaseChange`.
It states `NearIdentityMatchingStatement.{u, v} : Prop`. The statement is proved in
`Langlands.BaseChange.NearIdentityMatching` (`nearIdentityMatching`).

## Statement

For every nonarchimedean local field `F : Type u` of characteristic zero (`[Field F]
[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`), every field
`E : Type v` with `[Algebra F E] [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]`,
every `σ : E ≃ₐ[F] E` and `l n : ℕ` with `IsCyclicAlgebra σ l`, every Borel σ-algebra on `GL_n(F)`
and on `GL_n(E)`, and all Haar measures `μF` on `GL_n(F)` and `μE` on `GL_n(E)`:

- there is `U ∈ nhds (1 : GeneralLinear n E)` such that every `φ : SchwartzBruhat (GL_n(E))` with
  `Function.support φ ⊆ U` has some `f : SchwartzBruhat (GL_n(F))` with
  `AreConcordant σ l μF μE φ f`;
- there is `V ∈ nhds (1 : GeneralLinear n F)` such that every `f : SchwartzBruhat (GL_n(F))` with
  `Function.support f ⊆ V` has some `φ : SchwartzBruhat (GL_n(E))` with
  `AreConcordant σ l μF μE φ f`.

The hypotheses are those of `FinitePlaceFullMatchingStatement`, with `E` a field (so `E / F` is a
cyclic field extension of degree `l`).

## Relation to the literature

This is the case of Arthur–Clozel, Chapter 1, Proposition 3.1 (p. 20), for test functions supported
near `1`: there (i) asserts that every `φ ∈ C_c^∞(G(E))` has an `f` whose orbital integrals vanish
off the norms and equal the σ-orbital integrals of `φ` at associated regular elements, and (ii) the
converse for `f` satisfying the vanishing condition. Near `1` no vanishing hypothesis is needed in
the second direction: a small enough neighbourhood of `1` in `GL_n(F)` consists of `l`-th powers,
hence of norms (Henniart–Lemaire, II.6.7, p. 123; `normNeighbourhood`), and the transferred
functions concord in the sense of Henniart–Lemaire, I.2.5 (p. 17; `AreConcordant`), which
includes the vanishing at regular semisimple non-norms (`VanishesOffNorms`). Arthur and Clozel prove
the proposition locally on the space of classes (Lemma 3.4, pp. 22–25); the case of a neighbourhood
of `1` is the case `δ₀ = 1` of their Lemma 3.4, where the σ-centralizer of `δ₀` is `G(F)` itself.

## Lean conventions

The left coset spaces carry the Borel σ-algebra through the local instances
`leftQuotientMeasurableSpace` (high priority) and `leftQuotient_borelSpace` of
`Langlands.BaseChange.OrbitalIntegral`, installed again in this module, as in
`RegularTransferStatement`.

## Dependencies

`Langlands.BaseChange.OrbitalIntegral` (`AreConcordant`, `IsCyclicAlgebra` through
`Langlands.BaseChange.Norm`); `Langlands.HarmonicAnalysis.SchwartzBruhat`; Mathlib's
`IsNonarchimedeanLocalField` and `IsModuleTopology`.

## Literature

- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula*, Annals of Mathematics Studies 120 (1989), Chapter 1, §3, Proposition 3.1, p. 20, and
  Lemma 3.4 with its proof, pp. 22–25.
- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour GLₙ en
  caractéristique non nulle*, Mém. SMF 124 (2011), §I.2.5, p. 17 (concordance); §II.6.7,
  p. 123 (the norm is open near `1`).

## Source and licence

No text of the `riemann-hypothesis` repository: the statement is the Library's own,
in the vocabulary of `RegularTransferStatement` and `FinitePlaceFullMatchingStatement`.
Its content corresponds to the source's `UpperTheory.ConvolutionTheory.Loc.nearDown` and
`…Loc.nearUp`, stated there with the source's own norms, balls of the value group of `E`, and
integrals against chosen normalizing functions.
