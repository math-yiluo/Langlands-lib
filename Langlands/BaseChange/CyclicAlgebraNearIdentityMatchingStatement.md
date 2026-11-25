# Matching of test functions near the identity for a cyclic algebra

Module `Langlands.BaseChange.CyclicAlgebraNearIdentityMatchingStatement`, namespace
`Langlands.BaseChange`. It states `CyclicAlgebraNearIdentityMatchingStatement.{u, v} : Prop`. The
statement is proved in `Langlands.BaseChange.CyclicAlgebraNearIdentityMatching`
(`cyclicAlgebraNearIdentityMatching`).

## Statement

For every nonarchimedean local field `F : Type u` of characteristic zero (`[Field F]
[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`), every
commutative ring `E : Type v` with `[Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
[IsModuleTopology F E]`, every `σ : E ≃ₐ[F] E` and `l n : ℕ` with `IsCyclicAlgebra σ l`, every
Borel σ-algebra on `GL_n(F)` and on `GL_n(E)`, and all Haar measures `μF` on `GL_n(F)` and `μE`
on `GL_n(E)`:

- there is `U ∈ nhds (1 : GeneralLinear n E)` such that every `φ : SchwartzBruhat (GL_n(E))` with
  `Function.support φ ⊆ U` has some `f : SchwartzBruhat (GL_n(F))` with
  `AreConcordant σ l μF μE φ f`;
- there is `V ∈ nhds (1 : GeneralLinear n F)` such that every `f : SchwartzBruhat (GL_n(F))` with
  `Function.support f ⊆ V` has some `φ : SchwartzBruhat (GL_n(E))` with
  `AreConcordant σ l μF μE φ f`.

It is `NearIdentityMatchingStatement` with `[CommRing E]` in place of `[Field E]`, that is, with the
hypotheses on `E` of `RegularTransferStatement`: `E` is a finite reduced `F`-algebra of dimension
`l` whose `σ`-fixed elements are those of `F`, a product of `r` copies of a cyclic field extension
`L / F` of degree `d`, `l = r d`. This is the local situation at a place of a global field that is
not inert in a global cyclic extension.

## Relation to the literature

Henniart–Lemaire define association, norms and concordance for a cyclic algebra (§I.2.1–§I.2.2,
pp. 10–12; §I.2.5, Définition, p. 17) and reduce the transfer of functions with regular support to
the case of a field (§I.2.6, p. 18). Arthur–Clozel treat the field case (Chapter 1, §3,
Proposition 3.1, p. 20) and indicate the extension to places that are not inert (Chapter 1, §5,
pp. 48–49). The statement here is the case of test functions supported near `1`.

## Lean conventions

The left coset spaces carry the Borel σ-algebra through the local instances
`leftQuotientMeasurableSpace` (high priority) and `leftQuotient_borelSpace` of
`Langlands.BaseChange.OrbitalIntegral`, installed again in this module, as in
`NearIdentityMatchingStatement` and `RegularTransferStatement`.

## Dependencies

`Langlands.BaseChange.OrbitalIntegral` (`AreConcordant`, `IsCyclicAlgebra` through
`Langlands.BaseChange.Norm`); `Langlands.HarmonicAnalysis.Basic` (`SchwartzBruhat`); Mathlib's
`IsNonarchimedeanLocalField` and `IsModuleTopology`.

## Literature

- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour GLₙ en
  caractéristique non nulle*, Mém. SMF 124 (2011), §I.2.1, pp. 10–11 (a cyclic algebra as
  `E₁^r`, the action of `σ`, the norms `N`, `N₁`, `N'¹`); §I.2.2, p. 12 (Lemme, association);
  §I.2.5, p. 17 (concordance) and p. 18 (Proposition); §I.2.6, p. 18 (reduction to a field).
- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula*, Annals of Mathematics Studies 120 (1989), Chapter 1, §3, Proposition 3.1, p. 20;
  §5, pp. 48–49.
