# Full finite-place matching for a cyclic algebra

Module `Langlands.BaseChange.CyclicAlgebraFullMatchingStatement`, namespace
`Langlands.BaseChange`. It states `CyclicAlgebraFullMatchingStatement.{u, v} : Prop`. It is not
proved; `Langlands.BaseChange.CyclicAlgebraFullMatching` proves that it follows from
`FinitePlaceFullMatchingStatement.{u, v}`
(`cyclicAlgebraFullMatching_of_finitePlaceFullMatching`).

## Statement

For every nonarchimedean local field `F : Type u` of characteristic zero (`[Field F]
[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`), every
commutative ring `E : Type v` with `[Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
[IsModuleTopology F E]`, every `σ : E ≃ₐ[F] E` and `l n : ℕ` with `IsCyclicAlgebra σ l`, every
Borel σ-algebra on `GL_n(F)` and on `GL_n(E)`, and all Haar measures `μF` on `GL_n(F)` and `μE`
on `GL_n(E)`:

- every `φ : SchwartzBruhat (GL_n(E))` has some `f : SchwartzBruhat (GL_n(F))` with
  `AreConcordant σ l μF μE φ f`;
- every `f : SchwartzBruhat (GL_n(F))` with `VanishesOffNorms σ l μF f` has some
  `φ : SchwartzBruhat (GL_n(E))` with `AreConcordant σ l μF μE φ f`.

It is `FinitePlaceFullMatchingStatement` with `[CommRing E]` in place of `[Field E]`, with the
hypotheses on `E` of `RegularTransferStatement`.

## Relation to the literature

Arthur–Clozel, Chapter 1, §3, Proposition 3.1 (p. 20) for `E` a field; for a place that is not
inert, Chapter 1, §5 (pp. 48–49) reduces the orbital integrals of tensors to the field `E₁`.
Henniart–Lemaire, §I.2.6 (p. 18) make the same reduction for functions with regular support.

## Lean conventions

As in `CyclicAlgebraNearIdentityMatchingStatement`: the left coset spaces carry the Borel
σ-algebra through the local instances of `Langlands.BaseChange.OrbitalIntegral`.

## Dependencies

`Langlands.BaseChange.OrbitalIntegral` (`AreConcordant`, `VanishesOffNorms`, `IsCyclicAlgebra`);
`Langlands.HarmonicAnalysis.Basic` (`SchwartzBruhat`); Mathlib's `IsNonarchimedeanLocalField` and
`IsModuleTopology`.

## Literature

- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula*, Annals of Mathematics Studies 120 (1989), Chapter 1, §3, Proposition 3.1, p. 20; §5,
  pp. 48–49.
- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour GLₙ en
  caractéristique non nulle*, Mém. SMF 124 (2011), §I.2.5, p. 17 (concordance); §I.2.6, p. 18.
