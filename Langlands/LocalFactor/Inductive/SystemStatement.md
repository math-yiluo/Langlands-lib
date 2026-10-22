# Induction of local constants in arbitrary degree

Worker 33 wrote this proposition definition for task `e534647a` (row 10 of the
local-factor coverage map). The declaration is
`Langlands.LocalFactor.Inductive.SystemInductionCorrectionStatement`. It is a
statement only: no proof is claimed and nothing is assumed as an axiom.

## Objects

Every object comes from Worker 20's common-closure local-constant interface:

- `Langlands.LocalFactor.CommonClosure`: finite intermediate extensions `E ⊆ L` of
  Mathlib's algebraic closure of `F` (`Extension F`) and their Weil subgroups
  `W_E ⊇ W_L` (`weilSubgroup`). It also supplies the continuous exact virtual
  groups `R(W_E)` (`Virtual`), the virtual dimension (`degree`), induction
  `Ind_{L/E}` (`induce`), additive characters and Haar measures for the
  canonical topology, and the trace character `ψ ∘ Tr_{L/E}` (`traceCharacter`).
- `Langlands.LocalFactor.NonabelianSystem`: unit-valued assignments
  `ε_E(x, ψ, μ)` (`Assignment`) and the system property `IsSystem`. That property
  bundles normalized reciprocity, additivity, Haar scaling, degree-zero
  induction with trace characters, and rank-one agreement with the abelian
  constants.

`[1_L]` is the class in `R(W_L)` of the Library's character line of the trivial
character of `W_L` (`ExactGrothendieckGroup.characterClass 1`).

## The statement

Let `ε` be a system for a reciprocity family `e`, that is, `IsSystem F e ε` holds.
Let `E ⊆ L` be finite extensions of `F`, `ψ` an additive character of `E`, `μ_E` and
`μ_L` Haar measures on `E` and `L`, and `x` any virtual representation of `W_L`, of
dimension `n ∈ ℤ`. Put

`λ = ε_E(Ind_{L/E}[1_L], ψ, μ_E) · ε_L([1_L], ψ ∘ Tr_{L/E}, μ_L)^{-1}`.

Then

`ε_E(Ind_{L/E} x, ψ, μ_E) = λ^n · ε_L(x, ψ ∘ Tr_{L/E}, μ_L)`.

The power is an integer power in `ℂ^×`.

## Provenance

Tate (3.4.1) and (3.4.8) assert only degree-zero inductivity:
`ε(Ind V_L, ψ) = ε(V_L, ψ ∘ Tr)` for virtual `V_L` of degree zero. In
`NonabelianSystem` this is the clause `InductionRelation` of `IsSystem`. The task
contract forbids inferring an arbitrary-degree identity from it without the
correction. This statement gives the corrected arbitrary-degree form. It is a
derived consequence of the system property. Apply `InductionRelation` to the
degree-zero class `x - n[1_L]` (with the given `μ_E` and `μ_L`, which
`InductionRelation` allows to be arbitrary) and use additivity (`AdditiveRelation`).
The correction factor `λ` is the constant usually written `λ(L/E, ψ)`. With
arbitrary Haar measures it also carries the measure normalization: both sides
scale in the same way under the Haar scaling law, so the identity holds for every
pair `μ_E`, `μ_L`.

The companion `Langlands.LocalFactor.Inductive.Statement`, submitted separately
for review, states the same
correction (`DegreeCorrectionStatement`) for every function that is inductive in
degree zero in Tate's (2.3.2) sense, on the extension-embedding model of
`Langlands.LocalFactor.Inductive.Definitions`. This module states it for the
actual local-constant systems of the common-closure interface, which is the
model the system specification uses.

## Sources

- `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`: J. Tate,
  *Number theoretic background*, Corvallis Part II (1979). PDF page = printed
  page + 9.
  - (2.3.2), printed pp.11–12 (PDF pp.20–21): inductive in degree zero.
  - (3.4.1), printed pp.14–15 (PDF pp.23–24): the system with `ψ ∘ Tr_{E/F}`.
  - (3.4.2)–(3.4.3), printed p.15 (PDF p.24): additivity and Haar scaling.
  - (3.4.8), printed p.15 (PDF p.24): degree-zero induction.
- `deligne-1973-local-constants`, SHA-256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`:
  P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*
  (1973), Theorem 4.1, printed p.535 (PDF p.35): existence and uniqueness of the
  local constants with degree-zero inductivity.

## Dependencies and status

The only project import is `Langlands.LocalFactor.NonabelianSystem` (Worker 20,
published in the Library), which imports `Langlands.LocalFactor.CommonClosure`. A development check in
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the module with no
errors or warnings. Inspection reports a definition returning `Prop`, with
universe parameters `uF uV` and only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Compilation does not establish the truth of the statement.
Independent semantic review is required.
