# σ-lifts are Shintani lifts

The module `Langlands.BaseChange.SigmaLiftCharacterIdentityStatement` states, as the
proposition `SigmaLiftCharacterIdentityStatement.{u, v, uV, uW}`, Henniart–Lemaire's
characterization of σ-lifts by an identity "à la Shintani" between character functions. The
statement is **not** proved here.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`. PDF page =
  printed page + 8. Cited as HL.
  - II.2.7, Définition, printed p. 67: `Π` is a σ-lift ("σ-relèvement") of `π` if there is
    a constant `c ≠ 0` with `Θ^A_Π(φ) = c Θ_π(f)` for every concordant pair `(φ, f)`.
  - II.2.9, Proposition, printed p. 69: `Π` is a σ-lift of `π` if and only if there is a
    constant `c ≠ 0`, "la même que celle de la définition de 2.7", with
    `Θ^A_Π(δ) = c Θ_π(γ)` for every pair of associated elements `(δ, γ)` with `γ` regular.
    HL note that the proof follows from their 2.5 (transfer for regular support) and the
    Weyl integration formula (2.10, 2.11).
  - II.2.9, Remarques (1) and (2), printed p. 70: reduction to the case of a field, and
    the constant `c(π, A)`.
- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula* (1989), source ID `arthur-clozel-1989-base-change`, Chapter 1, Definition 6.1,
  printed p. 51. Shintani's definition of the lift by `trace(Π(g) I_σ) = trace π(Ng)` for
  `g` with regular norm, with the Whittaker-normalized `I_σ` and constant `1`.

## Statement

`SigmaLiftCharacterIdentityStatement.{u, v, uV, uW}` quantifies over the following data:

- a field `F : Type u` with `[ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]`;
- a commutative `F`-algebra `E : Type v` with `[TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E]`;
- `σ : E ≃ₐ[F] E` and `l n : ℕ` with `IsCyclicAlgebra σ l` (module `Langlands.BaseChange.Norm`).

The topological instances on `GL_n(F)` come from the Library's
`LocalFieldTopology.generalLinear_t2Space`, `generalLinear_locallyCompactSpace` and
`generalLinear_totallyDisconnectedSpace` (`Langlands/Group/GL/LocalFieldTopology.lean`).
Those on `GL_n(E)` come from lemma 9 of `Langlands.BaseChange.TwistedCharacter`, using that
`E` is a finite `F`-module (the first component of `IsCyclicAlgebra`). All are introduced
with `haveI` inside the statement.

The claim is the following. Take any complex vector spaces `V : Type uV` and `W : Type uW`,
admissible irreducible representations `π : Representation ℂ (GL_n(F)) V` (proof `hπ`) and
`τ : Representation ℂ (GL_n(E)) W` (proof `hτ`), any `A : SigmaIntertwiner σ n τ` and any
`c : ℂ`. Then

`IsSigmaLift σ l π hπ τ hτ A c ↔ IsShintaniLift σ l π hπ τ hτ A c`.

Here `IsSigmaLift` (item 6 of `TwistedCharacter`) says that `c ≠ 0` and that
`Θ^A_τ(φ) = c Θ_π(f)` for all Haar measures and all test functions `φ` and `f` that
concord in the sense of `AreConcordant` (module `Langlands.BaseChange.OrbitalIntegral`). `IsShintaniLift` (item 5) says that
`c ≠ 0` and that for every `δ` associated with a regular semisimple `γ`, `Θ_π` has a value
`a` at `γ` and `Θ^A_τ` has the value `c * a` at `δ`. Since both sides carry the same `c`,
the statement contains HL's "la même que celle de la définition de 2.7". Taking `∃ c` on
both sides gives HL's form "Π is a σ-lift of π iff there is `c ≠ 0` with the Shintani
identity". HL's σ-stability of `Π` is implied by the existence of `A`. As in
`TwistedCharacter`, HL's `Π` is written `τ` in Lean.

HL's Proposition presupposes the character functions of II.2.8. `IsShintaniLift` instead
asserts the existence of the values at the points it uses. In the direction from σ-lift to
Shintani identity, the statement therefore also claims that these values exist.
`TwistedCharacterRegularValuesStatement` and the Library's
`HasRegularSemisimpleCharacterValues` are the corresponding existence statements. They are
not hypotheses here.

## The hypothesis `CharZero F`

Association, regularity and concordance are tested at `γ` with `IsRegularSemisimple γ`, the
Library's notion: the characteristic polynomial is separable (HL's `G(F)'`). This holds both
in `IsShintaniLift` and inside `AreConcordant`. HL's regular elements have a
squarefree characteristic polynomial (II.1.2, printed p. 56). The two agree over perfect
fields, in particular in characteristic zero (Mathlib's
`PerfectField.separable_iff_squarefree`). There both sides of the equivalence are exactly
HL's notions, and HL's Proposition applies verbatim. In positive characteristic the Lean
conditions would test fewer points than HL's, so the statement assumes `[CharZero F]`, as
`Langlands.BaseChange.RegularTransferStatement` does.

## Cyclic algebras

HL's Chapter II takes `E` to be a cyclic field extension of `F` in II.1. From II.2.1
(printed p. 61) it allows a cyclic `F`-algebra `E = E₁ × ⋯ × E_r`, and it treats that case
by reduction to the field `E₁` in II.2.8 (Remarque, printed p. 69) and II.2.9 (Remarque (1),
printed p. 70: if the Proposition holds when `E` is a field, it holds in general). The
statement is therefore made for every `E` with `IsCyclicAlgebra σ l`, the
characterization in `Langlands.BaseChange.Norm` of HL's cyclic algebras.
