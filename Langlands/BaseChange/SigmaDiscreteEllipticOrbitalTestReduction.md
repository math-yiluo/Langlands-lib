# σ-elliptic orbital test functions for σ-discrete series: a reduction

The module `Langlands.BaseChange.SigmaDiscreteEllipticOrbitalTestReduction` proves that
`SigmaDiscreteEllipticOrbitalTestStatement` follows from two statements: the existence of a test
function with nonzero twisted trace at a σ-discrete series that kills the twisted traces of the
irreducible representations properly induced from σ-stable representations, and the vanishing
off the σ-elliptic set of the σ-orbital integrals of every such function. This splits
Henniart–Lemaire's and Arthur–Clozel's argument into its spectral half (pseudo-coefficients and
their vanishing on induced representations) and its geometric half (descent).

## Statement

`SigmaDiscreteEllipticOrbitalTestReductionStatement.{u, v, uW}` is the implication

`SigmaDiscreteProperInducedVanishingTestStatement.{u, v, uW} →
ProperInducedVanishingOrbitalStatement.{u, v, uW} →
SigmaDiscreteEllipticOrbitalTestStatement.{u, v, uW}`

with the same universe parameters for the field `F`, the cyclic extension `E` and the
representation spaces in the premises and the conclusion. The three propositions are in the
Library:

- `SigmaDiscreteProperInducedVanishingTestStatement` (module
  `Langlands.BaseChange.SigmaDiscreteProperInducedVanishingTestStatement`): for a nonarchimedean
  local field `F` of characteristic zero, a field `E` that is a cyclic `F`-algebra of group `⟨σ⟩`
  of order `l`, a σ-discrete series `τ` of `GL_{r+1}(E)` on `W : Type uW`, an isomorphism `A` of
  `τ` onto `τ^σ` and a Haar measure `μ`, some Schwartz–Bruhat `φ` has `tr(τ(φ) ∘ A) ≠ 0` and
  twisted trace `0` at every irreducible `Ind_B(Ξ)` (unnormalized smooth induction from a proper
  standard upper block parabolic) of an irreducible admissible σ-stable `Ξ` on a carrier in
  `Type uW`, for every intertwiner `A'` (Henniart–Lemaire 2011, II.5.13, Remarque, and II.5.14,
  Proposition 2 (1)).
- `ProperInducedVanishingOrbitalStatement` (module
  `Langlands.BaseChange.ProperInducedVanishingOrbitalStatement`): in the same setting, every
  Schwartz–Bruhat `φ` with this vanishing of induced twisted traces satisfies
  `SigmaOrbitalIntegralsVanishOffElliptic σ l μ ⇑φ` (Arthur–Clozel 1989, Chapter 1,
  Lemma 2.12 (ii) with the descent argument of Proposition 2.7; Henniart–Lemaire 2011, II.5.14,
  proof of Proposition 2 (2)).
- `SigmaDiscreteEllipticOrbitalTestStatement` (module
  `Langlands.BaseChange.SigmaDiscreteEllipticOrbitalTestStatement`): in the setting of the first
  statement, some Schwartz–Bruhat `φ` satisfies `SigmaOrbitalIntegralsVanishOffElliptic σ l μ ⇑φ`
  and `tr(τ(φ) ∘ A) ≠ 0`.

The vanishing condition on induced twisted traces is the same expression in the first two
statements, and it is clause (b) of the Library's
`TwistedCuspidalPseudoCoefficientExistenceStatement` at `n = r + 1`.

The theorem `sigmaDiscreteEllipticOrbitalTestReduction` proves the implication.

## Proof

Fix `F`, `E`, `σ`, `l`, `r`, `hE`, a σ-discrete series `τ` with admissibility proof `hτ`, an
intertwiner `A` and a Haar measure `μ`. The first statement, applied to these data, gives `φ`
with `tr(τ(φ) ∘ A) ≠ 0` and the vanishing of induced twisted traces. The second statement,
applied to `F`, `E`, `σ`, `l`, `r`, `hE`, `μ` and `φ`, turns that vanishing into
`SigmaOrbitalIntegralsVanishOffElliptic σ l μ ⇑φ`. The pair of the two properties is the
conclusion. The instance arguments (`Module.Finite F E`, the topology and the Borel σ-algebra
on `GL_{r+1}(E)`) are built from `hE` in the same way in the three statements, so the terms
match without conversion.

## Sources

- G. Henniart, B. Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011): II.5.13, Proposition, its proof and Remarque
  (printed pp. 113–114); II.5.14, Proposition 2 and its proof (printed pp. 115–117). HL deduce
  Proposition 2 (2) from Proposition 2 (1) by contradiction through descent, which is the
  composition carried out here.
- J. Arthur, L. Clozel, *Simple algebras, base change, and the advanced theory of the trace
  formula*, Ann. of Math. Stud. 120 (1989): Chapter 1, Proposition 2.7 (printed pp. 15–17),
  Corollary 2.10 (printed p. 18) and Lemma 2.12 with its proof (printed p. 19).
