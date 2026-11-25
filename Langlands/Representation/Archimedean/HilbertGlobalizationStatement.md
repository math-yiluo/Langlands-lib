# Hilbert globalization targets for algebraic GL modules

This module defines unproved propositions, in
`Langlands.Archimedean`, for Hilbert realization of irreducible admissible
algebraic modules for actual general linear groups. It imports the vocabulary
of [SmoothHilbert](SmoothHilbert.md). It does not construct a globalization
or prove any analytic theorem.

## Exact quantifiers and conclusion

`RealHilbertGlobalizationStatement.{uV}` quantifies over every `r : ℕ`, every
`V : Type uV`, its additive group and complex module structures, a representation
`ρ` of `Matrix.unitaryGroup (Fin (r + 1)) ℝ`, and an action `π` of the complexified
real matrix Lie algebra. It assumes precisely

- `IsRealGKModule (r + 1) ρ π`;
- `IsIrreducibleGKModule ρ π`;
- `IsAdmissibleGKModule ρ`.

`ComplexHilbertGlobalizationStatement.{uV}` has the same telescope with `ℂ`
in place of `ℝ` and the existing `IsComplexGKModule`. Its Lie algebra is
`ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ`, the complexification of the
underlying real Lie algebra, including all real directions in complex matrices.
The carrier universe `uV` is free, not specialized to `Type 0`.
`ArchimedeanHilbertGlobalizationStatement.{uV}` is their conjunction.
Every positive matrix size occurs as `r + 1`. No genericity, unitarity,
pairing, preselected globalization, or extra finite-dimensional hypothesis
is assumed.

Each conclusion existentially supplies `H : Type uV`, a `NormedAddCommGroup`,
an `InnerProductSpace ℂ H` with `CompleteSpace H`, a homomorphism
`R : GL_(r+1)(F) →* (H →L[ℂ] H)`, and a complex linear equivalence
`e : V ≃ₗ[ℂ] smoothHilbertKFinite F (r + 1) R` satisfying
`IsSmoothHilbertGlobalization`. Requiring the realization in the same universe
as the input permits lifted input carriers without restricting that input universe.

With `D = DerivativeSmoothVectors (matrixModel F (r + 1)) R`,
`R∞ = DerivativeSmoothVectors.representation`, and
`j = smoothHilbertGlobalizationMap F (r + 1) R e`, the conclusion explicitly gives:

- jointly continuous action `GL_(r+1)(F) × H → H`, topological irreducibility,
  and the existing compact admissibility for `unitaryCompact F (r + 1)`;
- a linear identification with **all** compact-finite vectors inside `D`,
  and `DenseRange j` for the genuine word-derivative topology of `D`;
- `j(ρ(k)v) = R∞(Unitary.toUnits k)(j(v))` for every compact group element;
- `j(π(1 ⊗ X)v) = DerivativeSmoothVectors.operator X (j(v))`
  for every real matrix direction `X`;
- `HasSmoothHilbertExponentialDerivatives`: for every `y : D` and every
  `L : D →L[ℂ] ℂ`, the real curve `t ↦ L(R∞(exp(tX))y)` has derivative
  `L(DerivativeSmoothVectors.operator X y)` at zero.

The last formula and Lie compatibility give directly

`(d/dt)|₀ L(R∞(exp(tX))j(v)) = L(j(π(1 ⊗ X)v))`

for every continuous complex linear functional on the smooth carrier, without
requiring it to be bounded in the Hilbert norm. The matrix exponential is the
actual `generalLinearRealExp`, whose underlying matrix is `NormedSpace.exp (t • X)`.
The operator is the genuine orbit derivative already constructed in the Library.

The Hilbert norm topology controls bounded operators, joint continuity, closed
invariant subspaces and compact admissibility on `H`. Density and the continuity
of `L` refer to the stronger topology on `D`: convergence in `H` of every genuine
word derivative. Neither the equivalence `e` nor `V` is assigned a norm topology.
No claim equates the inherited norm topology with the smooth topology.

## Original sources and derived formulation

Getz–Hahn, *An Introduction to Automorphic Representations* (2024), registered
source `getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`:
Section 4.4, printed pp.115–120 (PDF pp.130–135). Definition 4.4.6 and p.116
give the algebraic GK category. Proposition 4.4.7, Lemma 4.4.8 and the proof on
pp.117–118 give compact-finite smooth vectors and density, including density
in the smooth topology on p.118. Theorem 4.4.9 relates irreducibility of admissible
Hilbert representations to their GK modules. Definitions 4.4.11–12 and the
p.119 smooth Hilbert discussion specify the smooth Fréchet category;
Lemma 4.4.13 gives moderate growth. Theorem 4.4.14 and the discussion immediately
after it give the canonical globalization and comparison with Hilbert smooth
vectors.

The October 2026 errata, registered source `getz-hahn-2024-errata-2026-10`,
SHA256 `e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
p.1, correct both Section 4.4 points used here: continuity of the compact action
on finite-dimensional pieces, and compact-finite vectors in the p.120
comparison. The requested equivalence consequently targets compact-finite
vectors inside the smooth carrier, not the whole space of smooth vectors.

The statements are a derived Hilbert realization form of this framework, not
verbatim assertions of the cited book. A proof must realize every module under
the exact existing GK hypotheses on a complete Hilbert space and establish the
specified density, compact and derivative comparisons. In particular it must
supply any needed countability or finite-generation consequences of those
hypotheses, rather than silently add them as premises.

The smooth carrier is intended to fall in the smooth admissible Fréchet category
used by Aizenbud–Gourevitch, Definition 8.1.1, p.22, registered source
`aizenbud-gourevitch-2009-generalized-harish-chandra-descent-v7`, SHA256
`a789936fffe560b9295c666f420a3cf7c69a475192bace2e5c2c4c3d975d7dfd`.
The required comparison uses a finite real matrix Lie algebra basis to obtain
countably many generating word seminorms, completeness of the smooth topology,
smoothness and continuity of the transported action, compact admissibility and
irreducibility transfer, and the moderate-growth/canonical-globalization comparison
above. These are standard analytic proof obligations; they are not declared
proved by `DerivativeSmoothVectors` or `IsSmoothHilbertGlobalization`. The
scalar exponential derivative comparison is likewise requested as part of the
conclusion. Its coordinate formula uses the word `W ++ [X]`, as explained in
`SmoothHilbert.md`.

Once proved, these propositions are intended to combine with the separately
stated smooth Hilbert inverse-transpose pairing family and a dense restriction
argument to prove `ArchimedeanTransposePairingStatement`. This module neither
imports a restriction helper nor assumes that target. It uses no
global multiplicity-one or Rankin–Selberg argument. The Library proves
`RealHilbertGlobalizationStatement` as `realHilbertGlobalization` (module
`RealHilbertGlobalizationProof`); `ComplexHilbertGlobalizationStatement` is not proved in the
Library.
