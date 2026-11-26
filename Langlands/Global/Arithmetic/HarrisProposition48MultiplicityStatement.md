# Harris's Proposition 4.8 with Theorem 1.2 with multiplicity as input

Several published statements of the induction for Harris (1998), Proposition 4.8, take
the published `Harris1998Theorem12CuspidalStatement` (Harris's Theorem 1.2, multiplicity
one, with purity) as an input. Beside each one, this module states the version that
takes Harris's Theorem 1.2 with multiplicity in Henniart's form,
`Harris1998Theorem12CuspidalMultiplicityStatement` (module
`Langlands/Galois/Harris1998MultiplicityStatement`), in its place. The published statements
are unchanged. Everything here is a proposition definition, except the two implications
between the conclusions at the end of the next section.

## Why the problems carry two more clauses

The new premise is stated for base fields `E = E₀ K₀` with `[E₀ : ℚ]` even, and for
cuspidal classes of regular highest weight with a supercuspidal component at a split
place. These are hypotheses added to Henniart's theorem of 2001, §5.5, which assumes a
regular algebraic infinitesimal character and a discrete series component. Even real
degree holds over the fields of Henniart's construction, which all contain the real
quadratic field `R` of his §5.1 (Henniart 2001, §§5.1, 5.7–5.11). Regular highest weight
needs an additional choice: the infinity type of the inducing Hecke character is chosen
with exponents at distance at least two (the printed Proposition 4.8 allows more general
archimedean types, see Harris's Remark, printed p. 202). The weights of the induced
classes are those of the inducing character, up to a common shift. So the new
statements ask the problems of the induction to satisfy `Proposition48Problem.IsSpaced`
(module `HarrisProposition48SpacedData`): even real degree of the base field, and weights
of the inducing character at distance at least two. The data must satisfy
`IsProposition48SpacedDatum`. These clauses pass to the Mackey children and to the
parity-corrected problems (`IsSpaced.of_auxiliaryMackeyChild`,
`IsSpaced.withCorrectedCharacter`, module `HarrisProposition48SpacedInheritance`). They hold
for the datum built in Henniart's globalization (`henniartHarrisDatumSpaced`, module
`HenniartHarrisDatumSpacedProof`).

## The conclusions

- `Proposition48SpacedStatement`: the published `Proposition48Statement` with
  `Harris.IsProposition48SpacedDatum` (the published datum, even real degree, weights at
  distance at least two) in place of `IsProposition48Datum`.
- `IsProposition48ExactStabilizerSpacedDatum` and `Proposition48ExactStabilizerSpacedStatement`:
  the same for the exact-stabilizer datum `IsProposition48ExactStabilizerDatum` and the
  published `Proposition48ExactStabilizerStatement`.
- Proved: `proposition48SpacedStatement_of_proposition48Statement` (the published
  Proposition 4.8 implies its spaced form, since a spaced datum is a datum) and
  `proposition48ExactStabilizerSpacedStatement_of_proposition48SpacedStatement` (as the
  published `proposition48ExactStabilizerStatement_of_proposition48Statement`, through the
  published `IsProposition48ExactStabilizerDatum.isProposition48Datum`).

## The new statements, beside the published ones

| Published statement | New statement |
| --- | --- |
| `Proposition48ReductionStatement` | `Proposition48MultiplicityReductionStatement` |
| `Proposition48ReductionTCStatement` | `Proposition48MultiplicityReductionTCStatement` |
| `Proposition48PrimeBranchStatement` | `Proposition48MultiplicityPrimeBranchStatement` |
| `Proposition48PrimeBranchTCStatement` | `Proposition48MultiplicityPrimeBranchTCStatement` |
| `Proposition48SingletonBranchStatement` | `Proposition48MultiplicitySingletonBranchStatement` |
| `Proposition48SingletonBranchTCStatement` | `Proposition48MultiplicitySingletonBranchTCStatement` |
| `Proposition48SingletonDescentSelectionTCStatement` | `Proposition48MultiplicitySingletonDescentSelectionTCStatement` |
| `Proposition48ExactStabilizerReductionStatement` | `Proposition48ExactStabilizerMultiplicityReductionStatement` |
| `Proposition48ExactStabilizerReductionTCStatement` | `Proposition48ExactStabilizerMultiplicityReductionTCStatement` |
| `Proposition48ExactStabilizerPrimeBranchStatement` | `Proposition48ExactStabilizerMultiplicityPrimeBranchStatement` |
| `Proposition48ExactStabilizerPrimeBranchTCStatement` | `Proposition48ExactStabilizerMultiplicityPrimeBranchTCStatement` |
| `Proposition48ExactStabilizerSingletonBranchStatement` | `Proposition48ExactStabilizerMultiplicitySingletonBranchStatement` |
| `Proposition48ExactStabilizerSingletonBranchTCStatement` | `Proposition48ExactStabilizerMultiplicitySingletonBranchTCStatement` |
| `Proposition48ExactStabilizerRestrictedReductionStatement` | `Proposition48ExactStabilizerRestrictedMultiplicityReductionStatement` |
| `Proposition48ExactStabilizerRestrictedReductionTCStatement` | `Proposition48ExactStabilizerRestrictedMultiplicityReductionTCStatement` |
| `Proposition48ExactStabilizerRestrictedSingletonBranchStatement` | `Proposition48ExactStabilizerRestrictedMultiplicitySingletonBranchStatement` |
| `Proposition48ExactStabilizerRestrictedSingletonBranchTCStatement` | `Proposition48ExactStabilizerRestrictedMultiplicitySingletonBranchTCStatement` |

All are in namespace `Langlands.Global.Harris`.

### Branch statements

Each new branch statement (prime, singleton, exact-stabilizer prime and singleton,
restricted singleton, with their totally complex forms) is the published one with two
changes:

- the premise `Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV}` is replaced by
  `Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV}`;
- after the validity hypothesis on the problem `Q` (`Q.IsAuxiliaryValid` or
  `Q.IsAuxiliaryExactStabilizerValid`) the hypothesis `Q.IsSpaced` is added.

The other premises, the children and the conclusion are those of the published statement.

### The descent selection

`Proposition48MultiplicitySingletonDescentSelectionTCStatement` is the published
`Proposition48SingletonDescentSelectionTCStatement` with the same replacement of the
premise, the hypothesis `Q.IsSpaced` and the hypothesis `1 ≤ r` on the rank `r + 1` of
`S`. Theorem 1.2 with multiplicity excludes rank one, and the descent step is taken only
at Mackey steps, where the rank `[E' : E]` exceeds one. In the hypothesis on the cyclic
descents `c` of `S`, regular highest weight (`c.HasRegularHighestWeight`, module
`Langlands/Automorphic/RegularHighestWeight`) replaces regular algebraic type. It implies
regular algebraic type, so the hypothesis is stronger and the statement is weaker. In the
descent step the theorem with multiplicity is applied to a conjugate self-dual twist of a
descent by a finite-order character (Harris 1998, proof of Lemma 1.6; Henniart 2001,
§§5.9–5.10). The base fields of the descent step are CM fields, hence totally complex, and
a finite-order character is trivial on the connected group `ℂ^×` at each complex place.
Such a twist therefore leaves the archimedean components unchanged, and the hypothesis
gives the twist regular highest weight. This module proves none of this; it only states
the descent step.

### Reduction statements

`Proposition48MultiplicityReductionStatement` changes three of the fourteen inputs of the
published `Proposition48ReductionStatement`:

- input 5, `Proposition48PrimeBranchStatement`, becomes
  `Proposition48MultiplicityPrimeBranchStatement`;
- input 6, `Proposition48SingletonBranchStatement`, becomes
  `Proposition48MultiplicitySingletonBranchStatement`;
- input 7, `Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV}`, becomes
  `Harris1998Theorem12CuspidalMultiplicityStatement.{0, uV, uV}`.

Inputs 1–4 and 8–14 (`Proposition48AuxiliaryRankOneStatement`,
`Proposition48AuxiliaryParityNormalizationStatement`,
`Proposition48AuxiliaryParityUntwistStatement`, `Proposition48MackeyStepStatement`,
`HarrisSupercuspidalLocalComparisonStatement`, `CuspidalSpectralRigidityStatement`,
`Proposition48IsobaricInvarianceStatement`, `CyclicRegularInductionStatement`,
`CyclicRegularOrbitLiftStatement`, `CyclicStableDescentStatement`,
`CyclicWeakInductionSupercuspidalStatement`) are unchanged. The conclusion
`Proposition48Statement` becomes `Proposition48SpacedStatement`. The totally complex form
`Proposition48MultiplicityReductionTCStatement` changes inputs 5, 6 and 7 of
`Proposition48ReductionTCStatement` in the same way.

The exact-stabilizer reductions (with twenty-two inputs) change, in the same way, the two
branch inputs (prime and singleton, or restricted singleton) and the Theorem 1.2 input. The
conclusion `Proposition48ExactStabilizerStatement` becomes
`Proposition48ExactStabilizerSpacedStatement`.

## Sources

- M. Harris, *The local Langlands conjecture for `GL(n)` over a `p`-adic field, `n < p`*,
  Invent. Math. 134 (1998), Lemma 1.6 and its proof (printed pp. 188–189), Theorem 1.2
  (printed p. 185), Proposition 4.8, its proof and the Remark in the proof (printed
  pp. 201–203). Registered `harris-1998-local-langlands`, SHA256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
- G. Henniart, *Sur la conjecture de Langlands locale pour `GL_n`*, J. Théor. Nombres
  Bordeaux 13 (2001), §5.1 (printed p. 177), §5.5 (printed pp. 178–179) and §§5.7–5.12
  (printed pp. 179–182).
  Registered `henniart-2001-langlands-locale-gln-jtnb`, SHA256
  `c9db009ee2f2e561d834b9e1ef07a8b27ff40d0edd19546d3351f38f39b2dac5`.
