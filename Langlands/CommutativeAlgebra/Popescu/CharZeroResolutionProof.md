# Proof of Stacks Lemma 10.3 (07FE) in characteristic zero

`Langlands.CommutativeAlgebra.Popescu.charZeroResolution` proves
`Langlands.CommutativeAlgebra.Popescu.CharZeroResolutionStatement.{u}`: let `k` be a field
of characteristic zero, `A` a finitely presented `k`-algebra, `f : A →ₐ[k] Λ` a map to a
Noetherian `k`-algebra, and `q` a prime of `Λ` minimal over `h_A = singularRadical k f`
such that `Λ_q` is a regular local ring. Then `CanBeResolved k f q`.

## The proof

The theorem applies `charZeroResolution_of`, from module `CharZeroResolutionAssembly`
(see `CharZeroResolutionAssembly.md` for the argument, which follows the source proof).
It discharges that theorem's eight hypotheses with these published Library proofs:

| Hypothesis | Source | Library proof |
| --- | --- | --- |
| `NilpotentLiftingStatement` | Proposition 5.3 (07CM) | `NilpotentLifting.nilpotentLifting` |
| `StrictlyStandardDesingularizationStatement` | Lemma 7.3 | `Desing.strictlyStandardDesingularization` |
| `StrictlyStandardSmoothStatement` | Lemma 3.7(d) | `strictlyStandardSmooth` |
| `DimZeroResolutionStatement` | Lemmas 9.3-9.4 | `dimZeroResolution` |
| `CharZeroFieldFactorizationStatement` | Algebra 07BV | `charZeroFieldFactorization` |
| `RegularSequenceFlatStatement` | Algebra 07DY | `regularSequenceFlat` |
| `RegularParameterChoiceStatement` | Lemma 10.2 (07FD) | `regularParameterChoice` |
| `StrictlyStandardRetractStatement` | Lemmas 3.1 and 3.7(e) | `strictlyStandardRetract` |

All names are in the namespace `Langlands.CommutativeAlgebra.Popescu`.

## Supporting modules

Four modules besides this one support the proof:

- `SmoothingAlgebra`: the algebra `B = A[x, z]/(xᵢⁿ − Σ zᵢⱼ aⱼ)` and its smoothness
  over `R = k[x₁, …, x_d]` after inverting each `aⱼ`.
- `LocalLifting`: Lemma 9.2, `canBeResolved_of_sequence`, which reduces resolution
  along a sequence `x₁, …, x_d` to the dimension-zero case.
- `ArtinianBottom`: the bottom condition of Lemma 9.2 for `R/(x)` and `Λ/(π)`, built
  from flatness (07DY), the field case in characteristic zero (07BV) and nilpotent
  lifting (07CM).
- `CharZeroResolutionAssembly`: `charZeroResolution_of`, which derives the target from
  the eight statements above.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 10.3 (Tag 07FE, printed pp. 24-25).
