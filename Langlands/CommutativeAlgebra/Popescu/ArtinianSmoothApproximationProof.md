# Proof of Stacks Lemma 16.11.2 (07FH)

`artinianSmoothApproximation` proves
`Langlands.CommutativeAlgebra.Popescu.ArtinianSmoothApproximationStatement.{u}` for every universe
`u`. This is Stacks Project, *Smoothing Ring Maps*, Lemma 16.11.2 (Tag 07FH). It uses only the
standard axioms.

## Proof

The proof is one application of `SmoothApprox.artinianSmoothApproximation_of` (module
`SmoothApproxFinal`). That theorem derives the statement from six Library statements. Here each
hypothesis is filled by the published proof of the statement:

| Hypothesis | Statement | Published proof |
| --- | --- | --- |
| `ha` | `GeometricRegularityH1FiniteStatement` | `geometricRegularityH1Finite` |
| `hb` | `GeometricRegularityFlatStatement` (Stacks 07E6) | `GeometricRegularity.geometricRegularityFlat` |
| `hb2` | `RegularParameterExtensionStatement` | `regularParameterExtension` |
| `hc` | `ArtinianFlatSubalgebraStatement` (Stacks 07FG) | `artinianFlatSubalgebra` |
| `he` | `ArtinianUnitEnlargementStatement` | `Enlargement.artinianUnitEnlargement` |
| `hf` | `ArtinianEtaleCriterionStatement` | `EtaleCriterion.artinianEtaleCriterion` |

All names are in the namespace `Langlands.CommutativeAlgebra.Popescu`.

The mathematical argument is in `SmoothApproxFinal.md`, which also explains a gap in the source's
proof and its repair: the elements `λ_j ∈ Λ` used there need not exist. The helper lemmas are in
`SmoothApproxTools`.
