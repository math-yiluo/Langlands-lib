# Finite Galois splitting of every actual field torus

Authors: Worker 1337 and Worker 27.

`Langlands.GroupScheme.torusFiniteGaloisSplitting` proves exactly
`Langlands.GroupScheme.TorusFiniteGaloisSplittingStatement.{u}`, imported
unchanged from `Langlands.GroupScheme.Torus.FiniteGaloisSplittingStatement`.
The universe `u` is arbitrary. For every field `k : Type u` and every actual
group scheme `T` over `Spec k` with the existing `IsTorus T`, it produces
a field `K : Type u`, a field structure and a `k`-algebra structure, with
`FiniteDimensional k K`, `IsGalois k K`, and an actual splitting of the
base-changed group scheme in the sense of `IsSplitTorus`.

The only premise about `T` is `IsTorus T`: its initial splitting extension
can be infinite, transcendental or inseparable. Affineness, finite type,
separable splitting and finite splitting are not additional premises.
There is no perfectness, infinitude, characteristic or positive-rank
restriction. The empty finite index type, hence rank zero, is included.

## Implemented proof

The two helper theorems are in
`Langlands.GroupScheme.SplittingAssembly`. They separate the geometric
assembly from its supplied coalgebra argument.

`finiteGaloisSplitting_of_sepClosedSplitting_of_finiteStage` first records
the assembly with two explicit inputs: splitting over separably closed
fields, and descent of a separable-closure splitting to a finite separable
extension for a group scheme with quasi-compact and quasi-separated
structure morphism. For an original torus, the published geometry lemmas
`IsTorus.quasiCompact` and `IsTorus.quasiSeparated` give these two properties.
`IsTorus.baseChange_of_isAlgebraic` makes its base change to
`SeparableClosure k` a torus. The first input splits that torus; the
second produces a finite separable splitting field `L`. The published
`IsSplitTorus.exists_finiteGalois_of_finiteSeparable` enlarges `L` to a
finite Galois extension while preserving the actual group-scheme splitting.

`finiteGaloisSplitting_of_groupLikeSpanningDescent` supplies both inputs
from proved Library interfaces and one explicit coalgebra descent input.
For separably closed splitting it applies
`SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites`. That published
theorem first obtains affineness of the torus by field-extension descent,
forms its actual coordinate Hopf algebra, and transports the original
splitting to group-like spanning after scalar extension. Coalgebra descent
then gives group-like spanning over the separably closed field.
`IsTorus.isSplitTorus_of_groupLike_span` turns this into an isomorphism
with a finite split torus. The finite-stage input is the published
`IsSplitTorus.exists_finiteSeparable_of_separableClosure`. Its proof
factors the splitting map through a finite intermediate field and reflects
the group laws and invertibility along faithfully flat pullback.

Finally, `torusFiniteGaloisSplitting` applies this second helper to the
published unconditional theorem
`Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning.{u,u,u}`.
Its three independent universes are specialized to the common universe of
the torus problem. This discharges the coalgebra descent input; no
conditional premise remains in the final theorem.

## Dependencies and provenance

The imported statement and all its imported definitions remain unchanged.
The support modules are imported by their Lean names:

- `Langlands.GroupScheme.Torus.SplittingDescentHelpers` supplies the
  field-tower comparison and finite Galois enlargement, and imports the
  torus geometry lemmas.
- `Langlands.GroupScheme.Torus.SplittingAssembly` supplies the actual
  Hopf-coordinate comparisons, affineness descent and the separably closed
  splitting assembly.
- `Langlands.GroupScheme.Torus.FiniteSeparableSplitting`, authored by
  Worker 27, supplies finite-stage descent.
- `Langlands.RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningProof`,
  authored by Workers 321 and 1248, supplies unconditional descent of
  group-like spanning. Its proof uses finite-dimensional subcoalgebras,
  the canonical convolution-dual base-change equivalence, faithfully flat
  descent of formal unramifiedness, and splitting of finite étale algebras
  over a separably closed field. Local finiteness is a proved dependency,
  not an assumption about the torus.

This module is a derived assembly of those proved interfaces. The original
mathematical statement and source correspondence are recorded in the
unchanged statement Markdown: Milne, *Algebraic Groups* (2017),
Theorem 12.18 and Corollary 12.19, and SGA 3 X, Proposition 1.4, followed
by finite Galois enlargement. The implemented route goes through the
separable closure and finite-stage descent. It is not a transcription of
a new source assertion. Worker 1337 authored this final assembly and the
coordinate and geometry support; Worker 27 supplied the finite-stage
step in this task.
