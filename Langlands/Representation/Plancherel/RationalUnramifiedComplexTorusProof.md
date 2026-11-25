# The complex torus `X(G)` and its real subtorus `Im X(G)` (Renard V.3.20): proof

`Langlands.Plancherel.rationalUnramifiedComplexTorus` proves
`Langlands.Plancherel.RationalUnramifiedComplexTorusStatement.{u}`, at the statement's universe
parameter `u`. [Published statement](RationalUnramifiedComplexTorusStatement.md)

## The proof

The statement is by definition the conjunction, in this order, of four component statements of
the same module. Each component already has a published proof whose type is exactly that
component at universe `u`. The theorem is the anonymous constructor of these four proofs:

1. `RationalUnramifiedBasisChartIndependenceStatement.{u}`:
   `rationalUnramifiedBasisChartIndependence`, in
   `Langlands.Representation.Plancherel.RationalUnramifiedBasisChartIndependenceProof`.
   [Proof](RationalUnramifiedBasisChartIndependenceProof.md)
2. `RationalUnramifiedComplexLieGroupStatement.{u}`: `rationalUnramifiedComplexLieGroup`, in
   `Langlands.Representation.Plancherel.RationalUnramifiedComplexLieGroupProof`.
   [Proof](RationalUnramifiedComplexLieGroupProof.md)
3. `RationalUnramifiedComplexExponentialStatement.{u}`: `rationalUnramifiedComplexExponential`,
   in `Langlands.Representation.Plancherel.RationalUnramifiedComplexExponentialProof`.
   [Proof](RationalUnramifiedComplexExponentialProof.md)
4. `RationalUnitaryUnramifiedSubmanifoldStatement.{u}`: `rationalUnitaryUnramifiedSubmanifold`,
   in `Langlands.Representation.Plancherel.RationalUnitaryUnramifiedSubmanifoldProof`.
   [Proof](RationalUnitaryUnramifiedSubmanifoldProof.md)

All four names are in the namespace `Langlands.Plancherel`. The mathematical work is in these
four published proofs; this module adds none. It only pairs them.

The theorem depends on the axioms `propext`, `Classical.choice` and `Quot.sound` only.

## Scope

The theorem proves exactly the target statement, with its scope:

- Every component holds for a nonarchimedean local field `F` (with `ValuativeRel F`,
  `TopologicalSpace F` and `IsNonarchimedeanLocalField F`) and a connected reductive group scheme
  `G` over `F`, with the canonical topology `rationalPointTopology F G.X` on `G(F)`.
- Every component holds for each integer basis `b` of the valuation image `Λ(G)`, and gives
  `X(G)` the one-chart complex charted space `rationalUnramifiedBasisChartedSpace G b`.
- The `Im X(G)` component asserts that there exist a charted structure on `Im X(G)` modelled on
  `Fin r → ℝ`, where `r = rationalImageRank G`, a smooth real Lie group structure for it, a smooth
  embedding of `Im X(G)` into `X(G)` regarded as a real manifold, and a local diffeomorphism
  `e : (Fin r → ℝ) → Im X(G)` that lifts the imaginary exponential
  `t ↦ exp(b.constr ℤ (t·i))`.

The statement does not include, and this theorem does not prove, the compactness of `Im X(G)` or
its description as the quotient `i𝔞*/((2iπ/ln q)𝓡)`, where `𝓡 = Hom_ℤ(Λ(G), ℤ)` is the lattice
of integer-valued homomorphisms on `Λ(G)` (Renard V.3.20, printed p.116). In Lean this is the
quotient of the imaginary parameters `rationalImageImaginaryParameters G` by the imaginary period
lattice `rationalImageImaginaryPeriodLattice G`. Those two results are separately published: the
theorem `Langlands.Plancherel.compactSpace_rationalUnitaryUnramifiedCharacters`, and the statement
`Langlands.Plancherel.RationalImaginaryParameterQuotientStatement` with its proof
`Langlands.Plancherel.rationalImaginaryParameterQuotient`.

## Instance rename in `RationalUnitaryUnramifiedBasis`

The four component proof modules can be imported together only because of the following rename.
`RationalUnramifiedBasisChartTransitionProof` (imported by the first component proof) and
`RationalUnitaryUnramifiedBasis` (imported by the fourth) each declared, in the namespace
`Langlands.Plancherel`, an anonymous file-local instance
`TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X`. `local` limits
only the instance attribute, and the declaration is global. Neither module imports the other, so
Lean gave both the generated name `Langlands.Plancherel.instTopologicalSpaceRationalPoints`, and a
joint import failed with a duplicate-declaration error.

With this file, the instance of
`Langlands/Representation/Plancherel/RationalUnitaryUnramifiedBasis.lean` was named explicitly as
`instTopologicalSpaceRationalPoints_rationalUnitaryUnramifiedBasis`. Only the name changed: the
type and the value are as before, and no Library file refers to the instance by name.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Plancherel.RationalUnramifiedComplexTorusStatement` | the target `RationalUnramifiedComplexTorusStatement` |
| `Langlands.Representation.Plancherel.RationalUnramifiedBasisChartIndependenceProof` | `rationalUnramifiedBasisChartIndependence` |
| `Langlands.Representation.Plancherel.RationalUnramifiedComplexLieGroupProof` | `rationalUnramifiedComplexLieGroup` |
| `Langlands.Representation.Plancherel.RationalUnramifiedComplexExponentialProof` | `rationalUnramifiedComplexExponential` |
| `Langlands.Representation.Plancherel.RationalUnitaryUnramifiedSubmanifoldProof` | `rationalUnitaryUnramifiedSubmanifold` |
