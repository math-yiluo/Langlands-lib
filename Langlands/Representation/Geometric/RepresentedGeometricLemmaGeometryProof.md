# Geometric prerequisites of the represented geometric lemma (Renard V.4.5–V.4.7): proof

`representedGeometricLemmaGeometry`, in namespace
`Langlands.Aubert.General.RepresentedParabolic`, proves the published proposition
`RepresentedGeometricLemmaGeometryStatement.{u}` (module
`Langlands.Representation.Geometric.RepresentedGeometricLemmaGeometryStatement`) with no
hypotheses. Fix a nonarchimedean local field `k`, a connected reductive `G` over `k` with the
canonical rational-point topology and the retained local-compactness and
nonarchimedean-group instances, and two arbitrary represented parabolics `P = MN` and
`Q = LU`. The theorem gives:

- a natural number `m` and an equivalence `Fin m ≃ P(k) \ G(k) / Q(k)`, so the actual
  rational double-coset quotient is finite;
- a representative `z i ∈ G(k)` of the `i`-th double coset;
- a full `GeometricLemmaIntersectionDatum` at every `z i`.

Finiteness, the representatives, the intersection data and the maximal split torus inside
each datum are all conclusions. No standardness of the parabolics, minimal parabolic,
representatives, intersection data or torus is supplied, and the full represented geometric
lemma is not used.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`). V.4.5 (printed
pp.119–120 / PDF pp.125–126) gives the finite double cosets, and V.4.6–V.4.7 (printed
pp.120–122 / PDF pp.126–128) give the representatives and the intersection geometry. These
are the locations cited by the statement's paired Markdown. The proof below assembles
published Library results and does not follow the literature's proof step by step.

## Implemented proof

The theorem is a single term built from published results. It adds no new lemma.

1. **Double cosets with torus-adapted representatives.** The published conditional assembly
   `representedParabolicDoubleCosetStatement_of_dynamic_structural_inputs` (module
   `Langlands.GroupScheme.Rational.ParabolicDoubleCosetAssembly`) is applied to six published
   unconditional proofs: `rationalBruhat`, `genericMinimalParabolic`,
   `minimalParabolicConjugacy`, `parabolicIntersectionCentralizer`, `parabolicDynamic` and
   `smoothMaximalSplitTorusConjugacy`. This proves `RepresentedParabolicDoubleCosetStatement`:
   - the rational double-coset quotient is finite;
   - every double coset has a representative `z` and a maximal split torus `T` of `G` that
     factors through `M` and through `z L z⁻¹`.
2. **Intersection data.** The published reduction
   `representedGeometricLemmaGeometry_of_doubleCoset_of_parabolicDynamic` (module
   `Langlands.Representation.Geometric.RepresentedGeometricLemmaTorusFactorConstruction`) is
   applied to the result of step 1 and to the published `parabolicDynamic`. For each double
   coset it uses `geometricLemmaIntersectionDatumOfTorusFactors`, which chooses cocharacters
   of the torus `T` that realize both parabolic triples and builds the full intersection
   datum at `z`. The published enumeration lemma
   `exists_enumerated_geometricLemmaIntersectionDatum` then enumerates the finite quotient by
   `Fin m`.

The module adds only this composition. The statement pair and its imported closure are
unchanged. The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
