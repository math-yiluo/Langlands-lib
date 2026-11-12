# The geometric lemma for represented parabolics (Renard VI.5.1): proof

`representedGeometricLemma`, in namespace `Langlands.Aubert.General.RepresentedParabolic`,
proves the published proposition `RepresentedGeometricLemmaStatement.{u,v}`, with
independent field and representation-carrier universes and no hypotheses. Fix a
nonarchimedean local field `F`, a connected reductive `G` with its canonical rational-point
topology and retained local-compactness and nonarchimedean-group instances, and two
arbitrary represented parabolics `P = MN` and `Q = LU`. The theorem gives four things:

- a finite enumeration `Fin m ≃ P(F) \ G(F) / Q(F)` of the actual double cosets;
- a representative `z i` of each class;
- a full `GeometricLemmaIntersectionDatum` at each `z i`;
- a proof that `leviJacquetInductionFunctor`, the composite `r_Q ∘ i_P` of normalized
  induction and the normalized Jacquet functor, is `IsGluedFrom` the pieces
  `(D i).pieceFunctor = i^L_{Q'} ∘ ι ∘ r^M_{P'}`.

Representatives, intersection data and the filtration are all conclusions. No
admissibility, finite length, irreducibility, standardness of the parabolics, minimal
parabolic, representatives, intersection data or filtration is supplied.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`). VI.5.1: the theorem
and its reformulation are on printed pp.161–162 / PDF pp.167–168, and the proof runs to
printed p.172 / PDF p.178. V.4.5 (printed pp.119–120 / PDF pp.125–126) and V.4.7 (printed
pp.121–122 / PDF pp.127–128) supply the finite double cosets and the representatives.
For finiteness and the representatives, the Library also follows Borel–Tits, *Groupes
réductifs* (1965): 5.20 (printed p.102 / PDF p.49) and 4.18 (printed p.92 / PDF p.39).

## Implemented proof

The theorem applies the published conditional reduction
`representedGeometricLemma_of_geometry_and_orbitComparison` (module
`RepresentedGeometricLemmaOrbitReduction`) to four unconditional inputs.

1. **Geometry.** `RepresentedGeometricLemmaGeometryStatement` is proved by the published
   `representedGeometricLemmaGeometry_of_doubleCoset_of_parabolicDynamic` (module
   `RepresentedGeometricLemmaTorusFactorConstruction`). It is applied to the published
   `parabolicDynamic` and to a proof of `RepresentedParabolicDoubleCosetStatement`. That
   proof is the published
   `representedParabolicDoubleCosetStatement_of_dynamic_structural_inputs` (module
   `GroupScheme/Rational/ParabolicDoubleCosetAssembly`), applied to the published proofs
   `rationalBruhat`, `genericMinimalParabolic`, `minimalParabolicConjugacy`,
   `parabolicIntersectionCentralizer`, `parabolicDynamic` and
   `smoothMaximalSplitTorusConjugacy`.
   - The first three premises give finiteness: the finite set of minimal-parabolic double
     cosets, indexed by the relative Weyl group, maps onto `P(k) \ G(k) / Q(k)`.
   - The last three give, for each double coset, a representative `z` and a maximal split
     torus of `G` inside both `M` and `z L z⁻¹`.
   - For each representative, the torus-factor construction chooses cocharacters of that
     torus realizing both original triples and builds the full intersection datum. The
     published enumeration lemma `exists_enumerated_geometricLemmaIntersectionDatum`
     enumerates the finite quotient.
2. **Quotient compactness.** The published `arbitraryParabolicQuotientCompact`.
3. **Presentation existence.** The published `parabolicRootPresentationExistence`.
4. **Local orbit comparison.** `representedGeometricLemmaOrbitComparison`, from the sibling
   module `RepresentedGeometricLemmaOrbitComparisonProof`.

The imported reduction then works as follows; its paired Markdown has the details.

- The published finite-orbit ordering of the `Q(F)`-orbits on `P(F) \ G(F)` is reindexed
  to use the inverses of the good representatives from step 1.
- Along the induced order, Renard's support filtration of `i_P` (VI.5.1, printed
  pp.162–164 / PDF pp.168–170) becomes a filtration by actual support-image subspaces. Its
  image under the normalized target coinvariants is `leviJacquetSupportFiltration`.
- A root presentation of the specified target triple, from step 3, shows that the target
  radical points are a limit of compact subgroups. This gives the exactness of the
  coinvariants that the filtration needs.
- Compactness of `P(F) \ G(F)`, from step 2, identifies each support-image grade with the
  normalized coinvariants of its compact orbit piece (`leviJacquetSupportOrbitIso`).
- The local orbit comparison identifies that piece with `(D i).pieceFunctor`.
- The identity permutation witnesses `IsGluedFrom`.

The filtration is natural on the whole category of smooth complex representations of
`M(F)`. This module adds only the composition. The statement pair and its imported
closure are unchanged.
