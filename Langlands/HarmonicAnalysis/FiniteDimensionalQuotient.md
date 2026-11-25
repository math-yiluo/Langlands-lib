# Quotients and subspaces of a finite-dimensional space over a topological field

Outside GKT; the measure-theoretic preliminaries for the integrals over quotients `(A ∩ B) \ B`
and `ker(c) \ X` of GKT Proposition 1.21 (p. 30) and Proposition 2.13 (p. 55).

The module `Langlands.HarmonicAnalysis.FiniteDimensionalQuotient` collects what is needed to
integrate over a quotient `V ⧸ K` of a finite-dimensional vector space by a subspace: its topology,
σ-algebra and Haar measures, and the behaviour of Haar measures under linear isomorphisms.

## Content

Let `F` be a topological field and `V` an `F`-vector space with its module topology
(`IsModuleTopology F V`); Mathlib gives `V ⧸ K` the quotient topology, which is again the module
topology (`IsModuleTopology.instQuot`), and the quotient σ-algebra.

- `continuous_of_linearMap'`: a linear map from a space with the module topology to one with the
  module topology is continuous. Hence the instance `Langlands.Theta.isAddHaarMeasure_map_linearEquiv
  (e : X' ≃ₗ[F] X) (ν : Measure X') [ν.IsAddHaarMeasure] : (ν.map e).IsAddHaarMeasure` (for
  spaces with their module topologies, `X` a topological additive group, Borel σ-algebras): the
  image of a Haar measure under a linear isomorphism is a Haar measure (`e` is an additive
  homeomorphism). Its name is in the namespace `Langlands.Theta`, where it was first used.
- `exists_continuous_section`: the quotient map `V → V ⧸ K` has a continuous linear section.
- `borelSpace_quotient`, instance `instBorelSpaceQuotient`: the quotient σ-algebra is the Borel
  σ-algebra of the quotient topology (a set `S` with Borel preimage is the preimage of that set
  under the continuous section).
- `isModuleTopology_submodule`: the subspace topology of a subspace is its module topology (a
  linear left inverse `V → K` of the inclusion is continuous).
- `isCompact_preimage_of_injective`: for an injective linear map to a Hausdorff space with the
  module topology, preimages of compact sets are compact (they are closed and contained in the
  image of the compact set under a continuous linear left inverse).

Over a nonarchimedean local field `F` and a finite-dimensional `V`:

- instances `instLocallyCompactSpaceQuotient`, `instT2SpaceQuotient`,
  `instSecondCountableTopologyQuotient`, `instIsTopologicalAddGroupQuotient` for `V ⧸ K` (through
  the coordinates of `Langlands.HarmonicAnalysis.Bicharacter.SelfDual`), so that Haar measures on
  `V ⧸ K` exist and are unique up to a positive scalar;
- `isClosed_submodule`: every subspace is closed (the kernel of `V → V ⧸ K`);
- `linearEquivToContinuousAddEquiv`: a linear isomorphism as an additive homeomorphism;
- `exists_map_eq_smul`: the image of a Haar measure under a linear isomorphism `V ≃ V'` is `c ν`
  for any Haar measure `ν` on `V'` and some `c > 0` (Mathlib's `isAddLeftInvariant_eq_smul`).

## Declarations

- `continuous_of_linearMap'`, `exists_continuous_section`, `borelSpace_quotient`,
  `instBorelSpaceQuotient`, `isModuleTopology_submodule`, `isCompact_preimage_of_injective`.
- `instLocallyCompactSpaceQuotient`, `instT2SpaceQuotient`, `instSecondCountableTopologyQuotient`,
  `instIsTopologicalAddGroupQuotient`, `isClosed_submodule`, `linearEquivToContinuousAddEquiv`,
  `linearEquivToContinuousAddEquiv_apply`, `exists_map_eq_smul`.
- The instance `Langlands.Theta.isAddHaarMeasure_map_linearEquiv`.

All in the name space `Langlands.HarmonicAnalysis`.

## Dependencies

`Langlands.HarmonicAnalysis.Bicharacter.SelfDual` (`locallyCompactSpace_of_finiteDimensional`,
`t2Space_of_finiteDimensional`, `secondCountableTopology_of_finiteDimensional`); Mathlib:
`MeasureTheory.Constructions.SubmoduleQuotient`, `MeasureTheory.Measure.Haar.Unique`.
