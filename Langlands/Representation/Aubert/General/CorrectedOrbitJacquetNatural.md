# Naturality of the explicit orbit Jacquet data

Module: `Langlands.Representation.Aubert.General.CorrectedOrbitJacquetNatural`,
namespace `Langlands.Aubert.General.CorrectedFiltration`. It imports
`CorrectedOrbitJacquet` (the explicit data `orbitJacquetData`) and
`CorrectedGradedNatural` (the predicate `OrbitJacquetData.IsNatural`).

Author: Worker 1255 (task `d6be9c3b-ff6f-425c-9bb5-84c973b9568f`). The module answers
Worker 969's request for a naturality lemma for the orbit Jacquet data. It is a
conditional helper and does not prove the rational task target.

## Provenance

This is an internal derived result with no source in the literature. It states that
the orbit maps of `CorrectedOrbitJacquet` are natural in the representation, which is
the naturality of the orbit isomorphism of Aubert's erratum (Trans. AMS 348 (1996),
p. 4689), as cited in the Markdown of `CorrectedOrbitJacquet`. No source page was
re-read for this pair.

## Data

The ambient data are those of the section `Data` of `CorrectedOrbitJacquet`:

- semidirect decompositions `h : P_J = M_J ⋉ U_J` with closed `U_J`;
- `hU : Antitone U`, `hP : Monotone P` and closed `P_J` (`hPc`);
- a subgroup `T` with a Coxeter system `cs` on its relative Weyl group;
- an index set `I`, a Weyl element `w`, an element `m : G` and an index set `K`, with
  `hK : x ∈ M_I ↔ m⁻¹ x m ∈ M_K`.

The group `G` is locally compact, nonarchimedean and Hausdorff. The structural inputs
`hS1`, `hS2`, `hr` and `hD07` are the hypotheses of `orbitJacquetData` with the same
names. None of them mentions the representation.

## Results

- `orbitJacquetData_isNatural` (theorem): let `μN`, `μI` and `ν` be Haar measures on
  `U_I` (as the kernel of the Levi projection) and on `U_I ∩ m U_K m⁻¹`, and a
  compatible quotient measure. Let `φ : A ⟶ B` be a morphism of smooth
  representations. Then the data `orbitJacquetData … A …` and `orbitJacquetData … B …`,
  built from the same structural inputs and the same measures, satisfy
  `OrbitJacquetData.IsNatural _ _ φ`. Explicitly, take any surviving `s` (`K ⊆ univ \ s`,
  `w` minimal for `(univ \ s, I)`) and orbit functions `ψ` for `A` and `ψ'` for `B`
  with `ψ'(q) = [φ](ψ(q))` in `B_{U_J}` for every `q ∈ P_I`. Then
  `Θ^B_s ψ' = [φ](Θ^A_s ψ)` in `B_{U_K}`.
- `exists_compactOpen_unipotent_of_isLimitOfCompactSubgroups` (theorem): if
  `Jacquet.Localization.IsLimitOfCompactSubgroups ((U I).subgroupOf (P I))` holds, then
  every `u ∈ U_I` lies in a compact open subgroup of `U_I`.
- `naturalOrbitJacquetData` (definition): under the same compact-limit hypothesis
  `hNc`, the orbit Jacquet data of a smooth representation `E` (in the universe of
  `OrbitJacquetData`) are `orbitJacquetData … E … μN μI ν`. Here `μN` and `μI` are the
  Haar measures `haar` for the Borel structures on the kernel of the Levi projection
  and on `U_I ∩ m U_K m⁻¹`, and `ν` is a compatible quotient measure chosen by
  `Classical.choose` from `compatibleMeasureExists`. None of these choices depends on
  `E`, which is the last explicit argument.
- `naturalOrbitJacquetData_isNatural` (theorem): for every `φ : A ⟶ B`,
  `(naturalOrbitJacquetData … A).IsNatural (naturalOrbitJacquetData … B) φ`.

## Proofs

`orbitJacquetData_isNatural` is a single term. At a surviving `s`, the field `Θ s` of
`orbitJacquetData` is `orbitJacquetMap` for `P_J`, `U_J` and `U_K`, where `J = univ \ s`.
This map has the same structural arguments and the same measure `ν` for `A` and `B`.
So the claim is `orbitJacquetMap_natural` at `φ`, `ψ`, `ψ'` and the pointwise premise.
In turn, `orbitJacquetMap_natural` follows from `splitKernelValueIntegral_map_of_eval`
and the naturality of the coinvariant transition `E_{U_J} → E_{U_K}`.

`exists_compactOpen_unipotent_of_isLimitOfCompactSubgroups` repeats the argument of
`nonempty_orbitJacquetData_of_isLimitOfCompactSubgroups`. The subgroup
`V = (U I).subgroupOf (P I)` is nonarchimedean and locally compact, since `U_I` and
`P_I` are closed. `exists_compactOpen_mem_of_isLimitOfCompactSubgroups` gives a compact
open subgroup of `V` containing the image of `u` under the inverse of the topological
group isomorphism `subgroupOfEquiv : V ≃ U_I`. Its preimage under this inverse is the
required subgroup of `U_I`.

`naturalOrbitJacquetData` repeats the measure construction of `nonempty_orbitJacquetData`:

- Borel structures on the kernel of the Levi projection, on `U_I ∩ m U_K m⁻¹` and on
  their quotient;
- Haar measures `μN` and `μI`. They are right invariant by
  `Haar.compactOpenCoverUnimodularity`, whose compact-open cover of the kernel comes
  from the previous theorem transported along `projectionKerEquiv`;
- the compatible quotient measure `ν` from `compatibleMeasureExists`.

It then applies `orbitJacquetData` to `E`.

`naturalOrbitJacquetData_isNatural` rebuilds the same instances, measures and choice
so that the definitions unfold to `orbitJacquetData` with identical measures for `A`
and `B`. It then applies `orbitJacquetData_isNatural`.
