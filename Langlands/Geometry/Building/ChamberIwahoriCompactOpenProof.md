# Compact openness of the actual chamber Iwahori

Author: Worker 4343 (task `0afe58ab-4d40-41b0-a74d-258400979322`).

```lean
theorem Langlands.Geometry.Building.ParahoricBuildingData.chamberIwahoriCompactOpen
    (P : ParahoricBuildingData G) : P.ChamberIwahoriCompactOpenStatement
```

This proves the published target
[`ChamberIwahoriCompactOpenStatement`](ChamberIwahoriCompactOpenStatement.md)
at an arbitrary universe `u`. The theorem has the same binders as the
target:

- a nonarchimedean local field `F : Type u`, with the existing `Field`,
  `ValuativeRel`, `TopologicalSpace` and `IsNonarchimedeanLocalField`
  instances;
- a group scheme `G` over `Spec F` with affine structure morphism;
- an actual `P : ParahoricBuildingData G`.

Its type is the target itself. Assume the fixed-apartment axioms
`P.apartment.SatisfiesApartmentAxioms P.centralizer`, which include V 6, V 7
and the corrected AS 5. Then for every chamber `C` of the actual apartment,
the full chamber parahoric `P.chamberIwahori C = P.parahoric C` is compact
and open in `G(F)`. Here `P.parahoric C` is `j(Z(F)^0) ⊔ G(F)^♯_C`, with its
`Z(F)^0` factor, and `G(F)` carries the canonical topology
`rationalPointTopology F G.X`.

The theorem has no other hypothesis. It assumes no compactness, openness,
bounded-open-stabilizer, integral-model or full-validity statement. Both
equal and mixed characteristic are covered. So is relative rank zero: there
the root enumerations below are empty and the block products are the
identity.

## Lean module

`Langlands/Geometry/Building/ChamberIwahoriCompactOpenProof.lean` installs
the same local instances as
[`ChamberIwahoriCompactOpenReduction`](ChamberIwahoriCompactOpenReduction.md):

- `IsAffine G.X.left` and `rationalPointTopology F G.X` on `G(F)`;
- for the actual centralizer `Z = Z_G(S)` of `P`, the affine instance from
  the closed immersion `j : Z → G`, and `rationalPointTopology F Z.X` on
  `Z(F)`.

These instances agree with the `letI` instances in the target and in every
published statement used below. The module contains five declarations.

### `hasRankOneFactorization_actual`

`RelativeRoot.HasRankOneFactorization P.i` holds. It is the published proof
`rootRankOneFactorization`
([`RootRankOneFactorizationProof`](../../GroupScheme/Rational/RootRankOneFactorizationProof.md))
applied to the actual group, maximal split torus and torus embedding of `P`.

### `isOpen_chamberIwahori_actual`

Under the fixed-apartment axioms, `P_C` is open for every chamber `C`. The
proof applies the published reduction
`isOpen_chamberIwahori_of_openRootGeneration`
([`ChamberIwahoriCompactOpenReduction`](ChamberIwahoriCompactOpenReduction.md))
and supplies both of its premises from published proofs:

- **KP Corollary 8.2.6.** `RelativeRoot.OpenRootCentralizerGenerationStatement.{u}`
  is `openRootCentralizerGeneration_of_dynamicRootOrderedProduct`
  ([`OpenRootGenerationReduction`](../../GroupScheme/Rational/OpenRootGenerationReduction.md))
  applied to the published proof `RelativeRoot.dynamicRootOrderedProduct`
  ([`DynamicRootOrderedProductProof`](../../GroupScheme/Rational/DynamicRootOrderedProductProof.md)).
- **Openness of `Z(F)^0`.** This is the second component of the published
  `ParahoricBuildingData.centralizerZeroCompactOpen`
  ([`KPCentralizerZeroCompactOpenProof`](KPCentralizerZeroCompactOpenProof.md)).

Inside the reduction, `chamberIwahori_eq_parahoricAt`
([`ChamberParahoricConstancy`](ChamberParahoricConstancy.md)) identifies
`P_C` with `P_x` for a point `x ∈ C`. Corollary 8.2.6 is then applied to the
open root filtrations `U_{a,x,0}` (open by V 7) and to the open subgroup
`Z(F)^0`.

### `sharpCentralizer_subset_image_centralizerNormKernel`

Under the fixed-apartment axioms, for every apartment point `x`,

```text
Z^♯_x = Z(F) ∩ G(F)^♯_x  ⊆  j(Z(F)^1).
```

Here `Z^♯_x` is the Library's `sharpCentralizer {x}` (KP Definition
7.4.1(3)), and `Z(F)^1` is the common norm kernel
`Plancherel.rationalCommonNormKernel Z`.

Proof. Take `g ∈ Z^♯_x`. Since `j` represents the torus centralizer, `g`
is `j(z)` for some `z ∈ Z(F)`. The sharp fixer `G(F)^♯_x` lies in `P_x`
(`sharpFixer_le_parahoric`), so `j(z) ∈ P_x`. The published
`mem_centralizerNormKernel_of_mem_parahoric`
([`PointParahoricCentralizer`](PointParahoricCentralizer.md)) then gives
`z ∈ Z(F)^1`, using the fixed-apartment axioms and the rank-one
factorization above. That lemma combines two facts. First, rank-one point
exchange shows that `j(z)`, as an element of the normalizer, fixes `x`.
Second, `P_x` lies in the ambient zero subgroup `G(F)^0`, which lies in the
norm kernel `G(F)^1`.

This replaces the cover-image comparison
`ZeroSubgroupDatum.CoverImageCentralizerNormKernelStatement`, which would
give the sharper inclusion into `j(Z(F)^0)`. That comparison is not used.

### `isCompact_chamberIwahori_actual`

Under the fixed-apartment axioms, `P_C` is compact for every chamber `C`.

Proof. `G` is smooth, so `G(F)` is a topological group
(`rationalPoint_isTopologicalGroup`). Choose `x ∈ C`
(`exists_mem_of_isChamber`) and a generic cocharacter `ν`
(`IsSplitTorus.exists_genericCocharacter`).

1. **Sharp chamber decomposition.** The published
   `ValuationBuildingData.chamberSharpDecomposition_of_rankOneFactorization`
   ([`ChamberIwahoriLocalReduction`](ChamberIwahoriLocalReduction.md)) proves
   `ChamberSharpDecompositionStatement` (KP Corollary 7.4.9 with
   7.3.12(3),(5); see [`ChamberSharpStatement`](ChamberSharpStatement.md))
   from `dynamicRootOrderedProduct` and the rank-one factorization. Apply it
   to `C`, `x` and `ν`. Enumerate the indivisible roots positive on `-ν` and
   on `ν` injectively (`exists_indivisiblePositiveRoots_enumeration`). The
   last clause of `ChamberSharpConclusion` at depth `0` then gives

   ```text
   G(F)^♯_C = range (orderedSharpChamberProduct x false aneg apos)
            = { u⁻ · z · u⁺ : u⁻ ∈ A, z ∈ Z^♯_x, u⁺ ∈ B } ⊆ A · K · B.
   ```

   Here `A` and `B` are the ranges of the ordered depth-zero chamber block
   products `orderedChamberBlockProduct x false` for the two enumerations,
   and `K = j(Z(F)^1)`. The final inclusion is the previous declaration.
2. **Compact factors.**
   - `A` and `B` are compact by `isCompact_range_orderedChamberBlockProduct`
     ([`KPRootFixerTopology`](KPRootFixerTopology.md)): each root block is
     compact by V 7, and ordered multiplication is continuous.
   - `K` is the image under the continuous map `j` (`continuous_centralizerPointMap`)
     of `Z(F)^1`. `Z(F)^1` is compact by the published
     `ValuationBuildingData.isCompact_centralizerNormKernel_of_valuationData`
     ([`CentralizerNormKernelConstruction`](CentralizerNormKernelConstruction.md)),
     which has no structural or apartment premise.
   - `j(Z(F)^0)` is compact, as the image of `Z(F)^0`. The first component of
     `centralizerZeroCompactOpen` gives compactness of `Z(F)^0`.
3. **Containment.** By `coe_parahoric_eq_mul`
   ([`KPParahoricProduct`](KPParahoricProduct.md)),
   `P_C = j(Z(F)^0) · G(F)^♯_C` as sets. Step 1 gives
   `P_C ⊆ j(Z(F)^0) · ((A · K) · B)`, and this set is compact as a product
   of compact sets in a topological group.
4. **Closedness.** `P_C` is open by `isOpen_chamberIwahori_actual`. An open
   subgroup of a topological group is closed (`Subgroup.isClosed_of_isOpen`).

A closed subset of a compact set is compact, so `P_C` is compact.

### `chamberIwahoriCompactOpen`

The closing theorem introduces the apartment-axiom premise, the chamber `C`
and the chamber hypothesis. It returns the pair
`⟨isCompact_chamberIwahori_actual, isOpen_chamberIwahori_actual⟩`.

## Checks

`lean_check` in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`
compiles the module without errors or warnings. Inspection of
`chamberIwahoriCompactOpen` reports level parameter `u` and only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. The proof
adds no axiom and no `sorry`. The target and the modules it imports are
unchanged.

## Route and provenance

This proof composes published Library results. It adds no source
assertion. The target's Markdown records a derivation from Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, with the corrections of
1 November 2024, registered as `kaletha-prasad-2024-corrections`. That
derivation runs: `P_C = P_x` (Lemma 7.4.4); the constant-zero concave
function (Example 7.3.7(1), Definition 7.3.3(3)); bounded openness
(Corollary 7.3.14); closedness of open subgroups; Fact 2.2.3.

The implemented route keeps the parts on openness and closedness, and
proves compactness differently:

- **Openness.** As in the source, `P_C = P_x` (Lemma 7.4.4) and the
  openness half of 7.3.14, through the Library's KP Corollary 8.2.6. The
  proof of 7.3.14 itself refers to 8.2.6.
- **Closedness.** An open subgroup is closed, as in the source.
- **Compactness.** The source deduces compactness from algebraic
  boundedness and Fact 2.2.3. The Lean proof does not use boundedness. It
  instead places `P_C` inside an explicit compact product. That product is
  built from:
  - the depth-zero root blocks, compact by V 7;
  - the compact groups `Z(F)^0` and `Z(F)^1` in the canonical topology;
  - the sharp chamber decomposition of Corollary 7.4.9, which gives the
    product form.

  The compactness of `Z(F)^0` and `Z(F)^1` used here comes from the
  Library's published proofs. Their Markdown describes the local-field
  arguments, including the boundedness–compactness comparison where it
  is used.

The central factor of the sharp decomposition is placed in `j(Z(F)^1)`, not
in `j(Z(F)^0)`. Compactness needs only this weaker inclusion. So the proof
does not need KP Lemma 7.4.3 or the cover-image half of Corollary 2.6.28,
and it does not use `ChamberIwahoriDecompositionStatement`.
