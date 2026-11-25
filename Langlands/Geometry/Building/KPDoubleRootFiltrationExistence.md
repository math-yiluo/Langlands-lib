# Existence of a double-root friendly filtration of `Z(F)` (KP §9.8)

Lean module: `Langlands.Geometry.Building.KPDoubleRootFiltrationExistence`.

The theorem `Langlands.Geometry.Building.centralizerFiltrationDoubleRootExistence` proves the
published proposition
`Langlands.Geometry.Building.CentralizerFiltrationDoubleRootExistenceStatement` (module
`KPMoyPrasadDoubleRootStatement`) at arbitrary universe `u`. Its type is exactly
`CentralizerFiltrationDoubleRootExistenceStatement.{u}`. It adds no hypothesis, assumes no
unproved proposition and uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

Let `F` be a nonarchimedean local field, in either characteristic, `G` a group scheme over
`Spec F` with `[IsAffineHom G.X.hom]`, and `P : ParahoricBuildingData G` with
`P.SatisfiesApartmentAxioms`. Then there is a filtration `Zf : P.CentralizerFiltration` of
`Z(F)`, `Z = Z_G(S)`, with `Zf.SatisfiesFiltrationAxioms`, `Zf.IsOpenFiltration` and
`Zf.IsDoubleRootCommutatorFriendly`.

## The construction

The filtration is the one of Kaletha–Prasad §9.8: `Z(F)_r = Z(K)_{x,r} ∩ Z(F)`, where
`K = UnramifiedClosure F` is the maximal unramified extension. In Lean it is built in three
layers, all published in the Library.

1. **Building data over `K`.** For the given `P`, the comparison statement
   `UnramifiedComparisonExistenceStatement` (module `KPUnramifiedComparisonExistenceStatement`)
   supplies building data `B` of `G_K = baseChanged F K G`, a proof `hZ` that
   `B.centralizer.Z` is a torus, and a map `e : P.Apartment → B.Apartment` from the apartment
   `A(S)` to the apartment over `K`, satisfying `P.IsUnramifiedComparison B hZ e` (KP §9.6,
   §9.8.2).
2. **The rational family.** Put `Q y r = (B.moyPrasad hZ (e y) r).comap (rationalExtend F K G)`,
   that is `G(K)_{e y,r} ∩ G(F)`. The glue theorem
   `unramifiedRationalMoyPrasad_of_unramifiedComparison` (module
   `KPUnramifiedMoyPrasadComparison`) turns the comparison and the `K`-level Moy–Prasad
   properties into the ten fields of `P.IsRationalMoyPrasadFamily Q`.
3. **The filtration.** `IsRationalMoyPrasadFamily.centralizerFiltration hQ x₀` (module
   `KPRationalMoyPrasadFamily`) is the filtration `r ↦ j⁻¹(Q x₀ r)`, where
   `j : Z(F) → G(F)` is the inclusion and `x₀` is an arbitrary apartment point. This is
   `Z(K)_{x₀,r} ∩ Z(F)`.

## The proof

The proof is a short tactic block.

1. `have hC : UnramifiedComparisonExistenceStatement.{u}` is
   `unramifiedComparisonExistence_of_fields` (module `KPUnramifiedComparisonFieldStatements`)
   applied to six published proofs:
   - `specialTorusExistence : SpecialTorusExistenceStatement` (module
     `SpecialTorusExistenceProof`): a special `F`-torus `T ⊇ S` exists;
   - `unramifiedValuationDescent : UnramifiedValuationDescentStatement` (module
     `UnramifiedValuationDescentProof`): descent of the valuation of the root datum from `K`
     to `F` (KP Construction 9.6.1, Lemma 9.6.3, Theorem 9.6.5);
   - `unramifiedComparisonRootField : UnramifiedComparisonRootFieldStatement` (module
     `KPUnramifiedComparisonRootFieldProof`);
   - `unramifiedComparisonLeviField : UnramifiedComparisonLeviFieldStatement` (module
     `KPUnramifiedComparisonLeviFieldProof`);
   - `unramifiedComparisonZeroField : UnramifiedComparisonZeroFieldStatement` (module
     `KPUnramifiedComparisonZeroFieldProof`);
   - `unramifiedComparisonOpenField : UnramifiedComparisonOpenFieldStatement` (module
     `KPUnramifiedComparisonOpenProof`).

   The assembly theorem builds a concrete unramified apartment lift from the first two
   inputs (`exists_unramifiedApartmentLift`). It then fills the fields of
   `IsUnramifiedComparison` with the other four.
2. `have h3 : UnramifiedRationalMoyPrasadStatement.{u}` is
   `unramifiedRationalMoyPrasad_of_unramifiedComparison` (the glue in module
   `KPUnramifiedMoyPrasadComparison`) applied to
   `MaximalUnramified.localMoyPrasadGroupProperties :
   MaximalUnramified.LocalMoyPrasadGroupPropertiesStatement` (module
   `KPLocalMoyPrasadGroupPropertiesProof`, the eight `K`-level properties of `G(K)_{x,r}`)
   and `hC`.
3. After introducing `F`, `G`, `P` and `hP`, `h3 F G P hP` gives `B`, `hZ`, `e` and
   `hQ : P.IsRationalMoyPrasadFamily Q`.
4. The reduction
   `ParahoricBuildingData.exists_doubleRootFriendly_filtration_of_rationalMoyPrasadFamily hP hQ`
   (module `KPRationalMoyPrasadFamily`) closes the goal. It takes `x₀` arbitrary and returns
   `hQ.centralizerFiltration x₀` with three proofs:
   - `satisfiesFiltrationAxioms`: commutator friendliness (KP Definition 7.2.1 and
     Lemma 9.8.1), `N(F)`-stability, `[Z(F)_r, Z(F)_s] ⊆ Z(F)_{r+s}` and root-block
     compatibility;
   - `isOpenFiltration`: openness;
   - `isDoubleRootCommutatorFriendly`: the `Z`-component bound `Z(F)_{2r}` when `u ∈ U_{2a}(F)`
     or `u' ∈ U_{-2a}(F)`.

The two intermediate statements are written as typed `have`s. When the whole composite term
is elaborated against the unfolded target in one step, elaboration exceeds the default
heartbeat limit.

## Companion change: named local instances

The proof imports both `KPLocalMoyPrasadGroupPropertiesProof`, which imports
`KPLocalCoordinateValuationComparison`, and the comparison-side proofs, which import
`UnramifiedOmegaGaloisStable`. In the Library both modules declared anonymous
`local instance`s `NontriviallyNormedField F`, `IsUltrametricDist F` and `CompleteSpace F` in
namespace `Langlands.Geometry.Building.MaximalUnramified`. Both got the same auto-generated
names, such as `MaximalUnramified.instNontriviallyNormedField_langlands`, so no module could
import both. The three local instances of
`KPLocalCoordinateValuationComparison` therefore have explicit names: `coordinateValuationNormedField`,
`coordinateValuationUltrametric` and `coordinateValuationComplete`. Their values are
unchanged, no statement or proof in that module changes, and no Lean file in the Library
refers to the old auto-generated names. All 12 Library modules that import it, directly or
transitively, still compile with the change, as does this module.
