# A smooth model containing the bounded points of two split tori (proof)

This module proves the Library proposition
`Langlands.Geometry.Building.SpecialTorusBoundedModelStatement.{u}` at arbitrary universe `u`,
in equal and mixed characteristic. The statement module
`Langlands.Geometry.Building.SpecialTorusBoundedModelStatement` and its Markdown are unchanged.

## Declarations

* `specialTorusBoundedModel_of_torusUnitGaloisFixedPoint` derives
  `SpecialTorusBoundedModelStatement.{u}` from
  `UnramifiedTorusUnitGaloisFixedPointStatement.{u}`. That proposition is the only premise.
  Every other input is a proved Library theorem.
* `specialTorusBoundedModel : SpecialTorusBoundedModelStatement.{u}` applies this derivation to
  the Library theorem `unramifiedTorusUnitGaloisFixedPoint :
  UnramifiedTorusUnitGaloisFixedPointStatement.{u}` (module
  `Langlands.Geometry.Building.UnramifiedTorusUnitGaloisFixedPointProof`). It has no premise.

Two private helpers support the proof. One is the instance that the base change of an affine
`F`-group to `K` is affine. The other is the lemma `conj_mem_stabilizer_smul`: if `h • p = p`,
then `g * h * g⁻¹` fixes `g • p`.

This candidate also edits one existing helper module,
`Langlands.Geometry.Building.IntegerVertexFixerApproximation`. Its four anonymous local instances
now have explicit names. The proof of `MaximalUnramified.finiteVertexFixerApproximation` imports
that module. The proof of `unramifiedTorusUnitGaloisFixedPoint` imports
`IntegerValuationBuildingMetricReduction` and `IntegerValuationRetractionDistance`. With
generated names, the same instances in those modules clash, for example
`IntegerValuationBuildingData.instNormedSpaceRealTranslationSpaceI`, so no module could import
both proofs. The rename changes no statement, definition or proof.

## Notation and source

Write `K = inertiaFixedField F` (the maximal unramified extension), `O_K = fixedFieldIntegers F`,
`v = MaximalUnramified.valuation F`, `Γ = K ≃ₐ[F] K` and `H(K)^1 = characterValuationKernel v H`.
The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach` (SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`). It is read together with
the corrections of 1 November 2024, `kaletha-prasad-2024-corrections` (SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`). The proof follows
the first paragraph of the proof of Proposition 9.3.4 (printed p.332 / PDF p.363), with the
corrected §9.2.1 (corrections PDF p.39).

## The implemented proof

Fix `F`, a connected reductive `G` and a maximal split torus `iS : S.toGrp ⟶ G`.

1. **Fixed point.** `UnramifiedTorusUnitGaloisFixedPointStatement` (in the final theorem, its
   proof `unramifiedTorusUnitGaloisFixedPoint`) gives building data
   `C : MaximalUnramified.BuildingData F (baseChanged F K G)`, a homomorphism
   `ρ : Γ →* Equiv.Perm C.ReducedBuilding` and a point `y`. Here `ρ` is semilinear for
   `rationalConjugate`, `y` is fixed by every `ρ σ`, and `y` is fixed by the image of
   `S_K(K)^1` (`IsFixedByUnramifiedTorusUnits`). This is the KP point `x` fixed by `Γ` and
   `S(K)^1`.
2. **Apartment presentation.** `exists_smul_apartmentMap` writes `y = g • apartmentMap x` for
   some `g ∈ G(K)` and some point `x` of the standard apartment of `C`.
3. **Smooth model over `O_K`.** `exists_smoothFullModel_of_vertexInputs` is applied to the
   bounded set `{x}`. Its five inputs are Library theorems:
   `MaximalUnramified.vertexOneStabilizerMaximalBounded`,
   `MaximalUnramified.finiteVertexFixerApproximation`, `maximalBoundedIntegralModel`,
   `IntegralModel.smoothIntersection` and `IntegralModel.finiteIndexEnlargement`. It gives a
   smooth `O_K`-model `M'` of `G_K`. The integral points of `M'` are
   `G(K)^1 ⊓ pointwiseFixer {g • apartmentMap x}`, which unfolds to
   `G(K)^1 ⊓ stabilizer y`. This is KP's `𝒢^1_x` with `𝒢^1_x(O_K) = G(K)^1_x` (Axiom 4.1.20,
   printed p.163 / PDF p.194).
4. **Descent to `𝒪[F]`.** `IntegralModel.exists_descent_of_fixedPoint_integralPoints` is applied
   with the proved `IntegralModel.unramifiedSmoothModelDescent`, to `ρ`, `y` and `M'`. It gives
   a smooth `M : IntegralModel ↥𝒪[F] F G` and an isomorphism `e` from
   `M.baseChangeUnramified` to `M'` over the identity. The lemma's Γ-stability input is
   `unramifiedFixedPointStabilizer`: since `y` is Γ-fixed and `ρ` is semilinear,
   `G(K)^1 ⊓ stabilizer y` is stable under every `rationalConjugate σ`. This is KP §9.2.5
   (printed pp.327–328 / PDF pp.358–359) together with Fact 2.10.16. `e.integralPoints_eq`
   identifies the integral points of `M.baseChangeUnramified` with those of `M'`. This is item 1.
5. **Item 2.** Let `s ∈ S_K(K)^1`. `IntegerValuation.map_mem_characterValuationKernel` places
   its image in `G(K)^1`. The fixed-point clause of step 1 places it in `stabilizer y`.
6. **Item 3.** Take `A = C.S` with `iA = C.i ≫ (innerIso g).hom`. This is a maximal `K`-split
   torus by `IsMaximalSplitTorus.comp_iso`. Let `a ∈ A(K)^1`. Then
   `map_mem_characterValuationKernel` again gives membership in `G(K)^1`.
   `torusUnitApartmentFixation`, applied with the data's `isOmegaCompatible`, shows that
   `C.i a` fixes `apartmentMap x`. This is KP Axiom 4.1.4 (A1), printed p.159 / PDF p.190: the
   bounded subgroup of the apartment torus acts trivially on its apartment. `comp_innerIso_hom`
   and `constantPoint_self` rewrite `iA a` as `g * C.i a * g⁻¹`, and `conj_mem_stabilizer_smul`
   shows that it fixes `g • apartmentMap x = y`.

## Independence

The proof uses none of `SpecialTorusIntegralModelStatement`, `SpecialTorusExistenceStatement`,
`UnramifiedSpecialApartmentStatement` or `ValuationApartmentAxiomsExistenceStatement`, as
premises or through proofs. Each Library theorem used above is a closed proof with standard
axioms. This includes the proof of `unramifiedTorusUnitGaloisFixedPoint`. No Library theorem proves any
of these four propositions. The only theorems that conclude one of them are the conditional
`specialTorusIntegralModelStatement_of_boundedModel` and its packaged form
`specialTorusIntegralModelReductionStatement`, both of which assume the present target. So they cannot
enter these proofs. In the import closure, these propositions and the present target appear only
in their statement modules and as hypotheses of conditional reductions that the proof does not
use. The final theorem's axioms are `propext`, `Classical.choice` and
`Quot.sound`.
