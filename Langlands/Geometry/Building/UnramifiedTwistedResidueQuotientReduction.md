# Reduction of the twisted residue quotient to model, radical and descent inputs

This is an internal reduction, derived from published Library results and three published
statements. All objects have arbitrary universe `u`. The Prop-valued statement
`UnramifiedTwistedResidueQuotientInputsReductionStatement` says that
`UnramifiedTwistedResidueQuotientStatement` follows from
`UnramifiedParahoricModelStatement`, `UnramifiedUpstairsRadicalRootGenerationStatement`
(KP 8.4.12) and `UnramifiedTwistedReductiveQuotientDescentStatement`. The theorem
`unramifiedTwistedResidueQuotientInputsReduction` proves it. It does not prove any of the three
inputs.

## Notation

`F` is a nonarchimedean local field, `K = inertiaFixedField F`, `O = fixedFieldIntegers F`,
`Ω` the residue field of `O` and `𝓀[F]` that of `F`. `B` is a supplied building datum over `K`
for `G_K` with reduced building `B(G_K)`, and `A` is a semilinear apartment datum on `B`.
The point `y` satisfies `c σ • A.action σ y = y` for all `σ`, and `θ_σ(g) = c σ σ(g) (c σ)⁻¹`.
`E` is an `UnramifiedZeroDatum` with zero subgroup `G(K)^0`.

## Proof of the generic form `exists_twistedResidueQuotient_of_inputs`

1. Write `y = g · x` with `x` in the apartment. `UnramifiedParahoricModelStatement` with
   `Ωa = {x}` gives a relative-component model `D` over `O` with neutral points
   `P = G(K)^0 ∩ G(K)_y`. `exists_isReductiveQuotient` (module `ReductiveQuotientExistence`)
   gives reductive quotient data `Q`. It applies because `Ω` is algebraically closed.
2. `P` is `θ_σ`-stable (`twisted_mem_zeroPoints_fixer`). Here `G(K)^0` is stable under
   coefficient conjugation (`UnramifiedZeroDatum.rationalConjugate_mem_zeroPoints`) and normal.
   The fixer of `y` is stable by `SemilinearApartmentData.twistedAction_smul`.
3. The descent statement gives `R` over `𝓀[F]` and `e : R_Ω ≅ Q.quotient`. Define
   `q = (map e⁻¹) ∘ Q.parahoricReduction` and `θP(g) = θ_φ(g)`. The θ clause holds by
   definition, and the Frobenius clause is the descent conclusion. Surjectivity follows from
   `parahoricReduction_surjective` over the Henselian ring `O` with perfect residue field,
   together with `rationalPoints_map_inv_hom` (module `Transport.Package`).
   The fixer bound is `P ≤ G(K)_y`.
4. Kernel. Choose a regular `x₀` with `x` in its facet closure, and set
   `Y₀ = g · facet(x₀)`. This chamber has a closure presentation through `y`. If `q p = 1`,
   then `p ∈ Q.positivePoints` by `ker_parahoricReduction`. `radicalPreimage_fixes_facet`
   shows that `p` fixes `Y₀` pointwise. It translates the model back to `x` with `conjModel`,
   which composes the generic isomorphism with the inner automorphism of `g⁻¹`. It then applies
   the published `unramifiedRadicalPreimage_le_zeroFixer_facet` (module
   `UnramifiedRadicalChamberFixation`). That lemma uses KP 8.4.12 at `Ω = {x}` and shows that
   the radical preimage of a smooth model at `x` fixes `facet(x₀)` pointwise. For an
   arbitrary chamber `Y` through `y`, the published
   `IntegerValuationBuildingData.kernel_stabilizes_of_transitive` (same module) concludes. It
   writes `Y = h Y₀` with `h ∈ P` by transitivity; then `h⁻¹ p h` also lies in the kernel and
   preserves `Y₀`, so `p` preserves `Y`.
5. Transitivity is `UnramifiedZeroDatum.exists_zeroPoints_fixer_smul_chamber_eq` (module
   `SharpChamberClosureOrbit`) for `G(K)^0 ∩ G(K)_y = P`.

`unramifiedTwistedResidueQuotient_of_inputs` specializes the generic form to the building
datum `UnramifiedBuildingDescent.buildingData` and the semilinear datum
`UnramifiedBuildingDescent.semilinearData` of the target. It obtains `E` from
`Kottwitz.nonempty_unramifiedZeroDatum_baseChanged`.

## Remarks

- The subgroup `P` is the neutral parahoric `G(K)^0 ∩ G(K)_y` from the model statement, not
  the full fixer of `y`.
- The heartbeat limits are raised for the generic form (6400000), the translated radical bound
  the zero-subgroup conjugation helper and the specialization
  `unramifiedTwistedResidueQuotient_of_inputs` (1600000 each). Their elaboration is expensive but finite.
- No proof of any of the ten downstream statements excluded by Task 6572 is used.
