# The pair-factor clause for Henniart's composite map

Lean module: `Langlands.Global.Factors.HenniartCompositeFactorPair`.

Worker 5130, Task 5230. Internal derived lemma. Its only sources are published
Library results and the companion transport modules named below.

`PoleComparison.pairFactorCompatibility_henniartCompositeMap` proves the
pair-factor clause (`Correspondence.LatticeMap.PairFactorCompatibility`) at `K` for
the composite `henniartCompositeMap F E c v h K f T`, for every nontrivial additive
character `ψ` of `K`. Its hypothesis is the pair-factor clause of `T` at `F_v`
(`RelativeIsometryPairFactorCompatibility`) for every nontrivial additive character
of `F_v`. After `subst h`, `f : K ≅ F_v`. The proof goes as follows.

* `ψ_v` is `ψ` transported to `F_v` along `f`
  (`PadicField.ConductorTransport.additiveCharacter`), so `ψ_v(f x) = ψ(x)`. A
  self-dual measure for `ψ` on `K` exists by
  `Correspondence.existsUnique_localSelfDualMeasure`. If `ν` is self-dual for `ψ`,
  its pushforward `ν_v` is self-dual for `ψ_v` by `AbelianTransport.isSelfDual_iff`.
* Elements of the transported Weil image are `completionWeilLatticeEquiv x₀` with
  `x₀` in the Weil image at `F_v`. `henniartCompositeMap_apply` evaluates the
  composite on them as `completionSupercuspidalLatticeEquiv (T x₀)`.
* L-factors: `unitaryPairLFactor_restrictUnitaryLatticeEquiv` (from
  `HenniartCompositeFactorWeil`, with `localDegreeInt_completionWeilEquiv`)
  identifies the Weil-side L-factor at `K` with the one at `F_v`. Worker 5731's
  `isUnitaryPairLFactor_unitaryLatticeEquiv_iff_transport`
  (`UnitaryPairFactorTransport`) moves the supercuspidal L-factor relation from
  `F_v` (with `ψ_v`, `ν_v`) to `K`.
* Epsilon factors: take a reciprocity family `eC`, an assignment `ε` and a proof
  `hεK` that they form a local-constant system on `K`. The hypothesis at `F_v` is
  applied to `transportFamily F_v K f⁻¹ eC` and `transportAssignment F_v K f⁻¹ ε`,
  which form a local-constant system by `isSystem_transportAssignment`
  (`NonabelianSystemFieldTransportSystem`). It gives one certificate `e` for both
  sides at `F_v`, and `e` is moved back to `K`:
  - Weil side: `completionWeilEquiv` equals `weilEquiv F_v K f⁻¹`, so Worker
    5731's `FieldTransport.isUnitaryPairEpsilonFactor_transport`
    (`NonabelianSystemFieldTransportPairEpsilon`) applies, with `ψ ∘ f⁻¹ = ψ_v`
    holding by definition.
  - Supercuspidal side: Worker 5731's
    `isUnitaryPairEpsilonFactor_unitaryLatticeEquiv_iff_transport`.
