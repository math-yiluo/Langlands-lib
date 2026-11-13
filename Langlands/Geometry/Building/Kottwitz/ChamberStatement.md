# KP Corollary 11.7.5: rational surjectivity and the chamber quotient

`Langlands.Geometry.Building.Kottwitz.ChamberStatement` states Corollary 11.7.5 of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), printed p. 434 (PDF p. 465). The November 2024 corrections do not alter this corollary. This is a Prop-valued statement awaiting proof.

For every nonarchimedean local field `F` and connected reductive `F`-group `G`, put `K = inertiaFixedField F = UnramifiedClosure F`, `E = SeparableClosure F`, `I = Gal(E/K)`, `Γ = Gal(K/F)` and `A = π₁(G)_I`. The first conjunct asserts unconditionally that the constructed rational Kottwitz homomorphism `reductiveKottwitzRational F G hG : G(F) → A^Γ` is surjective.

The second conjunct is **conditional on supplied building data over `K`**. It quantifies over an `F`-torus inclusion `iT : T → G` whose base change is a maximal `K`-split torus; a `Γ`-stable equipollence class `D` of root-datum valuations for the integer order of `MaximalUnramified.valuation F`; its centralizer datum `C`; and the compatibility condition V 6 (`h6`). These give `B = UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6`, with `hGK` supplied by the Library theorem that connected reductivity is preserved by field extension. This clause does not assert existence of these data.

For every chamber `Cch : Set B.ReducedBuilding` stable under every coefficient Galois action, and every existing datum `d : ZeroSubgroupDatum i j`, let

- `P = G(F)_Cch` be the setwise stabilizer: the inverse image of `MulAction.stabilizer G(K) Cch` under the actual coefficient extension homomorphism `rationalExtend F K G`;
- `N = d.zeroSubgroup.subgroupOf P = G(F)_Cch ∩ G(F)^0`, viewed inside `P`, where `G(F)^0` is the existing Library zero subgroup.

The statement concludes that `N` is normal in `P` and that there exists a group isomorphism `e : P/N ≃ A^Γ` satisfying `e([x]) = κ_G(x)` for every `x ∈ P`. This equation specifies the isomorphism induced by the constructed Kottwitz map.

The chamber stability premise uses exactly `(UnramifiedBuildingDescent.semilinearData … hD).action`. By `UnramifiedBuildingDescent.semilinearData_action_apply`, this is the coefficient action `KPApartmentData.galoisQuotientAction`; it is determined by the supplied class and the group defined over `F`. A general semilinear action is not an input. `B.IsChamber` is the Library chamber predicate on its reduced building, and Galois stability is equality of the image of the chamber with itself, not pointwise fixation.

Lean writes the additive group `A^Γ` multiplicatively at the homomorphism and quotient interfaces. No Kottwitz map, kernel equality, surjectivity or normality is assumed. Both conjuncts allow equal and mixed characteristic, with no split, quasi-split, tame, rank or residue-characteristic restriction on `G`. The source's `dim(f) ≤ 1` assumption holds for the finite residue field of `F`. The supplied-data formulation of the chamber clause is the adaptation to the Library building interface allowed by the task; the rational surjectivity clause has no building premise.
