# The actual valuation of a split torus in its cocharacter lattice and real space

Author: Worker 293.

Let `F : Type u` be a field with the Library's `ValuativeRel`, `TopologicalSpace` and `IsNonarchimedeanLocalField` instances, and let `I : Type u` be any finite type, possibly empty. Write `𝕋 = splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I` for the actual commutative split torus and `rationalPoints 𝕋.toGrp` for its group of rational points. In the namespace `Langlands.GroupScheme.SplitTorusValuation`, the local notation `coords` denotes the existing split point-coordinate equivalence `splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of F)))`, from rational points to `I → Fˣ`. Lean variables for cocharacters are named `c`, because the scoped notation `CategoryTheory.MonObj`, which supplies the group structure on rational points, reserves `η`; below `η` and `c` mean the same thing.

## The integral embedding

For an arbitrary field `k` and an arbitrary commutative group scheme `T` over `Spec k`, `RealTorusSpace.latticeEmbedding T : cocharacterLattice T →+ RealTorusSpace.V T` is the additive map `η ↦ (1 : ℝ) ⊗ₜ[ℤ] η`, the map `TensorProduct.mk ℤ ℝ (cocharacterLattice T) 1` into the existing real space `V T = ℝ ⊗[ℤ] cocharacterLattice T`. Its laws are:

- `latticeEmbedding_apply`: the defining formula `ι(η) = 1 ⊗ η`;
- `latticeEmbedding_zsmul`: `ι(n • η) = (n : ℝ) ⊗ η` for `n : ℤ`;
- `eval_latticeEmbedding`: the existing evaluation `RealTorusSpace.eval T χ` sends `ι(η)` to the real cast of the existing integer pairing `latticePairing T χ η`.

For the split torus (`k` and `I : Type u` with `Finite I`), `splitCocharacterCoordinates_latticeEmbedding` shows that the existing real coordinates `RealTorusSpace.splitCocharacterCoordinates k I` of `ι(η)` are the real casts of the integer coordinates `splitTorus.cocharacterLatticeEquiv k I η`. Since the integer coordinates are injective and the cast `ℤ → ℝ` is injective, `latticeEmbedding_injective` proves that `ι` is injective on the split cocharacter lattice.

## The lattice valuation `ν`

`valuation F I : rationalPoints 𝕋.toGrp →* Multiplicative (cocharacterLattice 𝕋)` sends a point `t` to the cocharacter

`ν(t) = (splitTorus.cocharacterLatticeEquiv F I).symm (fun i => (fieldOrderUnits F (coords t i)).toAdd)`.

Here `Langlands.Plancherel.fieldOrderUnits F : Fˣ →* Multiplicative ℤ` is the existing positive order of field units (its value agrees with `FML.ord`). Multiplicativity follows coordinatewise from multiplicativity of `coords` and `fieldOrderUnits`. The defining coordinate law is `cocharacterLatticeEquiv_valuation`:

`splitTorus.cocharacterLatticeEquiv F I (ν(t)) i = (fieldOrderUnits F (coords t i)).toAdd`.

**Pairing identity.** `latticePairing_valuation` states that, for every actual character `χ : characterLattice 𝕋`,

`latticePairing 𝕋 χ ν(t) = (rationalCharacterValuation 𝕋.toGrp t).toAdd ((rationalCharacters.equivCharacterLattice 𝕋).symm χ)`,

where `Langlands.Plancherel.rationalCharacterValuation` is the published valuation of rational-character values. The proof uses the auxiliary lemma `rationalCharacterEval_characterLatticeEquiv_symm`: evaluating the actual character with integer coordinates `m` on `t` gives `∏ i, coords t i ^ m i`. This lemma is the Library's `splitTorus.pointsEquiv_characterLatticeEquiv_symm`, transported through the global-sections isomorphism that defines `coords`. The pairing is then a finite sum by `splitTorus.latticePairing_eq_sum`. The order of a product of integer powers is the corresponding sum of multiples of the orders, which gives the identity term by term.

**Uniqueness.** `eq_valuation_iff` states that a cocharacter `η` equals `ν(t)` if and only if `latticePairing 𝕋 χ η` equals the same rational-character valuation for every `χ`. The reverse direction uses the Library's proved perfect-pairing instance for the split lattice pairing (`LinearMap.IsPerfPair.bijective_right`). The theorem has no compatibility, perfectness or existence premise.

## The real valuation `ω`

`realValuation F I : rationalPoints 𝕋.toGrp →* Multiplicative (RealTorusSpace.V 𝕋)` is the composite of `ν` with the integral embedding, so `realValuation_toAdd` gives `ω(t) = ι(ν(t)) = 1 ⊗ ν(t)`. Its laws:

- `splitCocharacterCoordinates_realValuation`: the real coordinates of `ω(t)` are `fun i => ((fieldOrderUnits F (coords t i)).toAdd : ℝ)`;
- `eval_realValuation`: for every actual character `χ`, `RealTorusSpace.eval 𝕋 χ ω(t)` is the real cast of the rational-character valuation at `(rationalCharacters.equivCharacterLattice 𝕋).symm χ`;
- `eval_realValuation_eq_rationalNormLogarithm`: the same evaluation equals the corresponding coordinate of the published `Langlands.Plancherel.rationalNormLogarithm 𝕋.toGrp t`, by its proved identity `rationalNormLogarithm_eq_intValuation`.

No second norm or logarithm is constructed.

## Cocharacter evaluation

For an actual cocharacter `η : cocharacterLattice 𝕋`, `cocharacterPoints F I η : Fˣ →* rationalPoints 𝕋.toGrp` is the homomorphism `a ↦ η(a)`. It sends `a` to its rational point of `𝔾_m` (the inverse of the existing `Gm.affinePointsEquiv`) and then applies `rationalPoints.map` of the group-scheme homomorphism `CommGroupScheme.groupHom η`. The point is induced by the actual cocharacter morphism: no coordinate tuple is stipulated. `coords_cocharacterPoints` computes its coordinates, `coords (η(a)) i = a ^ (cocharacterLatticeEquiv F I η i)`, from the Library's `splitTorus.pointsEquiv_cocharacterLatticeEquiv_symm`. Consequently:

- `valuation_cocharacterPoints`: `ν(η(a)) = (fieldOrderUnits F a).toAdd • η`;
- `realValuation_cocharacterPoints`: `ω(η(a)) = ((fieldOrderUnits F a).toAdd : ℝ) ⊗ η`.

`uniformizerUnit F : Fˣ` is the existing order-one uniformizer `LocalField.uniformizer F` as a unit (`Units.mk0` with `uniformizer_ne_zero`). Its order is one (`fieldOrderUnits_uniformizerUnit`, from `fieldOrderUnits_ord` and `LocalField.ord_uniformizer`). Hence `valuation_cocharacterPoints_uniformizer` gives `ν(η(π)) = η` and `realValuation_cocharacterPoints_uniformizer` gives `ω(η(π)) = 1 ⊗ η`.

## Image and kernel

- `valuation_surjective` and `valuation_range`: `ν` is onto the full cocharacter lattice, since `η = ν(η(π))`.
- `mem_realValuation_range` and `realValuation_range`: the range of `ω` is exactly the range of `ι` (as a subgroup of `Multiplicative (V 𝕋)`), with no finite-index qualifier.
- `integralUnitKernel F I` is the pullback under `coords` of `Subgroup.pi Set.univ (fun _ => FML.unitGroup F)`. By `mem_integralUnitKernel`, `t` lies in it if and only if `∀ i, coords t i ∈ FML.unitGroup F`.
- `valuation_ker` and `realValuation_ker`: both kernels equal `integralUnitKernel F I`. The elementwise forms are `mem_valuation_ker` and `mem_realValuation_ker`. The proof uses the Library's `fieldOrderUnits_ker` (the kernel of the order is `FML.unitGroup F`) and, for `ω`, injectivity of `ι`.
- `integralUnitKernel_eq_rationalCommonNormKernel`: this subgroup equals the published `Langlands.Plancherel.rationalCommonNormKernel 𝕋.toGrp`. The proof combines `mem_rationalCommonNormKernel_iff_valuation` with the uniqueness theorem applied to `η = 0`.

These are algebraic identities. No topology on rational points is used.

## Regression specializations

On the one-coordinate torus (`I = PUnit`), `uniformizerPoint F` is the rational point with coordinate `uniformizerUnit F`, obtained from the inverse of the actual coordinate equivalence. The theorems `cocharacterLatticeEquiv_valuation_uniformizerPoint` and `..._inv` show that its lattice valuation has coordinate `+1` and that its inverse has coordinate `-1`. The theorems `splitCocharacterCoordinates_realValuation_uniformizerPoint` and `..._inv` give the same values for the real valuation. For empty `I`, `valuation_eq_one_of_isEmpty` and `realValuation_eq_one_of_isEmpty` show that both values vanish. The theorems `integralUnitKernel_eq_top_of_isEmpty`, `valuation_ker_eq_top_of_isEmpty` and `realValuation_ker_eq_top_of_isEmpty` show that every kernel is the whole rational-point group. All of these use the general maps. No hypothesis restricts the characteristic of `F` or of its residue field, so equal and mixed characteristic are both covered.

## Source correspondence and sign

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (Cambridge, 2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach` (SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`). Section 2.5(b) (PDF page 118, printed 87) defines `ω_T : T(k) → Hom_ℤ(X^*(T)^Θ, ℤ)`. Equation (2.5.1) and Lemmas 2.5.6–2.5.7 are on PDF page 119 (printed 88). The printed formula is `t ↦ (χ ↦ −ω(χ(t)))`. The authors' corrections of 1 November 2024, registered as `kaletha-prasad-2024-corrections` (SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`), PDF page 24, replace this in the fifth line of 2.5(b) by the positive map `t ↦ (χ ↦ ω(χ(t)))`. Both `ν` and `ω` here use the positive convention: their pairing with `χ` is the positive order of `χ(t)`.

For a split torus, `X^*(T)^Θ = X^*(T)` and `Hom_ℤ(X^*(T), ℤ) = X_*(T)`. Then `ν` is the source's `ω_T` with values in `X_*(T)`, and `ω` is (2.5.1) with real instead of rational coefficients. The identity `latticePairing_valuation` is the formula `⟨ω_T(t), χ⟩ = ω(χ(t))`, which the proof of Lemma 2.5.6 uses to determine `ω_T(t)` uniquely; `eq_valuation_iff` formalizes that uniqueness. `valuation_surjective` is the split case of Lemma 2.5.7, whose proof reduces to `𝔾_m`; here surjectivity comes directly from cocharacter evaluation at the uniformizer. The kernel identity matches the description of `ker(ω_T)` in Proposition 2.5.8 (PDF pages 119–120) only as an algebraic set. Maximal boundedness is not formalized.

The real tensor realization `V = ℝ ⊗[ℤ] X_*(T)` and the embedding `ι` are internal constructions implementing the real cocharacter notation of Chapter 6, §6.1.6–6.1.8 and 6.1.11–6.1.12 (PDF pages 231–234, printed 200–203). The real-image statement `realValuation_range` is the split case of Fact 6.1.11's description of the image of `S(k)` as `X_*(S)`.

## Boundaries

The maps are translation vectors for split-torus rational points. No apartment origin, affine space, normalizer action, root-group valuation, apartment or building is constructed. General (non-split) tori, Galois descent, maximal boundedness or compactness of the kernel, and analytic discreteness or cocompactness of the image are not addressed. No identification of `T(F)^0` with `T(F)^1` is asserted.
