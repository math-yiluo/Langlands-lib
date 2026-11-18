# Low-degree cohomology vanishing for groups of multiplicative type

`multiplicativeTypeLowDegreeVanishing` proves the published proposition `MultiplicativeTypeLowDegreeVanishingStatement.{u}`. It holds for every commutative ring `R` and every group scheme `H` over `Spec R` satisfying `RelativeMultiplicativeType.IsMultiplicativeType H`. Take any `R`-module `M` and any natural module representation `ρ` of `H` on `A ↦ A ⊗_R M`. Every regular one-cocycle is then the coboundary of a single element of `M`. Every regular two-cocycle is the coboundary of a natural one-cochain. No splitness of `H` is assumed, and no finiteness, freeness, flatness or projectivity of `M`. This is the degree-one and degree-two case of Conrad, *Reductive group schemes*, Appendix B.2, Remark B.2.4.

## Structure of the proof

The proof follows the flat base-change argument of Conrad's Proposition B.2.2. It descends membership in the image of a differential, not a chosen primitive.

1. **Splitting cover.** `exists_flat_isDiagonalizable` produces, for every prime `p` of `R`, an `R`-algebra `K` with three properties:
   - `K` is flat over `R`;
   - some prime of `K` lies over `p`;
   - the base change of `H` to `Spec K` is diagonalizable.

   It comes from the published `IsMultiplicativeType.exists_affine_chart`. That result gives an open affine `Spec R₀ → Spec R` containing `p` and a faithfully flat `R₀ → R'` splitting `H`. Then `K = R'`. Flatness of `R → R₀` comes from the open immersion, and the prime over `p` from surjectivity on spectra of `R₀ → R'`.
2. **Coboundaries as range membership.** `H` is affine (`IsMultiplicativeType.isAffineHom`), so the published `AffineCochainCoordinates` gives a universal point `g` over the coordinate algebra `O`, and a universal pair `(g₁, g₂)` over `O ⊗_R O`. Two `R`-linear differentials are defined:
   - `zeroDifferential ρ : M → O ⊗ M` sends `m` to `g • (1 ⊗ m) - 1 ⊗ m`;
   - `oneDifferential ρ : O ⊗ M → (O ⊗ O) ⊗ M` sends `w` to `g₁ • (g₂^* w) + g₁^* w - (g₁g₂)^* w`.

   `OneCochain.isCoboundary_of_mem_range` and `TwoCochain.isCoboundary_of_mem_range` show the following. If the universal value of a one-cochain (two-cochain) lies in the range of the corresponding differential, the cochain is a coboundary. In degree two the primitive is the natural one-cochain `oneCochainOfCoordinates` of a preimage. These are the published criteria `oneCoboundary_iff_generic` and `twoCoboundary_iff_generic`.
3. **Range membership after base change.** Let `K` be such that the base change of `H` to `Spec K` has vanishing low-degree cohomology. Then:
   - `oneCocycle_mem_range_lTensor` shows that `1 ⊗ c(g)` lies in the range of `K ⊗ zeroDifferential ρ`, for every one-cocycle `c`;
   - `twoCocycle_mem_range_lTensor` shows that `1 ⊗ c(g₁, g₂)` lies in the range of `K ⊗ oneDifferential ρ`, for every two-cocycle `c`.

   The cocycle is base-changed with the published `OneCochain.baseChange` / `TwoCochain.baseChange`, which preserve the cocycle property. Vanishing over `K` gives a primitive. In degree one this is an element `m'` of `K ⊗ M`. In degree two it is a natural one-cochain `b'` over `K`.

   Write `P` for `O` in degree one and `O ⊗_R O` in degree two. The coboundary equation is evaluated over `K ⊗_R P` at the images of the corresponding universal points. After applying `scalarExtensionCancel`, the lemmas of `RestrictedTestEvaluation` rewrite every term as `restrictedEval` of a tensor in `K ⊗_R (P ⊗_R M)`. Injectivity of this evaluation map gives the equation in that tensor module.

   In degree two, `b'` is first replaced by a coordinate tensor `w' ∈ K ⊗_R (O ⊗ M)`. Surjectivity of `restrictedEval` produces `w'` from the value of `b'` at the universal point over `K ⊗_R O`. The internal claim shows that `b'` is the evaluation of `w'` everywhere. The argument extends each point by `tensorTestLift` and uses naturality of `b'`, of `scalarExtensionCancel` and of `Lie.affineBaseChangeEquiv`.
4. **Descent.** The split case is the published `hasVanishingLowDegreeCohomology_of_isDiagonalizable`. With the splitting cover of step 1, it supplies for every prime `p` the hypotheses of `mem_range_of_flat_cover` (`FlatRangeDescent`). Hence the universal values lie in the ranges over `R` itself, and step 2 concludes.

## Provenance

The theorem is the target statement of Task 7643, published as `Langlands.GroupScheme.Cohomology.MultiplicativeTypeLowDegreeVanishingStatement`. The route is Conrad's: regular cochains correspond to coordinate tensors, the differentials are linear maps on them, and vanishing descends along a flat cover by base change. The Lean proof makes the descent elementary. It descends membership of a single element in a linear range along a pointwise flat cover. It does not use a general faithfully flat descent of cohomology. The intermediate lemmas are internal derived results and add no source assertion.
