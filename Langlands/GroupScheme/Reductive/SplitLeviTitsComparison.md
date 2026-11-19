# Tits obstructions of a group and of the derived group of a split-torus centralizer

Author: Worker 5662.

This module proves the Brauer-class part of the comparison of Tits obstructions with the
anisotropic kernel (Tits, *Représentations linéaires irréductibles d'un groupe réductif
sur un corps quelconque*, J. reine angew. Math. 247 (1971), §3.4 and §5.5). Let `d` be
Galois pinning data of `G` over `F`, with `K/F` Galois, and let `L : d.LeviComparison s ι e`
be Levi comparison data (module `Reductive/SplitLeviComparison`) for `ι : D ⟶ G`. For
every weight `λ` of `G` fixed by the full star action:

`α_G(λ) = α_D(λ|T_D)`,

where `α` is Task 7603's actual Tits obstruction (`GaloisPinningData.titsObstructionValue`,
packaged as `titsObstruction` on the star-fixed weights). For the Library's actual
anisotropic kernel this is clause 2 of Task 7605.

The proof follows the representation-theoretic route of Tits. Let `ρ` be a representation of
`G_K` of highest weight `λ` and let `B` be its Tits algebra. Let `X₀` be the isotypic subspace
of `ρ` for `λ|S`. A rational idempotent of `B` projects onto `X₀`. On `X₀` the group `D_K`
acts by an actual representation `ρ₀` in which `λ|T_D` is a weight of multiplicity one
dominating every other weight. Task 7603's maximal-weight theorem (Tits, Proposition 3.4)
identifies `α_D(λ|T_D)` with the class of the compression of `B`. The corner theorem then
identifies that class with `[B] = α_G(λ)`. No smoothness, perfectness or characteristic
assumption is made, and neither maximality of `S` nor anisotropy of `D` is used.

## Galois stability of the isotypic subspace

- `SplitTorusDatum.galoisRepresentation_splitCharacter`: the Galois action on characters of
  the base-changed split torus is trivial. This is the published
  `galoisRepresentation_of_isSplitTorus`.
- `SplitTorusDatum.isTwistedStable_isotypicSubspace`: given Galois intertwiners
  `P σ : ρ → ρ^σ`, every isotypic subspace `s.isotypicSubspace ρ μ` is stable under
  `u ↦ σ⁻¹(P σ u)` (Task 7603's `IsTwistedStable`). The intertwiner `P σ` maps the
  `χ`-character space of `ρ|S` into that of `ρ^σ|S`. Conjugation by `σ⁻¹` maps it into the
  `σ⁻¹·χ`-character space of `(ρ^σ)^{σ⁻¹}|S`, and that representation has the universal
  matrix of `ρ`. Finally `σ⁻¹·χ = χ`, since `S` is split. The proof uses Task 7603's
  `conjugate_mem_characterSpace_restrict_galoisTwist`,
  `characterSpace_restrict_eq_of_universalMatrix_eq` and `universalMatrix_galoisTwist_inv`.

## Coordinate subrepresentations and compression

Let `ρ` be a representation of `D_K` on `Kⁿ` and let `B, C` be stable split coordinates of a
stable subspace, with coordinate subrepresentation `ρ₀ = restrictCoordinates ρ B C`.

- `map_mul_rect_left`, `map_mul_rect_right`: a `K`-linear functional applied entrywise
  commutes with constant rectangular factors.
- `universalMatrix_restrictCoordinates`: the universal matrix of `ρ₀` is `C U(ρ) B`. This is
  the published `restrictCoordinates_affineMatrix` at the universal point.
- `coefficientMatrix_restrictCoordinates`: the coefficient matrices of `ρ₀` are
  `C X_φ(ρ) B`.
- `coefficientMatrix_restrictCoordinates_eq`: suppose `f` fixes a stable subspace `V`
  containing the columns of `B`. Then `X_φ(ρ₀) = (C f) X_φ(ρ) B`, because `X_φ(ρ) B` has
  columns in `V` (Task 7603's `coefficientMatrix_mulVec_mem`).
- `titsAlgebra_restrictCoordinates_le_compressed`: hence the Tits algebra of `ρ₀` lies in the
  compression `compressed Bk (C f) B` of any algebra `Bk` containing the Tits algebra of `ρ`.
- `intertwines_galoisTwist_restrictCoordinates`: let `P` intertwine `ρ` with `ρ^σ`, and let
  `f` satisfy `P f = σ(f) P`, `f B = B` and `B C f = f`. Then `σ(C f) P B` intertwines `ρ₀`
  with `ρ₀^σ`. The proof is a matrix identity between universal matrices over
  `K ⊗[F] O(D)`. It uses the intertwining identities of `P` and of `B`, and the fact that
  `galoisTensor` acts on scalar matrices through `σ`.

## The comparison

For Levi comparison data `L`:

- `pairing_weightRestriction`: pairing a restricted character with a simple coroot of `D`
  is the pairing with the corresponding simple coroot of `G` (fields `coroot_eq` and the
  published `latticePairing_precomp`). `isDominantWeight_weightRestriction`: restriction
  preserves dominance.
- `GaloisPinningData.pairing_starAction_weight_coroot` and
  `weightRestriction_starAction`: when the simple coroots of `D` span its cocharacter
  lattice, restriction intertwines the full star actions. The proof compares pairings with
  the simple coroots, using the field `star_eq` and the accepted clause-1 lemma
  `TitsIndexData.aut_pairing_weightEquiv_coroot`. `isStarFixedWeight_weightRestriction`
  follows.
- `titsObstructionValue_eq_of_isDominantWeight`: the comparison for dominant star-fixed
  `λ`. The steps:
  1. Choose `ρ` of highest weight `λ` (published `splitHighestWeightClassification`) and
     Galois intertwiners `P σ` (Task 7603's `exists_intertwiner_galoisTwist`). Put
     `B = titsAlgebra ρ ≤ twistedFixed P`, whose `K`-span is everything.
  2. `α_G(λ) = [toCSA P B]` by Task 7603's `titsObstructionValue_of_maximal` applied to `ρ`.
     The weight `λ` has multiplicity one and is maximal, since the positive root monoid is
     pointed.
  3. Restrict to `ρ' = ρ|D_K`. The `P σ` remain intertwiners (Task 7603's
     `intertwines_restrict_galoisTwist`). So `titsAlgebra ρ' ≤ twistedFixed P = B`
     (`titsAlgebra_eq_twistedFixed`).
  4. The isotypic subspace `X₀` for `λ` is twisted-stable. Task 7603's
     `exists_adapted_idempotent` then gives an idempotent `f ∈ B` with image `X₀` that fixes
     `X₀`.
  5. Take stable coordinates `B_c, C_c` of `X₀` (`LeviComparison.exists_isotypicCoordinates`)
     and let `ρ₀` be the coordinate representation of `D_K`. With `F₀ = C_c f` and
     `E₀ = B_c`, we have `F₀ E₀ = 1` and `E₀ F₀ = f ∈ B`.
  6. The compressed intertwiners `σ(F₀) P σ E₀` intertwine `ρ₀` with its Galois twists. The
     Tits algebra of `ρ₀` lies in `compressed B F₀ E₀`. The weight `λ|T_D` has multiplicity
     one in `ρ₀` and is maximal (module `Reductive/SplitLeviIsotypicWeights`).
  7. `titsObstructionValue_of_maximal` for `D` gives
     `α_D(λ|T_D) = [toCSA (compressed B F₀ E₀)]`, and Task 7603's
     `isBrauerEquivalent_toCSA_compressed` (built on the corner theorem
     `isBrauerEquivalent_cornerCSA`) identifies this class with `[toCSA P B]`.
- `titsObstructionValue_eq`: the comparison for every star-fixed `λ`. Write `λ = a − b`
  with `a = dominantPart λ` and `b = a − λ`, both dominant and star-fixed. Apply Task
  7603's `titsObstructionValue_eq_sub` to `G` and to `D` (restriction preserves dominance and
  star-fixedness), and the dominant case to `a` and `b`.
- `starFixedRestriction L hspan'`: restriction as an additive map from the star-fixed
  weights of `G` to those of `D`.
- `titsObstruction_comp_starFixedRestriction`: for simply connected `G` and `D`,
  `α_D ∘ restriction = α_G` as additive maps on star-fixed weights.

## The actual anisotropic kernel

`TitsIndexData.AnisotropicKernelIndex.titsObstruction_eq p hG λ`: let `G` be simply
connected with actual Tits index data `d` and Library anisotropic kernel `p`. The kernel
`p.kernel` is the actual derived subgroup of the actual centralizer of the actual maximal
split torus, and it is simply connected by the published
`AnisotropicKernelIndex.isSimplyConnected`. For every star-fixed weight `λ`:

`d.pinning.titsObstruction hG λ =
  p.index.pinning.titsObstruction (p.isSimplyConnected hG)
    (p.leviComparison.starFixedRestriction _ λ)`.

By `leviComparison_weightRestriction`, the restricted weight is the published actual
restriction `p.comparison.weightRestriction λ`.

The provenance is internal. The module combines Task 7603's Tits-algebra and obstruction
modules, Task 7605's corner algebra, clause-1 and Levi-comparison modules, and published
Library results. It formalizes the argument of Tits 1971, §3.4 and §5.5, for the actual
group schemes.
