# Galois-twisted stability of the highest-weight flag

This internal module belongs to the additivity step of the Tits obstruction
(Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un
corps quelconque*, J. reine angew. Math. 247 (1971), Proposition 3.4, pp. 204–205).
In that proposition, Galois-stable sub-`G`-modules `X ⊇ Y` of a
`D`-representation give a `D`-`G`-module `X/Y`. The module proves that the
flag `Y = highestRadical ρ ν ≤ X = highestGenerated ρ ν` of
`Reductive/HighestWeightSubquotient` is stable under the twisted Galois action
`u ↦ σ⁻¹(P σ · u)` coming from intertwiners `P σ : ρ → ρ^σ`, when `ν` is
star-fixed. This is the hypothesis `IsTwistedStable` of
`Algebra/GaloisTwistedFlags`.

## Setting

- `G` is an affine group scheme over a field `k`.
- `d : GaloisPinningData k K G` is a Galois pinning, so its maximal torus is
  defined over `k` and split over `K`.
- `ρ` is a matrix representation of `G_K` on `Kⁿ`. `ρ^σ = galoisTwist σ ρ` is
  its Galois twist.
- Weight spaces are taken for `d.toSplitPinning`. `d.galoisAction` is the
  ordinary Galois action on the root datum and `d.starAction` is the star
  action.
- `d.IsStarFixedWeight ν` means `(d.starAction σ).weightEquiv ν = ν` for every
  `σ`.

## Declarations

### Stability and Galois twists (`MatrixRepresentation`)

- `IsStableSubspace.galoisComap_of_galoisTwist`: if `V` is stable for `ρ^σ`,
  then `galoisComap σ V = {w | σ(w) ∈ V}` is stable for `ρ`. The proof uses
  the universal-matrix criterion `isStableSubspace_iff_universalMatrix` and
  `universalMatrix_galoisTwist_map_untwist`. It is the argument used inside
  `IsIrreducible.galoisTwist`, stated on its own.
- `IsStableSubspace.of_universalMatrix_eq`: stability depends only on the
  universal matrix.
- `IsStableSubspace.galoisComap_galoisTwist`: if `V` is stable for `ρ`, then
  `galoisComap σ⁻¹ V = σ(V)` is stable for `ρ^σ`. This applies the first lemma
  to `σ⁻¹` and `ρ^σ`, using `universalMatrix_galoisTwist_inv`
  (`(ρ^σ)^{σ⁻¹}` and `ρ` have the same universal matrix).

### Multiplicities in stable subspaces (`SplitPinning`)

- `exists_finrank_inf_representationWeightSpace`: for a stable subspace `V`
  of a representation `ρ` of a split group, there is a representation `τ`
  such that `dim (V ∩ ρ_μ) = dim τ_μ` for every weight `μ`. The
  representation `τ` is the subrepresentation on `V`, in the published
  coordinates `exists_subspace_split_coordinates`, `restrictCoordinates` and
  `intertwines_restrictCoordinates`. The inclusion `B` has left inverse `C`.
  By `Intertwines.map_weightSpace_eq_inf_range` it maps `τ_μ` onto
  `ρ_μ ∩ range B = V ∩ ρ_μ`, and it is injective.

### Weyl invariance and the flag (`GaloisPinningData`)

- `finrank_inf_representationWeightSpace_weyl`: for stable `V` and `w` in the
  Weyl group, `dim (V ∩ ρ_{wμ}) = dim (V ∩ ρ_μ)`. This is
  `finrank_representationWeightSpace_weyl` applied to the representation `τ`
  above.
- `representationWeightSpace_weyl_le_highestGenerated`:
  `ρ_{wν} ≤ highestGenerated ρ ν`. Since `X` contains `ρ_ν`, the dimension of
  `X ∩ ρ_{wν}` equals `dim ρ_ν = dim ρ_{wν}`.
- `highestRadical_inf_representationWeightSpace_weyl`:
  `highestRadical ρ ν ∩ ρ_{wν} = 0`. Its dimension equals
  `dim (Y ∩ ρ_ν) = 0` (`highestRadical_inf_weightSpace`).
- `exists_weyl_smul_eq_galoisAction_smul`: if `(starAction σ) ν = ν`, then
  `galoisAction σ • ν = w • ν` for some Weyl element `w`. Write
  `w₀ · galoisAction σ = starAction σ` with `w₀` in the Weyl group
  (`exists_weyl_mul_galoisAction_eq_starAction`) and take `w = w₀⁻¹`.
- `isTwistedStable_highestGenerated`: let `ν` be star-fixed and let each
  `P σ` intertwine `ρ` with `ρ^σ`. Then `X = highestGenerated ρ ν` satisfies
  `IsTwistedStable P X`.
  - The subspace `V = {v | σ⁻¹(P σ v) ∈ X}` is the preimage under `P σ` of the
    `ρ^σ`-stable subspace `σ(X)`, so it is `ρ`-stable.
  - For `v ∈ ρ_ν`, `P σ v` lies in `(ρ^σ)_ν`
    (`SplitPinning.Intertwines.mulVec_mem_weightSpace`). Write
    `ν = galoisAction σ • (galoisAction σ⁻¹ • ν)`. By
    `representationWeightSpace_galoisTwist_smul`, `σ⁻¹(P σ v)` then lies in
    `ρ_{galoisAction σ⁻¹ • ν}`.
  - Star-fixedness at `σ⁻¹` makes that weight a Weyl conjugate `wν`. So
    `σ⁻¹(P σ v) ∈ ρ_{wν} ≤ X`.
  - Hence `ρ_ν ≤ V`. The minimality of `X` (`highestGenerated_le`) gives
    `X ≤ V`, which is the claim.
- `isTwistedStable_highestRadical`: under the same hypotheses, with every
  `P σ` invertible, `Y = highestRadical ρ ν` satisfies `IsTwistedStable P Y`.
  - Let `Z = {z | σ(z) ∈ P σ (Y)}`, the set of vectors `σ⁻¹(P σ y)` with
    `y ∈ Y`. It is `ρ`-stable because `P σ (Y)` is `ρ^σ`-stable
    (`IsStableSubspace.map`). It lies in `X` by the previous theorem, since
    `Y ≤ X`.
  - Suppose `z = σ⁻¹(P σ y)` lies in `ρ_ν`. Then `σ(z) = P σ y` lies in
    `(ρ^σ)_{galoisAction σ • ν}` (`conjugate_mem_representationWeightSpace`).
  - Since `(P σ)⁻¹ P σ = 1`,
    `SplitPinning.Intertwines.mem_weightSpace_of_leftInverse` gives
    `y ∈ ρ_{galoisAction σ • ν} = ρ_{wν}` for a Weyl element `w`.
  - So `y ∈ Y ∩ ρ_{wν} = 0`, hence `z = 0`. Thus `Z ∩ ρ_ν = 0`.
  - The maximality of `Y` (`le_highestRadical`) gives `Z ≤ Y`. Every
    `σ⁻¹(P σ u)` with `u ∈ Y` lies in `Z`.

### Packaged statement (`Langlands.GroupScheme`)

- `HighestWeightTwistedStabilityStatement`: for every Galois extension `K/k`
  (`IsGalois k K`), affine `G` locally of finite type over `k`, Galois pinning
  `d`, representation `ρ` of `G_K` on `Kⁿ`, star-fixed `ν`, and invertible
  intertwiners `P σ : ρ → ρ^σ`, both `highestGenerated ρ ν` and
  `highestRadical ρ ν` are `IsTwistedStable P`.
- `highestWeightTwistedStability` proves it from the two theorems above.

Neither theorem uses continuity or a cocycle condition on `σ ↦ P σ`.
