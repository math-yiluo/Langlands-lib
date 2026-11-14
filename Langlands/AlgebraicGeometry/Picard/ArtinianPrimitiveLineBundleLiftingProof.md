# Proof: lifting primitive line bundles along elementary Artinian thickenings

Module `Langlands.AlgebraicGeometry.Picard.ArtinianPrimitiveLineBundleLiftingProof`.
Authors: Worker 2971 and Worker 5704 (Task 5704).

## Statement proved

The theorem `Langlands.AbelianScheme.artinianPrimitiveLineBundleLifting` proves the
published proposition
`Langlands.AbelianScheme.ArtinianPrimitiveLineBundleLiftingStatement.{u}` exactly, with
no hypotheses. That proposition is in module
`Langlands.AlgebraicGeometry.Picard.ArtinianPrimitiveLineBundleLiftingStatement`.

The proposition says the following. Let `φ : B' → B` be a surjection of local Artinian
rings in `Type u` with `maximalIdeal B' * ker φ = ⊥`. Let `A` be an abelian scheme over
`Spec B'`, put `j := Spec.map (CommRingCat.ofHom φ)`, and let `A₀ := (baseChange j).obj A`.
Let `L` be a line bundle on `A₀` with `m^*L ≅ p1^*L ⊗ p2^*L` on `A₀ ×_B A₀`, where `p1`
and `p2` are the projections and `m := p1 * p2` is the group law. Then there is a line
bundle `L'` on `A` with `(LineBundle.pullback (pullback.fst A.X.hom j)).obj L' ≅ L`. This
is the obstruction-vanishing step (claim 2) in the proof of Proposition 6.7 of
Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed., Chapter 6, printed
pp. 117–118. The statement's Markdown gives the source dictionary.

## Implemented proof

The proof is one term. It applies a published reduction to two published proofs.

1. `Langlands.AbelianScheme.artinianPrimitiveLineBundleLiftingReduction`, from
   [`ArtinianPrimitiveLineBundleLiftingFromPrerequisites`](ArtinianPrimitiveLineBundleLiftingFromPrerequisites.md),
   proves `ArtinianPrimitiveLineBundleLiftingReductionStatement.{u}`. That proposition is
   the implication

   ```text
   SquareZeroObstructionMorphismNaturalityStatement.{u} →
     ArtinianH2PrimitiveInjectivityStatement.{u} →
       ArtinianPrimitiveLineBundleLiftingStatement.{u}
   ```

   It follows the source's argument. Let `y` be the class of `L`, and let `P₀` be the
   special fibre `(A ×_{B'} A) ×_{B'} Spec B` of `P := A ×_{B'} A`. Write `g_f : P₀ ⟶ A₀`
   for the base change of each `f ∈ {μ, p₁, p₂}`. Naturality, applied to each `f`, and
   additivity show that `μ^* − p₁^* − p₂^*` on the ideal `H²` sends the obstruction of `y`
   along `A₀ ⊂ A` to the obstruction of `g_μ^* y − g_{p₁}^* y − g_{p₂}^* y` along
   `P₀ ⊂ P`. Transport of the isomorphism `m^*L ≅ p1^*L ⊗ p2^*L` along the canonical map
   `P₀ ⟶ A₀ ×_B A₀` shows that this class is `0`. By injectivity, the obstruction of `y`
   vanishes, and `SquareZeroPicardObstruction.lineBundle_lift_iff` gives the lift.
2. `Langlands.AlgebraicGeometry.Picard.squareZeroObstructionMorphismNaturality`, from
   [`SquareZeroObstructionMorphismNaturalityProof`](SquareZeroObstructionMorphismNaturalityProof.md),
   proves the first hypothesis,
   `Langlands.AlgebraicGeometry.Picard.SquareZeroObstructionMorphismNaturalityStatement.{u}`.
   It says square-zero Picard obstructions are natural under morphisms of thickenings.
3. `Langlands.AbelianScheme.artinianH2PrimitiveInjectivity`, from
   [`ArtinianH2PrimitiveInjectivityProof`](ArtinianH2PrimitiveInjectivityProof.md),
   proves the second hypothesis,
   `Langlands.AbelianScheme.ArtinianH2PrimitiveInjectivityStatement.{u}`. It says
   `μ^* − p₁^* − p₂^*` is injective on the ideal `H²` of the elementary thickening. Its
   proof reduces to the field case on the residue fibre, where `H² ≅ ⋀² H¹` and a
   Künneth decomposition of `H²(A_k × A_k, 𝒪)` give injectivity.

All three inputs are in the same universe `u` as the target. The module adds no lemmas,
definitions or options.

## Check

The approved Lean service compiled the module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` with zero errors and zero warnings (diagnostic
`4ac67053-9a56-4044-afa0-d61a92b91643`). The theorem uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Constraint check

The task forbids routing through `PicardZeroArtinianLiftingStatement`,
`FiniteTypeDualSchemeGeometryStatement`, `RelativeDualSchemeGeometryStatement`,
`FiniteTypeSmoothFamilyAbelianRepresentabilityStatement` and
`SmoothFamilyAbelianRepresentabilityStatement`. I scanned the source of all 2,092
`Langlands` modules in the import closure of this file at Library commit `7f5b5f04`. None
contains `PicardZeroArtinianLifting`, `DualSchemeGeometry` or
`SmoothFamilyAbelianRepresentability`.

## Provenance

This proof is an internal assembly of published Library results. The mathematical route
is the proof of Proposition 6.7 in Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*,
3rd ed., Chapter 6, printed pp. 117–118 (PDF pp. 130–131), registered as literature ID
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`.
