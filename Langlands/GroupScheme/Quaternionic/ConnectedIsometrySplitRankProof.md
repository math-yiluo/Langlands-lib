# Proof: the split rank of `O(q)⁰` equals the Witt index

Author: Worker 350.

Module `Langlands.GroupScheme.Quaternionic.ConnectedIsometrySplitRankProof`.

## Statement proved

`Langlands.GroupScheme.Quaternionic.connectedIsometrySplitRank :
ConnectedIsometrySplitRankStatement.{u}`. Fix a field `K` (any characteristic, finite or
infinite) and a finite-dimensional central division `K`-algebra `D` of degree `degree`. Let
`σ : FirstKindInvolution K D` be an involution of the first kind whose symmetric subspace has
dimension `degree (degree + 1) / 2`, and `q` a nondegenerate `σ`-quadratic form on `D^n` whose
isometry group `O(q)` is smooth. Then
`splitRank (σ.connectedIsometryGroup q) = σ.quadraticWittIndex q` in `ℕ∞`.

## Proof

The proof introduces all binders and applies `le_antisymm` to two bounds.

1. **Upper bound** (`QuadraticTorusWittBound.splitRank_connectedIsometryGroup_le`, module
   `Quaternionic.QuadraticTorusWittBound`): `splitRank O(q)⁰ ≤ σ.quadraticWittIndex q`. Take a
   closed split torus `𝔾ₘ^I → O(q)`. Its universal Laurent point in the unit group of
   `K[ℤ^I] ⊗ M_n(D)` has inverse `∑ₘ Xᵐ ⊗ eₘ` with orthogonal idempotents `eₘ`. The constant
   coefficient of its isometry defect, sandwiched by the sum `f` of the `eₘ` over a
   nonopposite set `S` of weights that represents every nonzero weight up to sign, shows that
   `f Q ᵗf^σ ∈ {X - ᵗX^σ}`. Hence nonzero rows of the `eₘ` (`m ∈ S`) span a totally singular
   subspace of dimension `|S|`. Since the weights generate `ℤ^I`, `|I| ≤ |S| ≤` Witt index.
   The bound for `O(q)⁰` follows from the one for `O(q)` through the closed inclusion
   `O(q)⁰ → O(q)`.
2. **Lower bound** (`FirstKindInvolution.quadraticWittIndex_le_splitRank_connectedIsometryGroup`,
   module `Quaternionic.QuadraticHyperbolicSplitTorus`):
   `σ.quadraticWittIndex q ≤ splitRank O(q)⁰`, using nondegeneracy. Nondegeneracy gives `r`
   mutually orthogonal hyperbolic pairs `(xₖ, yₖ)`, where `r` is the Witt index (module
   `Quaternionic.QuadraticHyperbolicFamily`). Scaling each `xₖ` by `tₖ` and each `yₖ` by
   `tₖ⁻¹` defines a monomorphism `𝔾ₘ^r → GL₁(M_n(D))`. Explicit defect identities show that
   it is an isometry over every coefficient algebra, so it factors through `O(q)`. Since
   `𝔾ₘ^r` is connected, it factors further through `O(q)⁰`, and the image is a closed split
   torus. Hence `r ≤ splitRank O(q)⁰`.

## Scope

All fields are allowed, including finite fields and characteristic `2`, at every universe `u`.
Both bounds use the universal point or points over arbitrary coefficient algebras, never
rational points, so no `[Infinite K]` is needed. The centrality of `D`, the degree equation and
the Tits-type condition on `σ.symmetricSubspace` are hypotheses of the statement that the
proof does not use. Neither bound uses any of the excluded results (`TypeDRankOneSpinStatement`,
`LocalRankOneClassificationStatement`, the local Kneser–Tits statements,
`ClassicalTypeDSpinPresentationStatement`) or anything proved from them. The only axioms are
`propext`, `Classical.choice` and `Quot.sound`.
