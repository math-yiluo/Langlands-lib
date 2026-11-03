# The character grading of the coordinate algebra of a group with a torus action

Module `Langlands.GroupScheme.Rational.TorusUnipotence.CoordinateGrading`, namespace
`Langlands.GroupScheme.TorusUnipotence`.

Let `k` be a field and `H` a group scheme over `Spec k` whose structure morphism is affine.
Let `S` be a split torus over `k` and `b : AutomorphicAction S.toGrp H` an action of `S` on `H`
by group automorphisms. Write `A = CharacterUnits.Coord H` for the coordinate algebra and
`A_χ = CoordinateWeights.weightSpace b χ` for its `χ`-eigenspace, for `χ` in the character
lattice of `S`. The module proves three facts about these character spaces. They are the
grading hypotheses of `isUnipotent_of_graded` in `MatrixCoefficients`, with `coordComul H` and
`coordCounit H` the comultiplication and counit defined there:

* `1 ∈ A_0`;
* `ε (A_χ) = 0` for `χ ≠ 0`, where `ε = coordCounit H` is evaluation at the identity;
* `Δ (A_χ) ⊆ ∑_α A_α ⊗ A_{χ - α}`, where `Δ = coordComul H` (the hypothesis `hΔ`).

## Statements

* `le_iSup_map₂_of_iSupIndep` (pure linear algebra). Let `K` be a field, `B` a `K`-vector space,
  `Γ` an additive abelian group, and `𝒜 : Γ → Submodule K B` with `⨆ χ, 𝒜 χ = ⊤`. Let
  `W : Γ → Submodule K (B ⊗ B)` be an independent family (`iSupIndep W`) such that
  `x ⊗ y ∈ W (α + β)` whenever `x ∈ 𝒜 α` and `y ∈ 𝒜 β`. Then for every `χ`,
  `W χ ≤ ⨆ α, map₂ (TensorProduct.mk K B B) (𝒜 α) (𝒜 (χ - α))`.
* `mul_isPointedEquivariant b`: the multiplication `μ[H.X] : H.X ⊗ H.X ⟶ H.X` is equivariant
  (`IsPointedEquivariant`) from the diagonal action `(ofGroup b).prod (ofGroup b)` to
  `ofGroup b`. It also sends the base point `(1, 1)` to `1`. Here `ofGroup b` is the Library's
  `PointedCoordinateWeights.PointedAction.ofGroup b`, the action `b` with the group law of `H`
  forgotten.
* `tensorPullback_mul`: the Library's `PointedCoordinateWeights.tensorPullback μ[H.X]`, i.e. the
  pullback along multiplication read in the tensor coordinates `A ⊗ A`, equals `coordComul H`.
* `one_mem_weightSpace_zero b`: `(1 : A) ∈ A_0`. No torus hypothesis is needed.
* `coordComul_mem_iSup b hS hf`: suppose `S` is a split torus (`hS : IsSplitTorus S.toGrp`) and
  `f ∈ A_χ`. Then
  `coordComul H f ∈ ⨆ α, map₂ (TensorProduct.mk k A A) (A_α) (A_{χ - α})`.
* `coordCounit_eq_zero b hS hχ hf`: suppose `S` is a split torus, `χ ≠ 0` and `f ∈ A_χ`. Then
  `coordCounit H f = 0`.

## Proof

*Linear algebra.* Put `V ψ = ⨆ α, map₂ mk (𝒜 α) (𝒜 (ψ - α))`. The hypothesis on pure tensors
gives `V ≤ W` pointwise. The pure tensors `x ⊗ y` span `B ⊗ B`. Expanding `x` and `y` along
`⨆ χ, 𝒜 χ = ⊤` (`Submodule.iSup_induction`) shows that every `x ⊗ y` lies in `⨆ ψ, V ψ`, so
`⨆ ψ, V ψ = ⊤`. An independent family that dominates a family with supremum `⊤` equals it
(`iSupIndep.le_iff_eq_of_iSup_eq_top`). So `V = W`, and in particular `W χ ≤ V χ`.

*Equivariance.* The action of `s` on `H × H` is computed componentwise: it sends `(g, h)` to
`(b.act s g, b.act s h)`. Since `b` acts by group homomorphisms (`AutomorphicAction.act_mul_right`),
`b.act s (g * h) = b.act s g * b.act s h`. The base-point condition is `1 * 1 = 1`.

*The comultiplication.* `tensorPullback μ[H.X]` unfolds through `tensorCoordinates_toAlgHom`,
`PointedCoordinateWeights.coordinates_comp` and `tensorPresentation_hom` to the coordinates of a
product point. The point is the product of the images of the universal point of `H` under the two
inclusions `A → A ⊗ A`. This is the definition of `CharacterUnits.comul H`, and `coordComul H`
is that map read over `k`. The remaining identification is `rfl`.

*Grading.* Let `a = ofGroup b`. The Library's `tensorPullback_mem_tensorWeightSpace`, applied to
the equivariant map `μ[H.X]`, sends `f ∈ A_χ` into `tensorWeightSpace a a χ`, the image of the
`χ`-eigenspace of `Coord (H.X ⊗ H.X)` in `A ⊗ A`. By `tensorPullback_mul` this is
`coordComul H f`. Apply `le_iSup_map₂_of_iSupIndep` with `𝒜 χ = A_χ` and
`W = tensorWeightSpace a a`:
* `⨆ χ, A_χ = ⊤` holds because `A` is the internal direct sum of the `A_χ`, by
  `CoordinateWeights.coordinateWeightDecomposition`.
* `W` is independent by `tensorWeightSpace_iSupIndep`. Its input is the internal decomposition of
  `Coord (H.X ⊗ H.X)` given by `pointedCoordinateDecomposition` for the action `a.prod a`.
* `tmul_mem_tensorWeightSpace` gives the pure-tensor condition.

*Weight of `1`.* `A_χ` consists of the `f` with `f(s · g) = χ(s) f(g)` for all `k`-algebras `R`
and all `R`-points `s` of `S` and `g` of `H` (`CoordinateWeights.IsEigenfunction`). For `f = 1`
both sides of the condition for `χ = 0` equal `1`, because the value of the zero character is
`1` (`Lie.characterValue_zero`).

*The counit.* Let `f ∈ A_χ` with `χ ≠ 0`, and let `p_χ = gradedProj A_• χ` be the projection
onto `A_χ` along the internal direct sum decomposition of `A`, with the decomposition chosen
from `CoordinateWeights.coordinateWeightDecomposition`. The counit `coordCounit H` is
`Lie.coordinateOrigin H`, so its kernel is the augmentation `I = CoordinateWeights.augmentation H`.
The same Library theorem shows that `I` is the internal direct sum of its eigenspaces
`I_ψ = CoordinateWeights.augmentationWeightSpace b ψ`, and each `I_ψ` lies in `A_ψ`. Hence `I` is
contained in `⨆ ψ, I_ψ`, viewed in `A`. On this supremum `ε ∘ p_χ` vanishes, by
`Submodule.iSup_induction`: on `I_χ` the projection is the identity and its values lie in `I`;
on `I_ψ` with `ψ ≠ χ` the projection is `0`. Apply this to `z = f - ε(f) · 1 ∈ I`. Since
`p_χ f = f`, and `p_χ 1 = 0` because `1 ∈ A_0` and `χ ≠ 0`, this gives
`0 = ε (p_χ z) = ε f`.

## Provenance

This is an internal interface for the proof of
`Langlands.GroupScheme.RelativeRoot.TorusActionUnipotenceStatement`, and no source states it in
this form. The underlying facts are elementary. The multiplication of `H` is equivariant for the
diagonal action of `S`, so its comorphism preserves the character gradings, with `A ⊗ A` graded by
total character. The identity of `H` is fixed by `S`, so evaluation there preserves the gradings,
with `k` in degree `0`. The constants have weight `0`. The character decompositions it relies on are the Library's
`CoordinateWeights.coordinateWeightDecomposition` and
`PointedCoordinateWeights.pointedCoordinateDecomposition`, used as published.
