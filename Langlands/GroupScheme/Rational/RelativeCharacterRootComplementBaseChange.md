# Scalar extension of the intrinsic character/root complement

Author: Worker 1278.

This internal construction and its accompanying lemmas supply the scalar-extension step for the intrinsic character/root complement. They prove that the rational complement implies the real complement in the existing full character space. They do not prove the geometric rational complement or the complete `RelativeCharacterRootComplementStatement`.

## Tensor-space construction

`Langlands.LinearAlgebra.rationalRealTensorEquiv M` is the real-linear equivalence

`ℝ ⊗[ℚ] (ℚ ⊗[ℤ] M) ≃ₗ[ℝ] ℝ ⊗[ℤ] M`

for any abelian group `M`. It specializes Mathlib's `TensorProduct.AlgebraTensorModule.cancelBaseChange` to the scalar tower `ℤ → ℚ → ℝ`. It sends `r ⊗ (q ⊗ m)` to `(q • r) ⊗ m`, and its inverse sends `r ⊗ m` to `r ⊗ (1 ⊗ m)`. The two accompanying simp lemmas state these formulas. No freeness, torsion-freeness, or finite-generation hypothesis is used.

The construction is internal tensor linear algebra rather than a separate assertion from the reductive-group literature. Its provenance is the existing scalar tower and Mathlib's tensor cancellation equivalence; the geometric source assertions remain those of the imported Library target.

## Compatibility lemmas

`baseChange_range` proves that scalar extension of the range of an `R`-linear map equals the range of its scalar extension, for commutative rings `R` and `A` with an `R`-algebra structure on `A`. The proof factors the map through its range. Extension of scalars preserves the surjectivity of the range restriction, so this factorization has the same image as the extended range inclusion. This uses right exactness and needs no flatness assumption.

`map_ratSpan_baseChange` identifies the image of the extended rational span under `rationalRealTensorEquiv` with the real span of the actual vectors `1 ⊗ m`. The proof rewrites scalar extension and linear images of spans, then applies tensor cancellation on the generating vectors.

`rationalRealTensorEquiv_naturality` says that tensor cancellation commutes with scalar extension of any integral linear map. The proof checks pure tensors. `map_range_baseChange_rat_real` combines naturality with `baseChange_range` and surjectivity of the cancellation equivalence, identifying the extended rational image with the real image.

`isCompl_baseChange` proves that complementary submodules of a module over a commutative ring remain complementary after extension to a commutative algebra. The proof extends the projection onto the first summand along the second. The extended projection fixes the extension of the first summand and kills that of the second, proving disjointness. Each pure tensor decomposes using the two original complementary projections, proving that the sum is the whole tensor space. This split argument needs neither flatness nor finite-dimensionality.

## Actual group-scheme specialization

`map_rationalCharacterRestrictRat_range_baseChange` specializes the image comparison to the existing actual character-restriction map along any homomorphism of group schemes over a field. Its right side is precisely the range of the existing `rationalCharacterRestrictReal`, not a replacement restriction construction.

`map_relativeRootSpan_baseChange` specializes the span comparison to the set of all actual relative roots of a homomorphism from a commutative group scheme into an affine group scheme. Its right side is precisely the existing `RealTorusSpace.relativeRootSpanReal`. The proof retains every root in the given set, including nonreduced root systems.

Finally, `Langlands.GroupScheme.relativeCharacterRootComplementReal_of_rat` takes

`IsCompl (relativeRootSpan i) (rationalCharacterRestrictRat i).range`

and proves

`IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range`.

It extends the rational complement, transports it by `rationalRealTensorEquiv (characterLattice T)`, and rewrites the two submodules using the actual-construction comparisons. The field has arbitrary universe `u`. The only geometric typeclass hypothesis is the existing affineness required to define the root set; connected reductivity, maximal splitness, and any root-system realization are not needed for this implication. In particular the proof imposes no positive-rank hypothesis and preserves the full central character directions. The rational complement hypothesis is discharged by the separate intrinsic geometric proof when assembling the final task target.
