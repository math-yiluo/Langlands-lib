# Actual torsion counts and native multiplication rank

This internal specialization connects the existing actual torsion `Level` to Mathlib's native `Scheme.Hom.finrank` of the actual multiplication morphism. It computes no numerical degree and assumes none.

`torsionLiftsEquiv` identifies the actual torsion `Level` over any field with the subtype of actual scheme maps whose composite with multiplication is the unit section. It composes the existing kernel-section equivalence with the universal property of the actual kernel pullback square. The maps are composition with the actual kernel inclusion and the pullback lift with identity second component.

`natCard_level_eq_multiplicationFinrank_at_unit` holds over any separably closed field when the field image of the level is nonzero. It first uses `torsionSectionsEquiv` to identify the actual torsion level with sections of the actual multiplication kernel. The generic finite étale section-count theorem identifies this count with the native rank of the kernel structure morphism. Finally, `kernel_isPullback_scheme` and native finite-flat base-change invariance identify this rank with the rank of multiplication at the unit point. The finiteness and étaleness hypotheses are obtained from the existing actual multiplication theorems.

`multiplicationFinrank_eq` proves that this rank is independent of the target point over any field. The underlying abelian scheme over the field is connected by geometric connectedness. The actual multiplication morphism is finite and étale, so its native rank is locally constant and hence constant on this connected space.

`natCard_level_eq_multiplicationFinrank` combines these two results to count actual torsion by multiplication rank at any point of the target abelian variety. A point of `Spec K` exists because `K` is a field; it is used only to select the unit point for the first comparison.

The provenance is the already implemented actual-kernel section comparison, the actual kernel pullback square, and the directly used Mathlib rank and connectedness theorems. The numerical formula `n^(2*g)` still requires a geometric degree argument. No relative dimension, supplied rank formula, comparison module or basis enters this bridge.
