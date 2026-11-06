# Component comparisons along specified coefficient-field embeddings

This is an internal construction derived from the published
`AlgebraicallyClosedComponentEquivalences`, `GaloisPointTowerBaseChange`,
`GaloisPointRationalTower`, and actual component-action APIs. It introduces no
external source assertion. All fields and group schemes have the common,
arbitrary universe `u`.

Let `k`, `L`, and `M` be fields, with algebra structures `k → L`, `k → M`, and
`L → M` satisfying `IsScalarTower k L M`. The last algebra structure specifies
an embedding; the scalar-tower hypothesis says it commutes with the maps from
`k`. Write `H_L` and `H_M` for the actual pullbacks of a group scheme `H` over
`Spec k`.

## Actual section extension

In namespace `GaloisPointComparison`, `fieldEmbeddingSectionHom k L M H` is a
homomorphism from the existing rational-section group of `H_L` to that of
`H_M`. The construction first applies `baseChangeSectionHom` along `L → M`
and then the point homomorphism of the actual iterated-to-direct pullback
isomorphism `towerBaseChangeIso k L M H`.

`baseChangeCoeffEquiv_fieldEmbeddingSectionHom` proves that under the existing
coefficient-point comparisons this map is exactly `relativeExtend k L M H`.
Its proof uses the published coefficient formula for the actual tower
isomorphism. The auxiliary coefficient calculation identifies pullback of a
section with `rationalExtend`, applies its coefficient formula, and uses
`coefficientBaseChangeEquiv_extend` and
`coefficientBaseChangeEquiv_rationalCoeffEquiv`.

These constructions and the section naturality law require neither affineness
nor smoothness. For an affine `H`, `fieldEmbeddingSectionHom_conjugate` also
proves compatibility with coefficient automorphisms `σ : L ≃ₐ[k] L` and
`τ : M ≃ₐ[k] M` under the explicit condition

```text
τ (algebraMap L M a) = algebraMap L M (σ a)   for every a : L.
```

The proof applies the injective coefficient comparison, then affine-coordinate
injectivity. On each coordinate the equality is precisely this condition.
`fieldEmbeddingSectionHom_naturality` proves compatibility with every actual
homomorphism `H → H'` over `k`, using the existing naturality law for coefficient
points and the compatible algebra homomorphism `L → M`.

## Equivalence of the full component groups

Suppose in addition that `L` and `M` are algebraically closed and that `H` is
smooth and affine over `k`. There is no algebraic-closedness assumption on `k`
and no characteristic, perfection, or algebraicity restriction on the field
extensions. In namespace `IdentityComponent`,
`componentFieldEmbeddingEquiv k L M H` is a multiplicative equivalence

```text
AlgebraicallyClosedComponents H_L ≃* AlgebraicallyClosedComponents H_M.
```

These are the full actual scheme connected-component groups from the published
library. The equivalence is constructed as the published component base-change
equivalence for `H_L` along `L → M`, followed by `allComponentIso` for the
actual tower isomorphism.

`allComponentMap_ofPoint` identifies the component map of an actual
homomorphism on a rational section. The proof uses the published identification
of that map with the continuous map on connected components.
`componentFieldEmbeddingEquiv_ofPoint` proves that the new equivalence sends
the component of a section `x` to the component of
`fieldEmbeddingSectionHom k L M H x`. Its construction reduces the component
formula to this actual-map lemma and the published base-change formula on
sections. The injective coefficient comparison and the preceding section
calculation identify the resulting section with the specified extension.

`allComponentConjugate_ofPoint` records that the existing full component action
is coefficient conjugation on sections.
`componentFieldEmbeddingEquiv_conjugate` proves equivariance for `σ` and `τ`
under the explicit compatibility condition above.
`componentFieldEmbeddingEquiv_naturality` proves compatibility with an actual
homomorphism over `k`, assuming both its source and target are smooth affine
group schemes. Both laws reduce to the section laws using the published
surjectivity of `allComponentOfPoint` over an algebraically closed field.

## Implementation and scope

Two private structures package the section homomorphism with its proved
coefficient formula and the component equivalence with its proved section
formula. Their private opaque constructors have explicit, kernel-checked Lean
bodies: they construct the maps and prove these laws with an abstract
isomorphism and its coefficient formula. The definitions then specialize these
complete constructions to the published actual tower isomorphism and theorem.
This prevents repeated kernel reduction of the concrete pullback isomorphism;
it adds no axiom or assumed structural theorem.

The comparison depends on the specified embedding `L → M`. The module does
not assert independence from that embedding, compatibility for three successive
coefficient extensions, descent of every invariant component to a rational
point, or a comparison between arbitrary algebraic closures without specified
embedding data. Those are separate obligations. No chosen-algebraic-closure
component module is imported here.
