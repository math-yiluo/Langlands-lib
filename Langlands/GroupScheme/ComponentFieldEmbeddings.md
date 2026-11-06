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
not assert independence from that embedding, descent of every invariant
component to a rational point, or a comparison between arbitrary algebraic
closures without specified embedding data. Those are separate obligations.
No chosen-algebraic-closure component module is imported here.

## Identity and tower composition

These intrinsic laws are derived from the actual coefficient and section maps
above. They introduce no additional external source assertion.

For fields `k`, `L`, `M`, `N`, choose algebra structures for every arrow
`k → L`, `k → M`, `k → N`, `L → M`, `L → N`, and `M → N`. Assume the four
scalar-tower laws for `k,L,M`, `k,L,N`, `k,M,N`, and `L,M,N`. These hypotheses
express compatibility of the specified embeddings, including equality of
successive and direct embeddings from `L` to `N`.

In namespace `GaloisPoint`, `relativeExtend_self` proves identity coefficient
extension is the identity homomorphism. `relativeExtend_comp` proves the
homomorphism equality from successive to direct coefficient extension. It
identifies the composite of the two actual algebra maps with the direct one
using `IsScalarTower.algebraMap_apply`, and applies the existing
`affinePointMap_comp` law.

In namespace `GaloisPointComparison`, `fieldEmbeddingSectionHom_self` and
`fieldEmbeddingSectionHom_comp` prove the corresponding equalities for actual
sections of the direct base changes of `H`. They apply the injective
coefficient-point comparison and the proved coefficient formula for
`fieldEmbeddingSectionHom`, then the preceding coefficient laws. These section
and coefficient laws require no affineness or smoothness of `H`, and no
algebraic-closedness of any field.

Assume additionally that `L`, `M`, and `N` are algebraically closed and `H`
is smooth and affine over `k`. In namespace `IdentityComponent`,
`componentFieldEmbeddingEquiv_self` identifies the comparison for the identity
embedding with the identity multiplicative equivalence.
`componentFieldEmbeddingEquiv_trans` identifies the successive comparisons
from `L` to `M` to `N` with the direct comparison from `L` to `N`, as an
equality of multiplicative equivalences on the full actual component groups.
Both proofs use the surjectivity of the section-to-component map over an
algebraically closed field, the section formula of the component comparison,
and the preceding section laws.

No algebraic-closedness condition is imposed on `k`; no algebraicity,
separability, perfection or characteristic restriction is added. All laws
concern the specified compatible embeddings. They do not assert independence
from those embeddings or descent of Galois-invariant components to rational
points. The unit is an internal derivation from the actual map APIs, with no
new external source assertion.
