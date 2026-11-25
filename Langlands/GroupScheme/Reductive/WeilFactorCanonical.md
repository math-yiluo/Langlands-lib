# The canonical algebra isomorphism attached to an isomorphism of Weil restrictions

Module `Langlands.GroupScheme.Reductive.WeilFactorCanonical`, namespace
`Langlands.GroupScheme.WeilFactor`. It imports
[`WeilFactorUniquenessReduction`](WeilFactorUniquenessReduction.md). Like that module, it does
not prove [`WeilFactorIdempotentRigidityStatement`](WeilFactorIdempotentRigidityStatement.md).
The results take a proof `hR` of it as a hypothesis, together with reductivity and almost simple
geometric fibres for the groups involved.

## Purpose and provenance

Provenance: derived/internal. Conrad, *Reductive group schemes*, Proposition 6.4.4 (p.232),
asserts that an isomorphism `R_{S′/S}(G′) ≃ R_{S′′/S}(G′′)` arises from a unique pair
`(α, f)`. The pair is therefore canonical and compatible with composition, which is what makes
étale descent of the pair possible. This module provides the algebra half of that canonicity:
a chosen isomorphism `α` for each `Φ`, characterized by a property, unique for that property,
and compatible with identities and composition.

## Declarations

`A`; finite projective étale `A`-algebras `B`, `B''`, `B'''`; affine group schemes `G`, `G''`,
`G'''`, locally of finite type, over `Spec B`, `Spec B''`, `Spec B'''`.

- `transportNat_id`, `transportNat_comp`: `transportNat` (from
  [`WeilFactorTransfer`](WeilFactorTransfer.md)) preserves identities and composition.
- `conj_refl`, `conj_trans`: conjugation by `Iso.refl` is the identity, and conjugation by
  `Φ₁ ≪≫ Φ₂` is conjugation by `Φ₁` followed by conjugation by `Φ₂`.
- `transfer_refl`: transfer along `Iso.refl` is the identity on idempotents.
- `transfer_trans`: transfer along `Φ₁ ≪≫ Φ₂` is transfer along `Φ₁` followed by transfer along
  `Φ₂`.
- `IsWeilAlgEquiv hR hred'' hsimple'' Φ α` (a `Prop`): for every `A`-algebra `T`, every
  `φ : B →ₐ[A] T` and every graph idempotent `e` of `φ`, the transfer of `e` along `Φ` is the
  graph idempotent of `φ ∘ α`.
- `weilAlgEquiv hR hred hsimple hred'' hsimple'' Φ : B'' ≃ₐ[A] B` (definition): an
  isomorphism with this property, chosen from `exists_algEquiv_transfer`.
- `weilAlgEquiv_spec`: `weilAlgEquiv Φ` has the property.
- `IsWeilAlgEquiv.eq`, `weilAlgEquiv_unique`: the property determines `α`. Two such `α`
  transfer the diagonal idempotent of `B ⊗_A B` to graph idempotents of the same element, so
  they agree by `IsGraphIdempotent.algHom_eq`.
- `weilAlgEquiv_refl`: `weilAlgEquiv (Iso.refl _) = AlgEquiv.refl`.
- `weilAlgEquiv_trans`: for `Φ₁ : R_{B/A}(G) ≅ R_{B''/A}(G'')` and
  `Φ₂ : R_{B''/A}(G'') ≅ R_{B'''/A}(G''')`,
  `weilAlgEquiv (Φ₁ ≪≫ Φ₂) = (weilAlgEquiv Φ₂).trans (weilAlgEquiv Φ₁)`, an isomorphism
  `B''' ≃ B''` followed by `B'' ≃ B`.

## Scope

The group part (that `comparisonIso` together with `α` recovers `Φ`) and compatibility with base
change of `A` are not in this module.
