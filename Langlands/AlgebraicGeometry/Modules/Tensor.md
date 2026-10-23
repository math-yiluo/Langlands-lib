# Tensor products of module sheaves on schemes

For every `X : AlgebraicGeometry.Scheme.{u}`, this module defines a tensor
bifunctor on Mathlib's actual category `X.Modules`, with module carriers in
universe `u`. All declarations are in `Langlands.Scheme.Modules`. No flatness,
quasicoherence, or local freeness hypothesis is imposed.

## Construction and interface

`sheafify X` is module sheafification over the identity map of the structure
presheaf of rings. Its right adjoint is the existing
`AlgebraicGeometry.Scheme.Modules.toPresheafOfModules X`.
`sheafifyAdjunction X` supplies this adjunction, and `sheafifyForgetIso X` is
its invertible counit on sheaves.

`tensorFunctor X : X.Modules × X.Modules ⥤ X.Modules` first forgets both
sheaves to presheaves, takes Mathlib's sectionwise tensor product, and applies
`sheafify X`. Thus its input presheaf has sections
`M(U) ⊗[𝒪_X(U)] N(U)` and the usual tensor product of restriction maps.
`tensorObj M N` is the resulting sheaf and `tensorMap f g` is the bifunctor's
map on a pair of morphisms. The functor structure includes its identity and
composition laws.

`tensorSheafificationIso M N` explicitly compares the tensor object with
sheafification of `PresheafOfModulesOfCommRing.Monoidal.tensorObj M.val N.val`.
It is the identity isomorphism because these objects are definitionally equal.
This comparison establishes agreement with the usual sheafification
construction without assuming a tensor universal property.

`tensorHomEquiv M N P` is the adjunction equivalence

```
(tensorObj M N ⟶ P) ≃ (M.val ⊗ N.val ⟶ P.val).
```

The target consists of morphisms of module presheaves out of the sectionwise
tensor. The file does not introduce a separate type of bilinear sheaf maps or
claim a formal equivalence with such a type.

`structureSheaf X` is exactly `SheafOfModules.unit X.ringCatSheaf`.
`tensorComm M N` sheafifies the presheaf symmetry. Its naturality is the
shared lemma `tensorComm_naturality`, obtained by applying sheafification to
presheaf braiding naturality. This lemma was moved unchanged from
[RigidifiedTensorSymmetry](../Picard/RigidifiedTensorSymmetry.md) so that
foundational tensor proofs can reuse it. `tensorLeftUnitor M` and
`tensorRightUnitor M` sheafify the respective presheaf unit isomorphism and
then compose with the counit isomorphism. These are actual isomorphisms;
this file does not yet package them into a monoidal structure.

`tensorPow M 0` is `structureSheaf X`, and
`tensorPow M (n + 1)` is `tensorObj M (tensorPow M n)`.
These are right-associated nonnegative powers with a final unit factor.
`tensorPowMap f n` recursively tensors `f` with its lower power, starting
with the identity of the structure sheaf. No negative powers are defined.

Two local instances expose Mathlib's existing symmetric monoidal structure
on `PresheafOfModulesOfCommRing.{u} X.presheaf` through the definitionally equal
scheme presheaf category. They impose no hypotheses and install no monoidal
instance on `X.Modules`.

## Source and provenance

The original mathematical source is the Stacks Project, Section 17.16
(tag 01CA), opening definition of the tensor product of sheaves by
sheafification and the following symmetry discussion. The construction here
specializes that definition from ringed spaces to schemes. The source's
bilinear characterization and associativity discussion are not asserted as
additional proved results in this file.

The source is registered as `stacks-module-tensor-products-2026-10-21`,
*Stacks Project - Tensor products of sheaves of modules (HTML snapshot
2026-10-21)*. The retained HTML file has SHA256
`825127394e5828c3a56f5134b8823afba20547d7ba5173f624b2f9556a058e34`.
The relevant text is the opening portion of Section 17.16 before Lemma 17.16.1.

The adjunction, comparison, and unit isomorphisms are internal categorical
packaging of this construction. They use the pinned Mathlib module
`Algebra/Category/ModuleCat/Presheaf/Sheafification.lean` for sheafification,
its adjunction, and the invertible counit, and
`Algebra/Category/ModuleCat/Presheaf/Monoidal.lean` for sectionwise tensors,
symmetry, and unit isomorphisms. Tensor powers and their maps are internal
recursive definitions from the tensor and unit just constructed.
The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.

## Remaining obligations

An associator and the symmetric monoidal coherence laws, as well as tensor
and unit comparisons for scheme pullback and their coherence, remain separate
units. The published proposition
`Langlands.Scheme.Modules.tensorLocalEquivalencesIsMonoidalStatement`
records the prerequisite for the intended monoidal localization route;
it is not assumed or used by this module. This definition contribution alone
does not complete the tensor and monoidal pullback task.
