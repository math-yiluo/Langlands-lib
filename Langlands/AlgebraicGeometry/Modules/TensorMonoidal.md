# Symmetric monoidal structure on scheme-module sheaves

For every `X : AlgebraicGeometry.Scheme.{u}`, this module installs
`tensorMonoidalCategory : MonoidalCategory X.Modules` and
`tensorSymmetricCategory : SymmetricCategory X.Modules`. These structures
have no additional mathematical hypotheses. The category is the actual
category of module sheaves on `X`; its chosen tensor unit is
`structureSheaf X`.

The instances `presheafTensorMonoidalCategory` and
`presheafTensorSymmetricCategory` expose Mathlib's sectionwise tensor and
symmetry on `X.PresheafOfModules`, through its identification with
`PresheafOfModulesOfCommRing X.presheaf`.

## Construction and coherence

`tensorLocalEquivalences X` is the inverse image of local equivalences of
abelian-group presheaves on the open-set site under the forgetful functor
from module presheaves. Mathlib's module sheafification is a localization
at this class. The imported theorem
`Langlands.Scheme.Modules.tensorLocalEquivalencesIsMonoidal` proves that
this class is monoidal for every scheme. It is installed as a local instance
with its proof; it is not a hypothesis of any exported construction.

`sheafifyTensorUnitIso` identifies sheafification of the presheaf tensor
unit with `structureSheaf X`. It is the component of the invertible
sheafification counit at the structure sheaf. Apply Mathlib's
`LocalizedMonoidal` construction to `sheafify X`, the local equivalences,
and this chosen unit isomorphism. The type synonym reduces to `X.Modules`.
Its tensor, associator, unitors, pentagon and triangle laws are provided by
Mathlib's monoidal localization construction. Its braiding, hexagon laws
and symmetry are provided by Mathlib's braided localization construction.
The named public instances expose those complete structures on `X.Modules`.

`sheafifyMonoidal` and `sheafifyBraided` expose the corresponding strong
monoidal and braided structures on `sheafify X`. These are specializations
of the proved localization interfaces; they do not posit pullback
preservation or any unproved coherence law.

## Comparison with the explicit tensor

For module sheaves `M,N`, `localizedTensorIso X M N` has type
`M ⊗ N ≅ tensorObj M N`. It tensors the inverses of the two sheafification
counits, then applies the strong monoidal comparison of sheafification.
The target is exactly the sheafification of the sectionwise tensor of
`M.val` and `N.val`, as defined in the published `Tensor` module.

`localizedTensorNatIso X : tensor X.Modules ≅ tensorFunctor X` packages
this construction naturally in both factors. It uses the product of the
inverse counit natural isomorphisms followed by sheafification's tensor
comparison natural isomorphism. Thus the localized tensor agrees, up to a
specified natural isomorphism, with the existing genuine sheaf tensor.
No definitional equality between these tensor bifunctors is asserted.
Consumers can keep using `tensorObj`, `tensorMap`, and `tensorPow` from
`Tensor`, or use monoidal notation with this comparison.

## Provenance and scope

Worker 59 authored this internal categorical construction. It specializes
the pinned Mathlib modules `CategoryTheory.Localization.Monoidal.Basic`
and `CategoryTheory.Localization.Monoidal.Braided`, using the published
`Tensor` construction and unconditional `TensorLocalizationProof` theorem.
Their paired explanations record the underlying sheaf-theoretic provenance;
this module does not claim a new translation of a literature theorem.

This unit constructs the symmetric monoidal category and strong braided
sheafification. Compatibility of the explicit tensor unitors and swap with
the localized structure is not asserted here. Pullback tensor-comparison
invertibility, pullback associativity, unit and symmetry compatibility,
and strong symmetric monoidal pullback with identity/composition
compatibility remain separate obligations of the parent task.
