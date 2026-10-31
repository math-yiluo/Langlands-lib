# Concrete images of original nonunital modules

Worker 633. This is an internal derived construction in the existing original
category `Langlands.Algebra.NonUnitalModuleCat`. It bundles the published stable
range with its inherited action and retains the actual subtype inclusion and
the original map with codomain restricted to that range.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 633 read the module conventions on printed pages 5–7 / PDF pages 11–13
and A.VI.2 on printed page 262 / PDF page 268. The source defines an image as
the least subobject through which the morphism factors; property 4 identifies
it with the kernel of the cokernel, and the image half of property 5 supplies
the epi-mono factorization. The explicit original-range construction here is
internal derived content, rather than a separately numbered book lemma.

The Library note `notes/renard/appendix-a-corrections.md` was read. Its discussion
of the insufficient full-subcategory closure criterion does not enter this
construction. The published ambient Abelian instance is used for a general
categorical image fact after proving epimorphism of the concrete factor map.

## Scope and original structures

Let `A : Type uA` have `[NonUnitalRing A]`, let
`M,N : NonUnitalModuleCat.{uA,uM} A`, and let `f : M ⟶ N`.
These are the only inputs. The ring and carrier universes are independent.
Every concrete object constructed here has its carrier in `Type uM`.
The original ring may be noncommutative and may have no unit. Zero rings,
zero carriers and degenerate actions are included, including the zero action
on a nonzero additive group over a unital ring. No unit-action law,
idempotentedness, nondegeneracy, field, nontriviality or finiteness condition
is assumed.

The imported `NonUnitalModuleKernels` supplies `f.rangeSubmodule`, its original
preimage membership criterion, the concrete kernel and cokernel and their
actual maps. `NonUnitalModuleSubobject` supplies the monomorphism of the
existing subtype inclusion. `NonUnitalModuleAmbientAbelianProof` supplies
the named Abelian instance on this same original category. Its preadditive
projection is the published pointwise structure. None of those dependencies
is changed or reconstructed.

## The concrete factorization

`concreteImage f` is exactly `NonUnitalModuleCat.of A f.rangeSubmodule`.
The theorem `concreteImage_carrier` identifies its carrier definitionally
with `{n : N // ∃ m : M, f m = n}`. Here and in the code, categorical
evaluation is exposed by `NonUnitalModuleHom.toAddMonoidHom`.

`concreteImageι f` is the existing `f.rangeSubmodule.subtype`.
`concreteImageι_apply` evaluates this inclusion as the subtype value.
`concreteImage_smul_coe` states that the action inherited by the range
has underlying value `a • n.val` for the given original action on `N`.
Both identities hold by reflexivity.

`factorThruConcreteImage f` sends `m` to `⟨f m, ⟨m, rfl⟩⟩`.
The proofs of additivity and compatibility with the original action are
subtype extensionality applied to the corresponding laws of `f`.
`factorThruConcreteImage_apply` records this exact subtype value, and
`factorThruConcreteImage_apply_coe` records its value in `N`.
`factorThruConcreteImage_ι` proves
`factorThruConcreteImage f ≫ concreteImageι f = f` pointwise.

`factorThruConcreteImage_surjective` uses the original preimage stored in
each range vector. `epi_factorThruConcreteImage` proves categorical
epimorphism directly: evaluate an equality of composites at such a preimage
to prove equality at every range vector. `mono_concreteImageι` reuses
the published monomorphism of an actual subtype inclusion.

## Mathlib's image universal property

`concreteImageMonoFactorisation f` is a Mathlib `Limits.MonoFactorisation f`
whose object, mono and source map are exactly `concreteImage f`,
`concreteImageι f` and `factorThruConcreteImage f`.
`concreteImageStrongEpiMonoFactorisation f` retains these same fields.
It upgrades the proved epimorphism to a strong epimorphism using
`CategoryTheory.strongEpi_of_epi` in the published ambient Abelian category.

`concreteImageIsImage f` is the actual Mathlib
`Limits.IsImage (concreteImageMonoFactorisation f)`, constructed by
`StrongEpiMonoFactorisation.toMonoIsImage`. This uses the strong
epimorphism's lifting property against the monomorphism of any other
factorization. Its universal property is an output of the construction.

For every other `F : MonoFactorisation f`, the theorem
`concreteImageIsImage_lift_ι` says that the universal lift followed by `F.m`
equals `concreteImageι f`. The theorem
`factorThruConcreteImage_isImage_lift` says that the source factor map
followed by that lift equals `F.e`. The theorem
`concreteImageIsImage_lift_unique` proves uniqueness of a lift commuting
with the inclusion by cancellation of `F.m`.

## Selected categorical image

`imageIsoConcrete f : Limits.image f ≅ concreteImage f` is
`IsImage.isoExt` applied to Mathlib's selected image witness and the
constructed concrete witness. Its four compatibility identities are:

| Theorem | Identity |
| --- | --- |
| `imageIsoConcrete_hom_ι` | `iso.hom ≫ concreteImageι f = Limits.image.ι f` |
| `imageIsoConcrete_inv_ι` | `iso.inv ≫ Limits.image.ι f = concreteImageι f` |
| `factorThruImage_imageIsoConcrete_hom` | `Limits.factorThruImage f ≫ iso.hom = factorThruConcreteImage f` |
| `factorThruConcreteImage_imageIsoConcrete_inv` | `factorThruConcreteImage f ≫ iso.inv = Limits.factorThruImage f` |

Here `iso` abbreviates `imageIsoConcrete f`. These are Mathlib's four
`IsImage.isoExt` compatibility laws specialized to the exhibited maps.

## Concrete kernel of the concrete cokernel

`mem_kernelSubmodule_concreteCokernelπ` states
`n ∈ (concreteCokernelπ f).kernelSubmodule ↔ n ∈ f.rangeSubmodule`.
Its proof is exactly the already published
`concreteCokernelπ_eq_zero_iff f n`, with kernel membership unfolded
definitionally. Thus it is precisely the zero-coset criterion for the
existing quotient by the stable range.

`concreteImageIsoKernelCokernel f` is an isomorphism
`concreteImage f ≅ concreteKernel (concreteCokernelπ f)`.
Both maps retain the underlying vector in `N` and use the two directions
of that zero-coset criterion to change its membership proof. Their additive
and original-action laws follow by subtype extensionality and reflexivity.
Both inverse identities are reflexive pointwise.

`concreteImageIsoKernelCokernel_hom_apply_coe` and
`concreteImageIsoKernelCokernel_inv_apply_coe` state that both underlying
maps retain the vector. The theorems
`concreteImageIsoKernelCokernel_hom_ι` and
`concreteImageIsoKernelCokernel_inv_ι` show that both directions commute
with the actual subtype inclusions into `N`.

## Selected Abelian image and checks

Mathlib's `CategoryTheory.Abelian.image f` is
`kernel (cokernel.π f)`, using selected categorical kernels and cokernels.
`abelianImageIsoConcrete f` composes Mathlib's
`Abelian.imageIsoImage f` with `imageIsoConcrete f`.
`abelianImageIsoConcrete_hom_ι` identifies its composite with the concrete
inclusion as `kernel.ι (cokernel.π f)`;
`abelianImageIsoConcrete_inv_ι` gives the inverse inclusion identity.
The two source-map identities are
`abelianFactorThruImage_abelianImageIsoConcrete_hom` and
`factorThruConcreteImage_abelianImageIsoConcrete_inv`. They follow by
cancelling the appropriate monic inclusion and using the factorization
equations. Thus this comparison also retains both arrows.

The final Lean section checks the complete unapplied types of all eleven
construction and instance interfaces, first at independent `uA,uM` and
then at both unequal specializations `(0,1)` and `(1,0)`. The pinned
environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with Lean
`v4.34.0` and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

This unit establishes the image construction, its intrinsic universal
laws and the stated comparisons. Concrete coimages, their first-isomorphism
comparison, uniqueness of arbitrary epi-mono factorizations, categorical
exactness, exactness of other functors and abelianness of the nondegenerate
full subcategory remain separate obligations.
