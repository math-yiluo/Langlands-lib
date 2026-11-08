# The actual finite Galois Weil pushout cocycle

Author: Worker 1556, using Worker 1839's equivariance module
`Langlands.Weil.Local.FiniteGaloisEquivariance`. This is a derived construction
unit for task `37d6d58f-e378-4630-8a8c-0f3d7212a970`. All declarations are in
`Langlands.Weil.Local`.

## Setting

Fix a prime `p`, p-adic fields `F : PadicField.{u} p` and `E : PadicField.{v} p`,
an embedding `f : F.Carrier →ₐ[Padic p] E.Carrier`, and
`hGal : IsGalois F.Carrier E.Carrier` for the algebra structure
`extensionAlgebra F E f`. Write `q = finiteGaloisQuotient F E f hGal`, the
continuous surjection `W_F → Gal(E/F)`. Fix a reciprocity candidate
`e : ReciprocityCandidate E` together with
`he : GeometricWeilReciprocityRelation E E.canonicalTopologicalData e`. No other
hypothesis is used.

## Construction

- `finiteGaloisSection` is a normalized set-theoretic section of `q`, chosen by
  `GroupExtensionPushout.Section.ofSurjective` from the proved surjectivity
  `finiteGaloisQuotient_surjective`.
- `finiteGaloisCocycle F E f hGal e he` is the normalized factor 2-cocycle of
  `Gal(E/F)` with values in `Eˣ`. It is obtained by applying the inverse kernel
  reciprocity map `finiteGaloisKernelReciprocity F E f hGal e` to the factor set
  of the section, which lies in the kernel of `q`. The generic construction
  `Section.cocycle` requires that this kernel map be equivariant for conjugation
  by `W_F` and the Galois action on `Eˣ`. That premise is supplied by
  `finiteGaloisKernelReciprocity_conjugateKernel F E f hGal e he` from
  `FiniteGaloisEquivariance`, which is proved from `he`.
- `finiteGaloisClass F E f hGal e he` is the class of this cocycle in the
  existing group `relativeCohomology F.Carrier E.Carrier 2`.
- `finiteGaloisPushout F E f hGal e he` is the continuous homomorphism from the
  actual Weil group `W_F` to the extension group of the cocycle, given by
  `Section.toContinuousMonoidHom`. It is continuous because `Gal(E/F)` is
  discrete and both `q` and the inverse kernel reciprocity map are continuous.

## Properties

- `projection_finiteGaloisPushout`: composing with the extension projection
  gives `q`. This holds by definition.
- `finiteGaloisPushout_projection_apply`: for `g : W_F` and `x : E`, the
  projection of the image of `g` acts on `x` through the specified embedding
  `extensionFieldEmbedding F E f` as the Galois image `localProjection F g`
  of `g`. This is `finiteGaloisQuotient_apply`.
- `finiteGaloisPushout_extensionWeilMap`: for `y : W_E`, the image of
  `extensionWeilMap F E f y` is `inl (reciprocityUnits E e y)⁻¹`. The proof uses
  the generic kernel formula `Section.toContinuousMonoidHom_kernel` at
  `finiteGaloisQuotientKernelEquiv F E f hGal y`, then
  `finiteGaloisKernelReciprocity_apply` and `map_inv`.
- `finiteGaloisClass_eq_of_section`: the class does not depend on the section.
  For any normalized section `s` of `q`, the class of the cocycle built from `s`
  equals `finiteGaloisClass`. This is the generic `Section.cohomologyClass_eq`,
  which uses the explicit change-of-section cochain.

## Scope and provenance

Provenance is derived. The unit composes the generic pushout construction of
`Langlands.GroupTheory.ExtensionPushout`, the finite Galois quotient and kernel
reciprocity modules, and the equivariance theorem of `FiniteGaloisEquivariance`.
It makes no new literature claim. Classically, it is the pushout of the
extension `1 → W_E → W_F → Gal(E/F) → 1` along inverse reciprocity
`W_E → Eˣ`, which presents the relative Weil group of Tate 1979, *Number
theoretic background*, §1. Nothing here relies on that source.

This unit does not identify `finiteGaloisClass` with an arithmetic fundamental
class, and it does not construct a map into `CompletionClassExtension`. No
desired class identity and no map to a prescribed extension is assumed. Both
remain obligations of the host task `LocalWeilClassMapExistenceStatement`.
