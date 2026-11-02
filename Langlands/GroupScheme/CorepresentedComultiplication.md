# Comultiplication, antipode and classifying maps of corepresented group functors

Author: Worker 228.

This module extends the published `Corepresented` interface
([`Corepresented`](Corepresented.md), [`CorepresentedPoints`](CorepresentedPoints.md)).
It concerns a group-valued functor `F : CommAlgCat R ⥤ GrpCat` with a corepresentation
`e : (F ⋙ forget GrpCat).CorepresentableBy B` by a commutative `R`-algebra `B`, over an
arbitrary commutative ring `R`. No field, finiteness or flatness hypothesis is used. All
declarations are in `Langlands.GroupScheme.Corepresented`, except `IsCentral.comp_iso`, which
is in `Langlands.GroupScheme`.

## Tensor products

`tensorObj A B` is `A ⊗[R] B` as an object of `CommAlgCat R`. `inl` and `inr` are the two
inclusions `a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b`. `tensorLift f g` is Mathlib's
`Algebra.TensorProduct.productMap`, `a ⊗ b ↦ f a * g b`. The lemmas `inl_apply`, `inr_apply`,
`tensorLift_tmul`, `inl_tensorLift`, `inr_tensorLift` and `tensorLift_comp` record the evident
identities. `tensorLift_comp` says that `tensorLift f g ≫ h = tensorLift (f ≫ h) (g ≫ h)`;
it is checked on pure tensors with `Algebra.TensorProduct.ext'`.

## Comultiplication and antipode

`homEquiv_comp'` restates the corepresentation axiom as
`e (f ≫ g) = F.map g (e f)`.

* The existing `LinearEmbedding.comul e : B ⟶ B ⊗ B`, imported from
  [`CorepresentedLinearEmbedding`](CorepresentedLinearEmbedding.md), classifies the product
  `e(inl) * e(inr)` of the two universal points over `B ⊗ B`. We write it as `comul e` below.
* `antipode e : B ⟶ B` classifies the inverse `e(𝟙 B)⁻¹` of the universal point.

`homEquiv_symm_mul` proves that for points `x, y` of `F` over any algebra `C`, the classifying
map of `x * y` is `comul e ≫ tensorLift (e⁻¹ x) (e⁻¹ y)`. This directly reuses the published
`LinearEmbedding.cls_mul`; its classifying maps and tensor-square pair map agree
definitionally with the interfaces used here. Likewise `homEquiv_symm_inv` proves that the classifying map
of `x⁻¹` is `antipode e ≫ e⁻¹ x`. `homEquiv_comul` and `homEquiv_antipode` are the defining
equations.

These are the comultiplication and antipode of the Hopf algebra of an affine group scheme.
Here they are obtained directly from the group-valued functor; no Hopf-algebra structure is
assumed or constructed.

## Classifying maps of natural homomorphisms

Let `G` be a second group-valued functor with a corepresentation `d` by `C`, and let
`α : F ⟶ G` be a natural transformation. `classify e d α : C ⟶ B` is the algebra map
classifying `α` applied to the universal point `e(𝟙 B)`.

* `app_homEquiv`: `α (e f) = d (classify e d α ≫ f)` for every `f : B ⟶ S`. This is
  naturality of `α` along `f`.
* `classify_comul`: `classify ≫ comul e = comul d ≫ tensorLift (classify ≫ inl) (classify ≫ inr)`.
  In other words, the classifying map intertwines the comultiplications. The proof applies
  `app_homEquiv` to `comul e`, uses that `α` preserves products, and then uses
  `homEquiv_symm_mul` for `d`.
* `classify_antipode`: `classify ≫ antipode e = antipode d ≫ classify`, by the same argument with
  inverses.

## Homomorphisms of corepresented group schemes

For the group schemes `groupScheme F e` and `groupScheme G d` of the published `Corepresented`
module:

* `hom_ext_affinePoints`: two homomorphisms agree if they agree after composition with every
  affine point, read through `affinePointsEquiv`. The proof uses the identity point of
  `Spec_R B`.
* `pointsTrans φ : F ⟶ G` is the natural transformation of a homomorphism `φ`, read off on
  affine points: `x ↦ affinePointsEquiv (affinePointsEquiv⁻¹ x ≫ φ)`. It is multiplicative
  because `φ` is a homomorphism of group objects (`MonObj.mul_comp`). Naturality follows from
  `affinePointsEquiv_naturality`.
* `groupSchemeMap_pointsTrans`: `groupSchemeMap e d (pointsTrans e d φ) = φ`. So every
  homomorphism of corepresented group schemes comes from a natural transformation.
* `groupSchemeMap_comp`: induced homomorphisms compose like the natural transformations.
* `groupSchemeMap_hom_left`: the underlying scheme map of `groupSchemeMap e d α` is
  `Spec.map` of `classify e d α`. This restates the published `groupSchemeMap_hom` with the
  name `classify`.

## Centrality

`IsCentral` is the published centrality predicate of
[`Rational/Characters`](Rational/Characters.md): every point maps into the all-test centre.

* `isCentral_groupSchemeMap`: `groupSchemeMap e d α` is central if, for every algebra `S`,
  every value `α x` commutes with every element of `G(S)`. The proof transports commutation
  along the multiplicative point equivalence `pointsEquiv` of `CorepresentedPoints`, which is
  valid over all test schemes, and uses `groupSchemeMap_points`.
* `IsCentral.commute_pointsTrans`: conversely, if `φ` is central, then the values of
  `pointsTrans e d φ` commute with all elements of `G(S)`. It specializes centrality to the
  affine test scheme `Spec_R S` and transports along `affinePointsEquiv`.
* `commute_of_mulEquiv` is the elementary fact that a multiplicative equivalence reflects
  commutation.
* `IsCentral.comp_iso` (namespace `Langlands.GroupScheme`): postcomposing a central
  homomorphism with an isomorphism of group schemes gives a central homomorphism. Each point of
  the new target is written as `(y ≫ e⁻¹) ≫ e`, and commutation is transported along
  `isoPointsEquiv`.

## Provenance

These are internal constructions from the published `Corepresented`, `CorepresentedPoints`
and `Rational/Characters` modules, reusing `CorepresentedLinearEmbedding` for comultiplication, and from Mathlib's corepresentable functors and algebra
tensor products. They make no claim from the literature.
