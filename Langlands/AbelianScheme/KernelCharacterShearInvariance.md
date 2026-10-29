# Invariance of the kernel character under translation by image points

This module shows that the canonical kernel character of a line bundle with
trivial homomorphism pullback does not change when the bundle is pulled back
along the shear by an image point. As a consequence, if the class character
on the given test scheme is injective, such a pullback is isomorphic to the
original bundle. Injectivity is an explicit hypothesis here; nothing in this
module proves it.

## Setting

Throughout, `S` is an arbitrary scheme, `A` and `B` are abelian schemes over
`S`, `f : A ⟶ B` is a homomorphism (no isogeny hypothesis), `T` is an object
of `Over S`, and `c : T ⟶ A.X` is a `T`-point of `A`. Write `f_T` for
`(homFamilySpaceMap f).app T : T ×_S A ⟶ T ×_S B`. The published shear
`shear B (𝟙 T) x` is the map `(t, b) ↦ (t, x(t) · b)` of `T ×_S B`. The
image point of `c` is `c ≫ (groupHom f).hom.hom`, written `f ∘ c` below.
Composition `p ≫ q` means "first `p`, then `q`".

## Declarations

- `shear_homFamilySpaceMap_id`: the square
  `f_T ≫ shear B (𝟙 T) (f ∘ c) = shear A (𝟙 T) c ≫ f_T`. It is the published
  `shear_homFamilySpaceMap` with parameter map `𝟙 T`, read backwards.

- `shearPullbackTrivialization`: given a module `M` on `T ×_S B` and an
  isomorphism `α : f_T^* M ≅ O`, it builds an isomorphism
  `f_T^* (shear B (𝟙 T) (f ∘ c))^* M ≅ O`. The construction composes three
  isomorphisms. The first is the published square comparison
  `squarePullbackIso` for the square above, which identifies the left side
  with `(shear A (𝟙 T) c)^* f_T^* M`. The second is the pullback of `α` along
  the source shear. The third is `pullbackUnitIso` for the structure module.

- `relativeSpace_map_shear_id`: for `a : U ⟶ T`, the change-of-parameter map
  followed by the source shear by `c` equals the shear over `U` by
  `a ≫ c` followed by the change of parameter. The proof writes the change of
  parameter as a shear by `1` (`shear_one`) and compares both sides with
  `shear_comp`.

- `kernelShear_shear_id`: for `a : U ⟶ T` and a `U`-point `k` of the kernel,
  the published `kernelShear f a k` followed by the source shear by `c` equals
  the shear over `U` by `a ≫ c` followed by `kernelShear f a k`. Both sides
  are shears by a product of two points (`shear_comp`). The two products
  differ only in the order of their factors, so `mul_comm` closes the goal.
  This step uses the commutativity of the abelian scheme `A`.

- `kernelTranslationAut_shear`: for the trivialization from
  `shearPullbackTrivialization`, the transported kernel action
  `kernelTranslationAut` at `(a, k)` equals
  `structureAutPullback (shear A (𝟙 U) (a ≫ c))` applied to the action of the
  original trivialization `α`. The proof first applies the published
  `equalCompositeUnitAut_square`, with both vertical maps equal to `f_T` and
  with the source and target shears as the horizontal maps. This rewrites the
  sheared action as the equal-composite automorphism of `α` along the two
  composites with the source shear. Then `relativeSpace_map_shear_id` and
  `kernelShear_shear_id` rewrite both composites as the shear over `U` by
  `a ≫ c` followed by the original maps. Finally the published
  `equalCompositeUnitAut_precomp` identifies the result with the pullback of
  the original automorphism along that shear.

- `kernelTranslationScalar_shear`: hence the global action scalar of the
  sheared trivialization is the image of the original scalar under the map
  on global units induced by `shear A (𝟙 U) (a ≫ c)`. This follows from the
  previous lemma and the published `structureAutScalar_pullback`.

- `kernelTranslationUnit_shear`: for every `h : UniversalGlobalFunctions A`,
  the descended unit on `U` (`kernelTranslationUnit`) is the same for the
  sheared trivialization and for `α`. The proof applies the published
  naturality lemma `relativeUnitDescend_map` to the shear over `U` by
  `a ≫ c`. That shear lies over the identity of `U` by `shear_fst`, so
  descending the transported scalar returns the original unit.

- `intrinsicKernelCharacter_shear`: the intrinsic kernel characters of the
  sheared trivialization and of `α` are equal. The proof applies
  `Cartier.characterHomEquiv` and reduces to homomorphisms of point groups.
  By `hom_ext_points` it compares the two homomorphisms on every `U`-point of
  the kernel, through `Gm.pointsEquiv` and
  `intrinsicKernelCharacterHom_points`. There the claim is
  `kernelTranslationUnit_shear`.

- `hasTrivialHomPullback_shear`: if `L` on `T ×_S B` satisfies
  `HasTrivialHomPullback f T L`, then so does the line bundle pullback of `L`
  along `shear B (𝟙 T) (f ∘ c)`. The witness is `shearPullbackTrivialization`
  applied to a chosen trivialization of `L`.

- `trivialHomPullbackCharacter_shear`: the canonical character
  `trivialHomPullbackCharacter f h` of the sheared bundle equals that of `L`.
  The published `trivialHomPullbackCharacter_eq` says that the canonical
  character can be computed from any trivialization. Applied to
  `shearPullbackTrivialization`, it reduces the claim to
  `intrinsicKernelCharacter_shear`.

- `nonempty_shear_pullback_iso`: assume `h : UniversalGlobalFunctions A` and
  that `trivialHomPullbackClassCharacter f (T := T) h` is injective. Then for
  every `L` with `HasTrivialHomPullback f T L` there is an isomorphism of
  line bundles
  `(LineBundle.pullback (shear B (𝟙 T) (f ∘ c))).obj L ≅ L`. The proof uses
  `trivialHomPullbackClassCharacter_classOf` and the previous lemma. They show
  that the two isomorphism classes in `TrivialHomPullbackClasses f T` have
  the same character. Injectivity makes the classes equal, `Quotient.exact`
  gives an isomorphism in `TrivialHomPullbackFamily f T`, and
  `trivialHomPullbackForget` turns it into an isomorphism of line bundles.

## Scope and provenance

Every statement holds over an arbitrary base `S`, for an arbitrary
homomorphism `f` of abelian schemes and an arbitrary test object `T`. The
injectivity of the class character enters only `nonempty_shear_pullback_iso`,
as an explicit hypothesis. This module proves neither injectivity nor any
descent or classification result.

The provenance is internal. These lemmas are bookkeeping for the published
kernel-character construction of `KernelTranslationScalar`,
`IntrinsicKernelCharacter` and `KernelCharacterIndependence`. They record
that translating by a point of the source commutes with the kernel action,
because `A` is commutative. The module serves as one step of the proof of
`FieldTrivialPullbackPicardZeroStatement`: a line bundle whose pullback along
`f` is trivial is invariant under translation by image points.
