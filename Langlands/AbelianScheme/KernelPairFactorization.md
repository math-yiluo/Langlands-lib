# Pairs with equal composite along a homomorphism family map

Author: Worker 934. This helper module supplies the geometric reduction of
equal-composite pairs along `f_T := (homFamilySpaceMap f).app T : T ×_S A ⟶ T ×_S B`
to the published kernel translations `kernelShear`. It is an internal formal
deduction from published definitions and Mathlib; no literature result is
formalized here. It is used by the injectivity and surjectivity proofs of the
normalized kernel character.

Throughout, `S` is an arbitrary base scheme, `A B : AbelianScheme S`,
`f : A ⟶ B`, and `T : Over S`.

## A congruence lemma

`Langlands.Scheme.Modules.equalCompositeUnitAut_congr`: if `a = a'` and
`b = b'`, then `equalCompositeUnitAut p a b h α = equalCompositeUnitAut p a' b' h' α`.
The proof substitutes the equalities.

## The family map is a base change of `f`

- `homFamilySpaceMap_isPullback`: the square with top `f_T`, verticals the second
  projections `T ×_S A ⟶ A` and `T ×_S B ⟶ B`, and bottom `hom f` is a pullback.
  This comes from Mathlib's `IsPullback.of_right`. The right square
  `T ×_S B ⟶ T`, `B ⟶ S` is the defining pullback. The outer rectangle is the
  defining pullback of `T ×_S A`, because `f_T ≫ fst = fst`
  (`homFamilySpaceMap_fst`) and `hom f ≫ B.X.hom = A.X.hom`.
- `isFinite_homFamilySpaceMap`, `flat_homFamilySpaceMap`,
  `surjective_homFamilySpaceMap`: for an isogeny `f` (finite, flat, surjective
  `hom f`), `f_T` is finite, flat and surjective. These follow from
  `MorphismProperty.of_isPullback` and the stability of each property under base
  change in Mathlib. A finite morphism is affine (`IsFinite` extends
  `IsAffineHom`).

## The kernel point of a pair

Fix a scheme `U` and `a b : U ⟶ T ×_S A` with `h : a ≫ f_T = b ≫ f_T`.

- `pairParameter a : Over T.left` is `U` with structure map
  `t := a ≫ pullback.fst`.
- `pair_fst_eq` shows `b ≫ fst = a ≫ fst`, by composing `h` with the first
  projection.
- `pairPoint a c _` is the point `c ≫ snd`, as a morphism over `S` from
  `U' := (Over.map T.hom).obj (pairParameter a)` to `A.X`.
- `pair_snd_hom` shows that the points of `a` and `b` have the same image under
  `f`, by composing `h` with the second projection.
- `pairKernelPoint f a b h : U' ⟶ ker f` is the kernel point with
  `pairKernelPoint ≫ ι = pairPoint b * (pairPoint a)⁻¹` (`pairKernelPoint_ι`).
  It is obtained from the published `GroupScheme.kernelPointsEquiv`.

## Factorization through a kernel translation

- `pairSection a : U ⟶ U' ×_S A` is `pullback.lift (𝟙 U) (a ≫ snd)`.
- `pairSection_map`: `pairSection a ≫ (relativeSpace A.X.hom).map t' = a`. Here
  `t' = kernelCharacterParameter (pairParameter a)` is the parameter map
  `U' ⟶ T` used by the published intrinsic character.
- `pairSection_kernelShear`:
  `pairSection a ≫ kernelShear f t' (pairKernelPoint f a b h) = b`. On second
  components, the shear multiplies `(pairPoint b * (pairPoint a)⁻¹)` by
  `pairPoint a`. This uses `MonObj.comp_mul` and the fact that `pairSectionOver`,
  the section regarded over `S`, has first component the identity and second
  component `pairPoint a`.

## Comparison scalars along `f_T`

`structureAutScalar_equalCompositeUnitAut_eq`: for every module `M` on
`T ×_S B` and every trivialization `α : f_T^* M ≅ O`,

```text
structureAutScalar (equalCompositeUnitAut f_T a b h α) =
  Units.map (pairSection a).appTop
    (kernelTranslationScalar f α t' (pairKernelPoint f a b h)).
```

The proof first rewrites `a` and `b` by the two factorizations through
`equalCompositeUnitAut_congr`. It then applies the published
`equalCompositeUnitAut_precomp` along `pairSection a`, which yields the
published `structureAutPullback` of `kernelTranslationAut`, and finally
`structureAutScalar_pullback`. So every comparison scalar along `f_T` is
determined by kernel-translation scalars, the scalars that define the
normalized character.
