# Degree-zero vanishing for nontrivial translation-invariant line bundles

Module `Langlands.AlgebraicGeometry.Picard.TranslationInvariantH0VanishingProof`.

This module proves the exact target
`Langlands.AbelianScheme.AlgClosedFieldTranslationInvariantH0VanishingStatement` (module
`Langlands.AlgebraicGeometry.Picard.TranslationInvariantH0VanishingStatement`), as the theorem
`Langlands.AbelianScheme.algClosedFieldTranslationInvariantH0Vanishing`. Take an
algebraically closed field `K`, an abelian scheme `A` over `Spec K` and a line bundle `L` on
`A.X.left` that is invariant under every `K`-rational translation and is not isomorphic to the
trivial bundle. Then the degree-zero relative cohomology
`(DerivedSections.relativeCohomology A.X.hom 0).obj L.obj` is zero.

## Source

Edixhoven, van der Geer and Moonen, *Abelian Varieties* (preliminary chapters), literature ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, Lemma (7.19), first paragraph,
printed p.105 / PDF p.109. The source shows that if `L` is in `Pic⁰` and nontrivial, then a
nonzero section of `L` together with the induced section of `(-1)^*L ≅ L⁻¹` gives a nonzero
section of `𝒪`, which is a nonzero constant. So both sections are nowhere zero and `L` is
trivial. The Lean proof follows the same idea, using the trivialization opens of sections
instead of divisors.

## Declarations

### `Langlands.AlgebraicGeometry.Picard.LineBundle.eq_zero_of_trivializationOpen_eq_bot`

Let `X` be reduced, `L` a line bundle on `X` and `s` a global section. If the trivialization
open `trivializationOpen L.obj s` is empty, then `s = 0`.

Proof. Around each point `x`, use the chosen trivialization `L|_W ≅ 𝒪_W` on
`W = L.trivializingOpen x`. Transported along it, the restriction of `sectionHom L.obj s`
becomes an endomorphism `ψ` of `𝒪_W`. By `structureModule_hom_eq_zero_iff`, `ψ = 0` holds
exactly when its coefficient `g ∈ Γ(W, ⊤)` is zero. On the reduced scheme `W`, `g` is zero
exactly when its basic open is empty (`basicOpen_eq_bot_iff`), that is, when `g` has zero
image in every residue field. At a point `y` where it does not, `residueLocalChartCriterion`
says `s` is nonvanishing at `y`. Then `lineBundleResidueOpenComparison` puts `y` in the
trivialization open, which is empty by assumption. So every local restriction of
`sectionHom L.obj s` is zero. The uniqueness half of `OpenCoverHomGluing.openCoverHomGluing`
on the cover by the opens `L.trivializingOpen x` shows that `sectionHom L.obj s = 0`. Hence
`s = 0` by `sectionHom_eq_zero_iff`.

### Reused `Langlands.SchemeModule.trivializationOpen_mapIso`

The published lemma from `AmpleIsoProof` is reused directly. An isomorphism of
modules `e : M ≅ N` does not change trivialization opens:
`trivializationOpen N (e.hom.app ⊤ s) = trivializationOpen M s`. The proof uses
`sectionHom_naturality`; composing with the isomorphism `e.hom` preserves being an
isomorphism on every open.

### `Langlands.AlgebraicGeometry.Picard.trivializationOpen_structureSheaf_of_isUnit`

A unit `g` of `Γ(X, ⊤)` has trivialization open `⊤` as a section of the structure sheaf. The
multiplication endomorphism `sectionHom (structureSheaf X) g` has coefficient `g`. Its
restriction to each open `U` is `g|_U`, which is a unit. So by `unitEnd_app_isIso` every
component is invertible.

### `Langlands.AlgebraicGeometry.Picard.LineBundle.eq_zero_of_tensor_pullback_iso`

Let `X` be integral with `Γ(X, ⊤)` a field. Let `f : X ⟶ X` be surjective and `L` a line
bundle with an isomorphism `φ : L ⊗ f^*L ≅ 𝒪_X`, not isomorphic to the trivial bundle. Then
every global section `s` of `L` is zero.

Proof. Let `t = f^*s` (`pullbackSection`) and `g = φ(s ⊗ t) ∈ Γ(X, ⊤)`.
`lineBundlePullbackSectionOpen` and `tensorSectionGenerationLocus`, transported along `φ` by
`trivializationOpen_mapIso`, give
`trivializationOpen 𝒪 g = U ⊓ f⁻¹U`, where `U = trivializationOpen L.obj s`.

- If `g = 0`, then `U ⊓ f⁻¹U = ⊥` (`trivializationOpen_zero`). If `U` were nonempty, say
  containing `f y`, then `f⁻¹U` would contain `y`. On the irreducible space `X` two nonempty
  opens meet (`nonempty_preirreducible_inter`), which is a contradiction. So `U = ⊥` and
  `s = 0` by the first lemma.
- If `g ≠ 0`, then `g` is a unit in the field `Γ(X, ⊤)`, so `U ⊓ f⁻¹U = ⊤` and `U = ⊤`. By
  `isIso_sectionHom_of_trivializationOpen_eq_top`, `sectionHom L.obj s : 𝒪 ⟶ L` is an
  isomorphism. This contradicts the nontriviality of `L`.

### `Langlands.AbelianScheme.inversion_left_comp_inversion_left`

For an abelian scheme `A` over `S`, inversion `i = ((𝟙 A.X)⁻¹).left` satisfies `i ≫ i = 𝟙`.
This follows from `GrpObj.comp_inv` and `inv_inv` in the group `A.X ⟶ A.X`.

### `Langlands.AbelianScheme.relativeCohomology_zero_isZero_of_inversion_tensor_iso`

For an abelian scheme `A` over `Spec K`, with `K` any field, let `L` be a line bundle on
`A.X.left` not isomorphic to the trivial bundle, and suppose given an isomorphism
`L ⊗ i^*L ≅ 𝒪` for the inversion `i`. Then
`(DerivedSections.relativeCohomology A.X.hom 0).obj L.obj` is zero.

Proof.

1. `smoothGeometricIntegrality` makes `A.X.hom` geometrically integral, so `A.X.left` is
   integral (`GeometricallyIntegral.isIntegral_of_subsingleton`).
2. `fieldSmoothProperConnectedGlobalFunctions` makes `A.X.hom.appTop` an isomorphism. With
   `Scheme.ΓSpecIso` this gives a ring isomorphism `Γ(A.X.left, ⊤) ≅ K`, so `Γ(A.X.left, ⊤)` is
   a field.
3. `i` is surjective, because `i ≫ i = 𝟙`.
4. The previous lemma, applied with `f = i`, shows that every global section of `L` is zero.
5. `relativeCohomologyZeroIso` and `relativeGlobalSectionsIso` identify the degree-zero
   cohomology with the global sections of `L`, with scalars restricted. A module with at most
   one element is zero (`ModuleCat.isZero_of_subsingleton`).

### `Langlands.AbelianScheme.algClosedFieldTranslationInvariantH0Vanishing`

The exact target, `AlgClosedFieldTranslationInvariantH0VanishingStatement.{u}`.

Proof. Fix `K`, `A`, a translation-invariant `L` and its nontriviality. The second conjunct
of the published theorem
`Langlands.AbelianScheme.algClosedFieldTranslationInvariantPullbackIdentities` (module
`Langlands.AlgebraicGeometry.Picard.TranslationInvariantPullbackIdentitiesProof`) gives an
isomorphism `φ : L ⊗ i^*L ≅ 𝒪` for the inversion `i = ((𝟙 A.X)⁻¹).left`. Only this inversion
identity is used, not the multiplication identity.
`relativeCohomology_zero_isZero_of_inversion_tensor_iso`, applied to `φ` and the
nontriviality hypothesis, gives the vanishing.

The proof adds no hypotheses. Translation invariance enters only through the identities
theorem, and the remaining steps hold over any field.
