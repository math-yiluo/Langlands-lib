# Derived sections of a pushforward with vanishing higher direct images

Author: Worker 727.

Module `Langlands.AlgebraicGeometry.Modules.PushforwardComparison`. It defines a
comparison map and proves when it is an isomorphism. Everything is proved in the
file: there are no hypotheses beyond those in the signatures and no proof holes.
The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.

The mathematical content is Stacks Project, Cohomology of Sheaves,
Lemma 01F4 (1): for a morphism of ringed spaces `f : X → Y` and an
`𝒪_X`-module `F` with `Rᵠ f_* F = 0` for `q > 0`, `Hᵖ(X, F) = Hᵖ(Y, f_* F)` for
all `p`. The Lean module gives this identification as a named map in both
directions of generality: first for a composite of functors between abelian
categories, then for pushforwards of scheme modules and `R`-module cohomology over
an affine base. The isomorphism theorem takes the acyclicity of pushforwards of
injective modules as an explicit hypothesis. That acyclicity is the separate
statement `Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicStatement`
(its second conjunct has exactly the form of the hypothesis `hJ` below); it is
not proved here.

## General part: `Langlands.Cohomology.AcyclicResolution`

Throughout, `C`, `D` and `E` are abelian categories (arbitrary universes), and
`F : C ⥤ D` is an additive functor.

### `mapAugmentation F I`

For `A : C` and an injective resolution `I : InjectiveResolution A` (Mathlib),
`mapAugmentation F I : (CochainComplex.single₀ D).obj (F.obj A) ⟶
(F.mapHomologicalComplex _).obj I.cocomplex` is the cochain map from `F A` placed in
degree `0` to `F` applied termwise to `I`, whose degree-`0` component is
`F` applied to the augmentation `A ⟶ I⁰`. In Lean the degree-`0` component is
`F.map ((singleObjXSelf (ComplexShape.up ℕ) 0 A).inv ≫ I.ι.f 0)`
(`mapAugmentation_f_zero`, a `simp` lemma); here `singleObjXSelf` is Mathlib's
identification of the degree-`0` term of `A` in degree `0` with `A`. It is built
with Mathlib's `CochainComplex.fromSingle₀Equiv`, using that the augmentation
followed by `I⁰ ⟶ I¹` is zero.

### `quasiIso_mapAugmentation`

If `C` has injective resolutions, `F` preserves finite limits, and
`hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)`, then
`QuasiIso (mapAugmentation F I)`. In words: `F I` is a right resolution of `F A`.

Proof. In degree `0`, Mathlib's `InjectiveResolution.exact₀` says that
`A ⟶ I⁰ ⟶ I¹` is exact with `A ⟶ I⁰` a monomorphism; a functor preserving finite
limits preserves this kernel (`ShortComplex.Exact.map_of_mono_of_preservesKernel`),
so `F A ⟶ F I⁰ ⟶ F I¹` is exact with `F A ⟶ F I⁰` a monomorphism, which is the
quasi-isomorphism condition in degree `0`
(`CochainComplex.quasiIsoAt₀_iff`, `ShortComplex.quasiIso_iff_of_zeros`). In degree
`q + 1` the source complex has zero homology, and the homology of `F I` is
`R^{q+1} F A` by Mathlib's `InjectiveResolution.isoRightDerivedObj`, which is zero
by `hA`.

### `compComparison G e A hA n`

Assume in addition that `D` has injective resolutions, `F` preserves finite limits,
`G : D ⥤ E` and `H : C ⥤ E` are additive, and `e : F ⋙ G ≅ H`. For `A : C` with
`hA` as above and `n : ℕ`,

`compComparison G e A hA n : (H.rightDerived n).obj A ⟶ (G.rightDerived n).obj (F.obj A)`

is the composite of

1. Mathlib's `((injectiveResolution A).isoRightDerivedObj H n).hom :
   Rⁿ H A ≅ Hⁿ(H I)` for Mathlib's chosen injective resolution `I` of `A`;
2. the homology in degree `n` of the inverse of
   `Functor.mapHomologicalComplexCompIso e` at `I`, which identifies `H I` with
   `G (F I)` termwise through `e`;
3. the Library's `resolutionComparison G (mapAugmentation F I) n :
   Hⁿ(G (F I)) ⟶ Rⁿ G (F A)`
   (`Langlands.Cohomology.AcyclicResolution.Comparison`): the comparison of the
   right resolution `F I` of `F A` (a quasi-isomorphism by
   `quasiIso_mapAugmentation`) with Mathlib's chosen injective resolution of
   `F A`.

The definition depends only on the displayed data; `hA` is used to supply the
`QuasiIso` instance needed by `resolutionComparison`.

### `isIso_compComparison`

If moreover `G` preserves finite limits and
`hG : ∀ J : C, Injective J → ∀ q : ℕ, IsZero ((G.rightDerived (q + 1)).obj (F.obj J))`
(`F` sends injective objects to `G`-acyclic objects), then
`IsIso (compComparison G e A hA n)` for every `n`.

Proof. The first two factors are isomorphisms. For the third, the terms of
`F I` are `F` of injective objects, hence `G`-acyclic by `hG`, so the Library's
proved theorem `acyclicResolutionComparisonStatement` (module
`Langlands.Cohomology.AcyclicResolution.ComparisonProof`), applied to the right
resolution `mapAugmentation F I`, the chosen injective resolution of `F A`, and the
lift `lift (mapAugmentation F I) (𝟙 _) _` (augmentation-compatible by the
Library's `comp_lift_id`), says that this comparison map is an isomorphism. The
comparison map so obtained is by definition `resolutionComparison`.

This is the derived-functor form of a composite `H ≅ G ∘ F` with `F` sending
injectives to `G`-acyclics, restricted to an object `A` that is itself `F`-acyclic:
Stacks Project, Cohomology of Sheaves, Lemma 01EZ and Remark 01F0 (the
"down-to-earth explanation": `RΓ(Y, Rf_* F)` is represented by `Γ(Y, f_* I•)`,
by Leray's acyclicity lemma), and the comparison of acyclic resolutions of
Cartan–Eilenberg, Chapter V, Proposition 1.1a, already formalized in the Library.

## Scheme part: `Langlands.AlgebraicGeometry.Modules.DerivedSections`

Fix schemes `X Y : Scheme.{u}`, a morphism `h : X ⟶ Y`, a commutative ring
`R : CommRingCat.{u}` and a morphism `g : Y ⟶ Spec R`. Write
`h_* = Scheme.Modules.pushforward h : X.Modules ⥤ Y.Modules` (Mathlib).

### `relativeGlobalSectionsCompIso h g`

`Scheme.Modules.pushforward h ⋙ relativeGlobalSections g ≅
relativeGlobalSections (h ≫ g)`: the `R`-module global sections over `Spec R` of
`h_* M` (via `g`) are the `R`-module global sections of `M` (via `h ≫ g`). Here
`relativeGlobalSections` is the Library's `pushforward ⋙ moduleSpecΓFunctor`
(module `Langlands.AlgebraicGeometry.Modules.DerivedSections`), and the
isomorphism is the functor associator followed by Mathlib's
`Scheme.Modules.pushforwardComp h g : h_* ⋙ g_* ≅ (h ≫ g)_*` whiskered by
`moduleSpecΓFunctor`.

### `pushforwardComparison h g M hM n`

For `M : X.Modules` with
`hM : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj M)` (vanishing of the
Library's higher direct images `R^{q+1} h_* M`) and `n : ℕ`,

`pushforwardComparison h g M hM n :
(relativeCohomology (h ≫ g) n).obj M ⟶ (relativeCohomology g n).obj (h_* M)`

is the map `Hⁿ(X, M) ⟶ Hⁿ(Y, h_* M)` of `R`-module cohomology (the Library's
`relativeCohomology`, the right-derived functors of `relativeGlobalSections`),
where `X` lies over `Spec R` through `h ≫ g`. It is
`compComparison (relativeGlobalSections g) (relativeGlobalSectionsCompIso h g) M hM n`
with `F = h_*` (additive and finite-limit preserving, Library/Mathlib instances)
and `H = relativeGlobalSections (h ≫ g)`. Concretely: compute `Hⁿ(X, M)` from the
chosen injective resolution `I` of `M`, read the complex of sections as the
sections of `h_* I` over `Y`, and compare the right resolution `h_* I` of `h_* M`
with an injective resolution of `h_* M`.

### `isIso_pushforwardComparison`

With `hM` as above and

`hJ : ∀ J : X.Modules, Injective J → ∀ q : ℕ,
IsZero ((relativeCohomology g (q + 1)).obj (h_* J))`,

`pushforwardComparison h g M hM n` is an isomorphism for every `n`. This is
`isIso_compComparison`; `relativeGlobalSections g` preserves finite limits by a
Library instance.

`hJ` is the `R`-module conjunct of
`PushforwardInjectiveAcyclicStatement` for `h` and `g` (Stacks Project, Cohomology
of Sheaves, Lemma 01EX (2) with `V = Y`; another route goes through Lemmas 09SX and
09SY: injective modules are flasque, pushforwards of flasque modules are flasque,
flasque modules are acyclic). Once that statement is proved, `hJ` is available for
every `h` and `g`, and the theorem gives the `R`-module form of Stacks Lemma 01F4 (1)
under the vanishing hypothesis `hM`.

## Intended use

For a closed immersion `i : X ⟶ P` (for example a section axis of an abelian
scheme over a field, in the proof of Stacks tag 0BF3 for task
`eab37f2b-d9cf-40e4-86ad-492608a9c630`), `R^{q+1} i_* M = 0` and the isomorphism
identifies `Hⁿ(P, i_* M)` with `Hⁿ(X, M)`. Composing with the map induced by the
unit `𝒪_P ⟶ i_* i^* 𝒪_P` then gives the restriction map
`Hⁿ(P, 𝒪_P) ⟶ Hⁿ(X, 𝒪_X)` used in
`Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1InjectivityStatement`.
The closed-immersion vanishing and the compatibility of this map with base change
are not part of this module.

## Provenance

- Stacks Project, Chapter "Cohomology of Sheaves", source `cohomology.tex` at commit
  `a04446e57ec1fbc252a871afcec7752fb2807b14` (sha256
  `fa9747d0082afbf8b09244dcc6c260f8a122e5e3b4a3c69e2273506d76e18a42`), retained in
  the literature folder "Stacks Project - Flasque sheaves, affine vanishing and
  Kunneth over a field (source at a04446e5)" (source id
  `stacks-flasque-affine-vanishing-kunneth-a04446e5`): Lemma
  `lemma-pushforward-injective` (tag 01EX, source line 1779), Lemma
  `lemma-before-Leray` (tag 01EZ, line 2092), Remark `remark-elucidate-lemma`
  (tag 01F0, line 2147) and Lemma `lemma-apply-Leray` (tag 01F4, line 2255).
- The general composite comparison is derived internally: it packages the
  Library's acyclic-resolution comparison (Cartan–Eilenberg, Chapter V,
  Proposition 1.1a, as cited in `Langlands.Cohomology.AcyclicResolution.Comparison`)
  for the specific resolution `F I`. The Stacks proof of 01F4 instead degenerates
  the Leray spectral sequence; the Lean route avoids spectral sequences.
