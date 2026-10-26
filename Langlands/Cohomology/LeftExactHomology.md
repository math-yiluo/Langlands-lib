# Left exact functors, homology and right derived functors

Author: Worker 61. The module imports my
`Langlands.Cohomology.AcyclicResolution.Comparison` (`comparison`, `comparisonNatTrans`,
`comparisonNatTrans_app`, `comp_lift_id`). From Mathlib it uses the short complex API
(`ShortComplex.liftCycles`, `ShortComplex.descHomology`, `ShortComplex.cyclesIsKernel`,
`ShortComplex.cyclesMap`, `ShortComplex.homologyMap`, `ShortComplex.isIso_homologyπ`,
`ShortComplex.LeftHomologyData.map`, `ShortComplex.LeftHomologyData.homologyIso`),
`KernelFork.mapIsLimit`, `InjectiveResolution.isoRightDerivedObj`,
`InjectiveResolution.isoRightDerivedObj_hom_naturality`,
`InjectiveResolution.isoRightDerivedObj_inv_naturality` and `InjectiveResolution.desc`.

Composition `f ≫ g` is `f` followed by `g`. For a functor `Φ`, `S.map Φ` is the short
complex obtained by applying `Φ` to the objects and maps of `S`.

## Setting

All declarations are in the namespace `Langlands.Cohomology.LeftExactHomology`. `D` and `E`
are abelian categories (`D : Type u`, `Category.{v} D`, `E : Type u'`,
`Category.{v'} E`), and `Φ : D ⥤ E` is an additive functor that preserves finite limits
(`[PreservesFiniteLimits Φ]`), i.e. a left exact functor. `toCycles`,
`toCycles_iCycles`, `map_toCycles_comp_toCycles` and `toCycles_naturality` do not use the
finite limit hypothesis and omit it.

## Short complexes

Let `S : ShortComplex D`, with maps `S.f : S.X₁ ⟶ S.X₂` and `S.g : S.X₂ ⟶ S.X₃`.

- `toCycles Φ S : Φ.obj S.cycles ⟶ (S.map Φ).cycles` is the lift of
  `Φ.map S.iCycles` to the cycles of `S.map Φ`, which exists because
  `Φ.map S.iCycles ≫ Φ.map S.g = 0`. `toCycles_iCycles` (`simp`, with a `reassoc` form):
  followed by the inclusion of the cycles of `S.map Φ` it is `Φ.map S.iCycles`.
- `cyclesIso Φ S : Φ.obj S.cycles ≅ (S.map Φ).cycles` compares two kernels of
  `Φ.map S.g`: the image under `Φ` of the kernel fork of the cycles of `S`, which `Φ`
  preserves since it preserves finite limits, and the cycles of `S.map Φ`. `cyclesIso_hom`
  says its morphism is `toCycles Φ S`, so `toCycles Φ S` is an isomorphism (instance
  `isIso_toCycles`).
- `map_toCycles_comp_toCycles` (`simp`, `reassoc`):
  `Φ.map S.toCycles ≫ toCycles Φ S = (S.map Φ).toCycles`, where `S.toCycles : S.X₁ ⟶
  S.cycles` is the map induced by `S.f`.
- `homologyHom Φ S : (S.map Φ).homology ⟶ Φ.obj S.homology` is the map on homology induced
  by `inv (toCycles Φ S) ≫ Φ.map S.homologyπ` (`homologyπ_homologyHom`, `simp`,
  `reassoc`). This map vanishes on the boundaries `(S.map Φ).toCycles` by
  `map_toCycles_comp_toCycles` and `S.toCycles_comp_homologyπ`, so it descends to the
  homology. Equivalently (`toCycles_homologyπ_homologyHom`, `simp`, `reassoc`):
  `toCycles Φ S ≫ (S.map Φ).homologyπ ≫ homologyHom Φ S = Φ.map S.homologyπ`.
- `toCycles_naturality` and `homologyHom_naturality` (both with `reassoc` forms): for a
  morphism `φ : S ⟶ S'` of short complexes,
  `toCycles Φ S ≫ cyclesMap (Φ.mapShortComplex.map φ) = Φ.map (cyclesMap φ) ≫ toCycles Φ S'`
  and `homologyMap (Φ.mapShortComplex.map φ) ≫ homologyHom Φ S' =
  homologyHom Φ S ≫ Φ.map (homologyMap φ)`.
- `isIso_homologyHom_of_f_eq_zero Φ S hf`: if `S.f = 0`, then `homologyHom Φ S` is an
  isomorphism. Both homology projections are isomorphisms then, and
  `homologyHom Φ S = inv (S.map Φ).homologyπ ≫ inv (toCycles Φ S) ≫ Φ.map S.homologyπ`.
- `isIso_homologyHom` (instance): if `Φ` also preserves homology
  (`[Φ.PreservesHomology]`, which holds for exact functors), `homologyHom Φ S` is an
  isomorphism. Proof: with the left homology data `h := S.leftHomologyData` and its image
  `h.map Φ`, `homologyHom Φ S` equals the composite of the isomorphisms
  `(h.map Φ).homologyIso` and `Φ.mapIso h.homologyIso.symm`.

## Homological complexes

Let `c : ComplexShape ι` and `i : ι`.

- `homologyNatTrans Φ c i : Φ.mapHomologicalComplex c ⋙ homologyFunctor E c i ⟶
  homologyFunctor D c i ⋙ Φ` has component `homologyHom Φ (K.sc i)` at a complex `K`
  (`homologyNatTrans_app`, by definition). `K.sc i` is the short complex
  `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)`, whose homology is the degree-`i` homology of
  `K`. The image of `K.sc i` under `Φ` is the short complex of `Φ` applied to `K`, by
  definition. Naturality is `homologyHom_naturality`.
- `isIso_homologyNatTrans` (instance): an isomorphism if `Φ` preserves homology.
- `isIso_homologyNatTrans_zero` (instance): for `c = ComplexShape.up ℕ` (cochain
  complexes indexed by `ℕ`) and `i = 0`, `homologyNatTrans` is an isomorphism, because the
  incoming differential of `K.sc 0` is zero (there is no degree `-1`) and
  `isIso_homologyHom_of_f_eq_zero` applies.

## Right derived functors

Let `C` be an abelian category (`C : Type u''`, `Category.{v''} C`) with
`[HasInjectiveResolutions C]` and `F : C ⥤ D` an additive functor. `F` is not assumed left
exact. `F ⋙ Φ` is additive, so both `F.rightDerived n` and `(F ⋙ Φ).rightDerived n` are
Mathlib's right derived functors.

- `derivedHom Φ F I n : ((F ⋙ Φ).rightDerived n).obj A ⟶ Φ.obj ((F.rightDerived n).obj A)`,
  for an injective resolution `I` of `A`, is
  `(I.isoRightDerivedObj (F ⋙ Φ) n).hom`, then the component of
  `homologyNatTrans Φ (ComplexShape.up ℕ) n` at `F` applied to `I.cocomplex`, then
  `Φ.map (I.isoRightDerivedObj F n).inv`. That is, both derived functors are computed by
  the cohomology of `F I` and `Φ (F I)` (the same complex, since
  `(F ⋙ Φ).mapHomologicalComplex` is `F.mapHomologicalComplex ⋙ Φ.mapHomologicalComplex`
  on objects by definition), and the map between them is `homologyHom`.
- `derivedHom_naturality Φ F f I J ψ comm n`: for `f : A ⟶ B`, injective resolutions `I`
  of `A` and `J` of `B`, and a cochain map `ψ : I.cocomplex ⟶ J.cocomplex` over `f`
  (`comm : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0`),
  `((F ⋙ Φ).rightDerived n).map f ≫ derivedHom Φ F J n =
  derivedHom Φ F I n ≫ Φ.map ((F.rightDerived n).map f)`. Proof: Mathlib's naturality
  of `isoRightDerivedObj` (hom for `F ⋙ Φ`, inv for `F`) and the naturality of
  `homologyNatTrans` at `F ψ`.
- `derivedHom_eq Φ F I J n`: `derivedHom Φ F I n = derivedHom Φ F J n` for any two
  injective resolutions of `A`. This is `derivedHom_naturality` for `f = 𝟙 A` and
  `ψ := InjectiveResolution.desc (𝟙 A) J I`.
- `derivedNatTrans Φ F n : (F ⋙ Φ).rightDerived n ⟶ F.rightDerived n ⋙ Φ` has component
  `derivedHom Φ F (injectiveResolution A) n` (Mathlib's chosen resolution). Naturality is
  `derivedHom_naturality` with `ψ := InjectiveResolution.desc f _ _`.
  `derivedNatTrans_app Φ F I n` says that its component at `A` is `derivedHom Φ F I n` for
  every injective resolution `I` of `A`.
- `isIso_derivedNatTrans_zero` (instance): `derivedNatTrans Φ F 0` is an isomorphism, by
  `isIso_homologyNatTrans_zero`.
- `isIso_derivedNatTrans` (instance): if `Φ` preserves homology, `derivedNatTrans Φ F n`
  is an isomorphism for every `n`, by `isIso_homologyNatTrans`.

## Compatibility with the comparison maps of resolutions

`AcyclicResolution.comparison F I φ n : Hⁿ(F K) ⟶ (F.rightDerived n).obj A` (my published
module `AcyclicResolution.Comparison`) is the cohomology map of `F φ` for a cochain map
`φ : K ⟶ I.cocomplex`, followed by `(I.isoRightDerivedObj F n).inv`.

- `comparison_comp_derivedHom Φ F I φ n`:
  `AcyclicResolution.comparison (F ⋙ Φ) I φ n ≫ derivedHom Φ F I n =
  (homologyNatTrans Φ (ComplexShape.up ℕ) n).app ((F.mapHomologicalComplex _).obj K) ≫
  Φ.map (AcyclicResolution.comparison F I φ n)`.
  No compatibility of `φ` with augmentations is needed. Proof: the isomorphisms
  `isoRightDerivedObj (F ⋙ Φ)` cancel, and the rest is the naturality of
  `homologyNatTrans` at `F φ`.
- `comparisonNatTrans_comp_derivedNatTrans Φ F 𝒦 e he n`: for a functorial right
  resolution `𝒦 : C ⥤ CochainComplex C ℕ`, `e : single₀ C ⟶ 𝒦` with
  `he : ∀ A, QuasiIso (e.app A)`,
  `AcyclicResolution.comparisonNatTrans (F ⋙ Φ) 𝒦 e he n ≫ derivedNatTrans Φ F n =
  whiskerLeft (𝒦 ⋙ F.mapHomologicalComplex _) (homologyNatTrans Φ (ComplexShape.up ℕ) n) ≫
  whiskerRight (AcyclicResolution.comparisonNatTrans F 𝒦 e he n) Φ`.
  Both comparison transformations are computed with Mathlib's injective resolution and
  the augmentation-compatible lift `lift (e.app A) (𝟙 A) _` (`comparisonNatTrans_app`,
  `comp_lift_id`), and `comparison_comp_derivedHom` applies.

In words: for a functorial resolution `𝒦` and a left exact `Φ`, the square formed by the
comparison maps `Hⁿ(Φ F 𝒦 A) ⟶ Rⁿ(F ⋙ Φ) A` and `Hⁿ(F 𝒦 A) ⟶ Rⁿ F A` (the latter followed
by `Φ`) and the two maps `homologyHom` and `derivedHom` commutes.

## Provenance and interpretation

Provenance: derived. These are standard constructions of homological algebra, formalized
here as framework infrastructure; they are not quoted from a source.

For a left exact `Φ` and a complex `K`, `Φ` preserves the kernels of the differentials, so
the cycles of `Φ K` are `Φ` of the cycles of `K`. The projection of `Φ` of the cycles onto
`Φ` of the homology kills the boundaries of `Φ K`. This gives the canonical map
`Hⁱ(Φ K) → Φ(Hⁱ K)` (`homologyHom`, `homologyNatTrans`). In degree zero of an `ℕ`-indexed
cochain complex it is an isomorphism, since `H⁰` is the kernel of the first differential.
For exact `Φ` it is an isomorphism in all degrees. Applied to `F I` for an injective
resolution `I`, it gives the map `Rⁿ(F ⋙ Φ) A → Φ(Rⁿ F A)` (`derivedHom`,
`derivedNatTrans`). This module does not relate it to any spectral sequence.

The use in the framework is Harris, *Galois properties of cohomological automorphic forms
on GL(n)* (1999), §2, printed p.305. There the cohomology is computed by the complex of
global sections of a smooth equivariant Godement-type resolution (Lemma 2.2, printed
p.304, and its truncation, Lemma 2.2 bis, printed p.305), and (2.3) identifies its
cohomology with the étale cohomology. Harris then chooses an open normal pro-p subgroup
`H` acting trivially on this cohomology and states that, since p is prime to ℓ, the
functor `H⁰(H, ·)` is exact on ℓ-primary torsion modules, so the inclusion of the
complex of `H`-invariants into the complex in (2.3) is a quasi-isomorphism. Invariants
under a subgroup are thus taken termwise in the resolution. This module supplies the
functor-independent part of comparing the cohomology of `Φ` applied to such a resolution
with `Φ` of its cohomology, and with right derived functors of `F ⋙ Φ`, for a left exact
`Φ` such as the invariants under a subgroup. It is compatible with the comparison maps of
`AcyclicResolution.Comparison`. Exactness of `H⁰(H, ·)` on the relevant modules is not
formalized here. It enters only as the hypothesis `[Φ.PreservesHomology]` of
`isIso_homologyHom`, `isIso_homologyNatTrans` and `isIso_derivedNatTrans`.

## Scope

- One left exact additive functor `Φ`. The isomorphism statements in positive degrees need
  `Φ` to preserve homology. Nothing is claimed about the kernel or cokernel of
  `homologyHom` in general.
- The specialization to smooth representations (invariants under a compact open
  subgroup, and full invariants, applied to the smooth Godement complex) is not part of
  this module.
