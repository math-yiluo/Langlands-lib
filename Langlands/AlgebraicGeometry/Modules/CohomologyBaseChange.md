# Base change maps on cohomology over affine bases

Author: Worker 727.

Module `Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange`. It defines the
base change map on cohomology for a commutative square of schemes over a map of
affine bases, and proves that this map and the comparison maps it is built from are
natural in the module. Everything is proved in the file: there are no hypotheses
beyond those in the signatures and no proof holes. The only axioms used are
`propext`, `Classical.choice` and `Quot.sound`.

The mathematical content is the degreewise, global-sections form of the base change
map of Stacks Project, Cohomology of Sheaves, Lemma 02N7, constructed differently
(see "Provenance"). It does not assume any flatness. Instead the definition takes
two vanishing hypotheses, `hM` and `hJ` below, which make the comparison map of the
module `PushforwardComparison` an isomorphism. The module states no further
properties of the map (no isomorphism criterion and no compatibility with
composition of squares).

## General part: `Langlands.Cohomology.AcyclicResolution`

Throughout, `C`, `D` and `E` are abelian categories (arbitrary universes). The
declarations `mapAugmentation`, `quasiIso_mapAugmentation` and `compComparison` are
those of the Library module `Langlands.AlgebraicGeometry.Modules.PushforwardComparison`.

### `mapAugmentation_naturality`

Let `F : C ⥤ D` be additive, `u : A ⟶ B` a morphism of `C`, `I` and `J` injective
resolutions of `A` and `B` (Mathlib's `InjectiveResolution`), and
`ψ : I.cocomplex ⟶ J.cocomplex` a cochain map with
`I.ι ≫ ψ = (CochainComplex.single₀ C).map u ≫ J.ι` (that is, `ψ` lies over `u`).
Then

`mapAugmentation F I ≫ (F.mapHomologicalComplex _).map ψ =
(CochainComplex.single₀ D).map (F.map u) ≫ mapAugmentation F J`.

Proof. Both sides are maps out of a complex concentrated in degree `0`, so it
suffices to compare degree-`0` components; there the identity is `F` applied to the
degree-`0` component of the hypothesis on `ψ`.

### `compComparison_naturality`

Assume `C` and `D` have injective resolutions, `F : C ⥤ D` is additive and preserves
finite limits, `G : D ⥤ E` and `H : C ⥤ E` are additive, and `e : F ⋙ G ≅ H`. For
`u : A ⟶ B` in `C`, with `hA` and `hB` the vanishing of `R^{q+1} F` at `A` and at
`B` for all `q : ℕ`, and `n : ℕ`,

`(H.rightDerived n).map u ≫ compComparison G e B hB n =
compComparison G e A hA n ≫ (G.rightDerived n).map (F.map u)`.

(The `@[reassoc]` attribute also generates `compComparison_naturality_assoc`.)

Proof. Take for `ψ` Mathlib's `InjectiveResolution.desc u` between the chosen
injective resolutions of `A` and `B`. Each of the three factors of `compComparison`
is natural with respect to `ψ`:

1. Mathlib's `InjectiveResolution.isoRightDerivedObj_hom_naturality` for the
   identification `Rⁿ H ≅ Hⁿ(H I)`;
2. naturality of the inverse of `Functor.mapHomologicalComplexCompIso e`;
3. the Library's `resolutionComparison_naturality` (module
   `Langlands.Cohomology.AcyclicResolution.Comparison`) for the right resolutions
   `mapAugmentation F I` and `mapAugmentation F J`, whose hypothesis is
   `mapAugmentation_naturality` above.

## Scheme part: `Langlands.AlgebraicGeometry.Modules.DerivedSections`

Write `h_*` for Mathlib's `Scheme.Modules.pushforward h`, `h^*` for Mathlib's
`Scheme.Modules.pullback h`, and `Hⁿ_R(X, M)` for the Library's
`(relativeCohomology f n).obj M`, the `n`-th right-derived functor of the `R`-module
global sections `relativeGlobalSections f` along `f : X ⟶ Spec R` (module
`Langlands.AlgebraicGeometry.Modules.DerivedSections`). All schemes and rings are in
one universe `u`.

### `pushforwardComparison_naturality`

For `h : X ⟶ Y`, `g : Y ⟶ Spec R`, `u : M ⟶ N` in `X.Modules`, `hM` and `hN` the
vanishing of the Library's `higherDirectImage h (q + 1)` at `M` and at `N` for all
`q : ℕ`, and `n : ℕ`,

`(relativeCohomology (h ≫ g) n).map u ≫ pushforwardComparison h g N hN n =
pushforwardComparison h g M hM n ≫ (relativeCohomology g n).map (h_*.map u)`.

This is `compComparison_naturality` with `F = h_*`, `G = relativeGlobalSections g`
and `e = relativeGlobalSectionsCompIso h g` (the definition of the Library's
`pushforwardComparison`). It also has an `_assoc` form.

### `structureRingHom_eq_comp`

For `φ : R ⟶ R'` in `CommRingCat`, `f : X ⟶ Spec R` and `f' : X ⟶ Spec R'` with
`w : f = f' ≫ Spec.map φ`, the Library's ring maps satisfy
`structureRingHom f = φ ≫ structureRingHom f'`. Here `structureRingHom f` is
`(Scheme.ΓSpecIso R).inv ≫ f.appTop : R ⟶ Γ(X, ⊤)`; the proof substitutes `w` and
closes the goal by `simp` (Mathlib's `simp` lemmas for `Spec.map` and
`Scheme.ΓSpecIso`).

### `relativeCohomologyBaseRingIso φ f f' w n`

With `φ`, `f`, `f'` and `w` as above and `n : ℕ`,

`relativeCohomologyBaseRingIso φ f f' w n :
relativeCohomology f n ≅ relativeCohomology f' n ⋙ ModuleCat.restrictScalars φ.hom`.

In words: if `X` lies over `Spec R` through `Spec R'`, then the `R`-module
`Hⁿ_R(X, M)` is the `R'`-module `Hⁿ_{R'}(X, M)` viewed as an `R`-module through `φ`,
naturally in `M`. It is the composite of the inverse of the Library's
`relativeCohomologyRestrictScalarsIso f n` (both sides are the `Γ(X, ⊤)`-module
cohomology `cohomology X n` with scalars restricted), Mathlib's
`ModuleCat.restrictScalarsComp'` for `structureRingHom f = φ ≫ structureRingHom f'`
(by `structureRingHom_eq_comp`), an associator, and
`relativeCohomologyRestrictScalarsIso f' n` whiskered by restriction of scalars along
`φ`.

### `baseChangeMap φ f f' g w M hM hJ n`

Data: schemes `X X' : Scheme.{u}`, rings `R R' : CommRingCat.{u}`, `φ : R ⟶ R'`,
`f : X ⟶ Spec R`, `f' : X' ⟶ Spec R'`, `g : X' ⟶ X` with
`w : g ≫ f = f' ≫ Spec.map φ` (a commutative square), `M : X.Modules`, `n : ℕ`, and
the hypotheses

- `hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj (g^*.obj M))`: the
  higher direct images `R^{q+1} g_* (g^* M)` vanish;
- `hJ : ∀ J : X'.Modules, Injective J → ∀ q : ℕ,
  IsZero ((relativeCohomology f (q + 1)).obj (g_*.obj J))`: pushforwards along `g` of
  injective `𝒪_{X'}`-modules have vanishing positive-degree `R`-module cohomology.

Then

`baseChangeMap φ f f' g w M hM hJ n :
Hⁿ_R(X, M) ⟶ (ModuleCat.restrictScalars φ.hom).obj (Hⁿ_{R'}(X', g^* M))`

is the `R`-linear (equivalently, `φ`-semilinear) map defined as the composite

1. `(relativeCohomology f n).map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)
   : Hⁿ_R(X, M) ⟶ Hⁿ_R(X, g_* g^* M)`, induced by Mathlib's adjunction unit
   `M ⟶ g_* g^* M`;
2. the inverse of the Library's `pushforwardComparison g f (g^* M) hM n :
   Hⁿ_R(X', g^* M) ⟶ Hⁿ_R(X, g_* g^* M)`, where `X'` lies over `Spec R` through
   `g ≫ f`; it is an isomorphism by the Library's `isIso_pushforwardComparison`
   applied to `hM` and `hJ`;
3. the component at `g^* M` of `relativeCohomologyBaseRingIso φ (g ≫ f) f' w n`,
   identifying `Hⁿ_R(X', g^* M)` (over `Spec R` through `g ≫ f`) with
   `Hⁿ_{R'}(X', g^* M)` viewed as an `R`-module.

Informally, it is the map on cohomology induced by `M ⟶ g_* g^* M`, read on `X'`
through `Hⁿ(X, g_* N) = Hⁿ(X', N)`; in degree `0` one expects the pullback of
sections `Γ(X, M) ⟶ Γ(X', g^* M)`, but this module does not state or prove that
description.

The hypotheses are available in the intended cases. `hJ` is the `R`-module conjunct
of the Library statement
`Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicStatement` for `g` and
`f` (not yet proved). `hM` holds when `g` is a closed immersion (pending statement
`ClosedImmersionHigherDirectImageVanishingStatement`, candidate
`b5b9bd00-06c8-4e1b-b4bd-a669668176cf`) or when `g` is affine and `g^* M` is
quasi-coherent (pending statement `AffineQuasicoherentHigherDirectImageVanishingStatement`,
candidate `a9359701-4274-4e64-85d6-b1481386776e`). Neither is used or assumed by this
module.

### `baseChangeMap_naturality`

With the data of `baseChangeMap`, `u : M ⟶ N` in `X.Modules`, and `hM`, `hN` the
vanishing hypotheses for `M` and `N`,

`(relativeCohomology f n).map u ≫ baseChangeMap φ f f' g w N hN hJ n =
baseChangeMap φ f f' g w M hM hJ n ≫
(ModuleCat.restrictScalars φ.hom).map ((relativeCohomology f' n).map (g^*.map u))`.

Proof. Each factor is natural: the adjunction unit (its naturality square), the
inverse comparison (from `pushforwardComparison_naturality` applied to `g^*.map u`,
inverted), and the natural isomorphism `relativeCohomologyBaseRingIso`.

## Provenance

- Stacks Project, Chapter "Cohomology of Sheaves", source `cohomology.tex` at commit
  `a04446e57ec1fbc252a871afcec7752fb2807b14` (sha256
  `fa9747d0082afbf8b09244dcc6c260f8a122e5e3b4a3c69e2273506d76e18a42`), retained in
  the literature folder "Stacks Project - Flasque sheaves, affine vanishing and
  Kunneth over a field (source at a04446e5)" (source id
  `stacks-flasque-affine-vanishing-kunneth-a04446e5`): Section
  `section-base-change-map` (tag 02N6, line 2956), Lemma
  `lemma-base-change-map-flat-case` (tag 02N7, line 2977), Remark
  `remark-correct-version-base-change-map` (line 3035) and Lemma
  `lemma-pushforward-injective-flat` (tag 02N5, line 1821). The web pages of 02N6
  and 02N7 with their comments are retained in the literature folder "Stacks Project -
  The base change map on cohomology, tags 02N6 and 02N7 (HTML snapshot 2026-10-29)"
  (source id `stacks-base-change-map-02N6-02N7-comments`).
- Stacks 02N7 assumes the square of ringed spaces `g' : X' → X`, `f`, `f'`,
  `g : S' → S` with `g` and `g'` flat, and constructs `g^* Rf_* F → R(f')_* (g')^* F`
  in `D^+(S')`: lift the unit `F → (g')_* (g')^* F` to injective resolutions
  `I → (g')_* J` (by Lemma 02N5, `(g')_* J` is injective when `g'` is flat), push down
  to `S`, and apply the adjunction of `g^*` and `g_*`. Before that adjunction step,
  the map is `Rf_* F → g_* R(f')_* (g')^* F`. The Lean map is its `n`-th cohomology
  over affine `S = Spec R`, `S' = Spec R'`, for a single module `M` (here `g'` is the
  Lean `g`, and the Stacks `g` is `Spec.map φ`).
- The Lean construction is derived internally and differs from the Stacks proof. It
  does not lift to injective resolutions. It uses the map on derived functors induced
  by the unit, and then identifies `Hⁿ(X, g_* g^* M)` with `Hⁿ(X', g^* M)` by the
  Library's `pushforwardComparison`. This identification needs `hM`. It also needs
  `hJ`, in place of flatness of `g'`: pushforwards of injectives need only be acyclic,
  not injective. No flatness of `Spec.map φ` is needed for this form, as comment
  #5457 on tag 02N7 observes; comment #5675 notes that for non-flat `g` the
  derived-category source should be `L g^* Rf_* F`, which this adjoint form avoids.
