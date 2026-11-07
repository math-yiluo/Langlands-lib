# Adjunctions from a counit on a copresenting subcategory

Module `Langlands.CategoryTheory.CopresentedCounitAdjunction`, namespace `Langlands`.

This is general category theory. Nothing here is specific to representations. It
isolates the formal part of the argument in Renard 2026, VI.9.6, printed pp.201–202
(PDF pp.207–208). There Renard first proves second adjointness (VI.9.6.1) for
representations of the form `π~`, then extends it to every smooth `π` through the exact
sequence `0 → π → π~~ → π₁~~`, where `π₁ = π~~/π`. The construction below is an internal
abstraction of that step, so it has no separate citation. The Lean route works with
counits rather than with Renard's diagram of exact `Hom` sequences, and the two are
equivalent.

## Factorisation through a monomorphism

Let `E F : C ⥤ C`, `S : ObjectProperty C`, `ε' : E ⟶ F` and `ι : 𝟭 C ⟶ F`.

- `liftOfMonoFactorisation ε' ι hmono hfac : S.ι ⋙ E ⟶ S.ι`. The hypotheses are:
  - `hmono`: `ι.app X` is a monomorphism for every `S`-object `X`.
  - `hfac`: for every `S`-object `X` there is some `e : E X ⟶ X` with
    `e ≫ ι.app X = ε'.app X`.

  The component at `X` is the chosen `e`. Naturality on morphisms between `S`-objects
  is checked after composing with the monomorphism `ι.app Y`, using naturality of `ε'`
  and of `ι`.
- `liftOfMonoFactorisation_app_comp`: the defining equation
  `(lift).app X ≫ ι.app X = ε'.app X`.
- `eq_liftOfMonoFactorisation_app`: any factorisation `e` equals the lift, because
  `ι.app X` is mono.

## Kernel copresentations

Assume `C` has zero morphisms. A `KernelCopresentation S X` consists of:

- `S`-objects `obj₀` and `obj₁`;
- morphisms `ι : X ⟶ obj₀` and `k : obj₀ ⟶ obj₁` with `ι ≫ k = 0`;
- a proof `isLimit` that `KernelFork.ofι ι w` is a limit cone, so `X` is a kernel of `k`;
- the extension property `extend`: every morphism from `X` to an `S`-object `Z`
  factors as `ι ≫ h₀` for some `h₀ : obj₀ ⟶ Z`.

Lemmas:

- `KernelCopresentation.mono_ι`: the inclusion `ι` is mono.
- `KernelCopresentation.map_w`: a functor `R` preserving zero morphisms satisfies
  `R.map ι ≫ R.map k = 0`.

## Extending the counit

Let `L : D ⥤ C` and `R : C ⥤ D` both preserve zero morphisms, and let
`ε : S.ι ⋙ R ⋙ L ⟶ S.ι`.

- `counit_naturality_of_mem`: naturality of `ε`, restated for morphisms of `C` between
  `S`-objects.
- `counit_comp_k_eq_zero`, `extendedCounit`, `extendedCounit_ι`. Given a copresentation
  `c` of `X`, the composite `L R X ⟶ L R obj₀ ⟶ obj₀` vanishes after `k`. This uses
  naturality of `ε` along `k` together with `R.map ι ≫ R.map k = 0`. The composite
  therefore lifts uniquely through the kernel `X`; the lift is `extendedCounit L R ε c`.
- `extendedCounit_naturality_of_mem`: for `h : X ⟶ Z` with `Z` an `S`-object,
  `L (R h) ≫ ε_Z = extendedCounit c ≫ h`. First factor `h` through `ι` with `extend`,
  then use naturality of `ε`.
- `extendedCounit_naturality`: for any `f : X ⟶ Y` and copresentations `cX` and `cY`,
  the extended counits commute with `L (R f)` and `f`. To prove this, cancel the mono
  `cY.ι` and apply the previous lemma to `f ≫ cY.ι`.
- `extendedCounit_eq_of_mem`: on an `S`-object the extended counit is `ε` itself.
- `bijective_extendedCounit`. Assume:
  - `hbij`: `g ↦ L g ≫ ε_Z` is bijective on `τ ⟶ R Z` for every `S`-object `Z` and
    every `τ`;
  - `hc`: `R` sends the kernel fork of `c` to a kernel fork.

  Then `g ↦ L g ≫ extendedCounit c` is bijective on `τ ⟶ R X`. Injectivity comes from
  injectivity at `obj₀` after composing with the mono `R.map ι`. For surjectivity, take
  `h : L τ ⟶ X` and lift `h ≫ ι` at `obj₀` to some `g₀`. Injectivity at `obj₁` gives
  `g₀ ≫ R k = 0`. Then `g₀` factors through the kernel `R X`.
- `adjunctionOfCopresentedCounit L R ε hbij c hc : L ⊣ R`, built with
  `Adjunction.mkOfHomEquiv`. Its hom equivalence is the inverse of
  `g ↦ L g ≫ extendedCounit (c X)`. The required naturality on the right is
  `extendedCounit_naturality`.
- `adjunctionOfCopresentedCounit_counit_app`: the counit at `X` is
  `extendedCounit L R ε (c X)`.
- `adjunctionOfCopresentedCounit_counit_app_of_mem`: on an `S`-object the counit is `ε`.
