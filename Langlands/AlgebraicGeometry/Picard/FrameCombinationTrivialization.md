# Trivializing a line bundle by a combination of global sections

Author: Worker 766.

This module is in the namespace
`Langlands.AlgebraicGeometry.Picard.FrameCombination`. It imports Mathlib,
`Langlands.AlgebraicGeometry.Modules.TensorSections`, and modules of the Library's port of the Anthropic FLT formalization:
`Def_AlgebraicGeometry_RelativePicardFunctor` (`Scheme.Modules.IsInvertible`),
`Def_AlgebraicGeometry_ModulesSectionsTensor` (`IsFrameOn`, `unitSection`),
`Def_AlgebraicGeometry_ModulesPullbackLocalSection` (`pullbackLocalSection`),
`Def_AlgebraicGeometry_TwoChartCechSectionsOf` (`moduleSectionsOfHom`, and through
its import `Def_AlgebraicGeometry_TwoAffineOpenCover` the abbreviation
`Scheme.TwoAffineOpenCover.specMap`), and the
theorems `exists_basicOpen_forall_exists_frame_of_frame_pullback`,
`IsFrameOn.pullbackLocalSection` and `isIso_of_isFrameOn_of_iSup_eq_top`
together with the solution module of `IsFrameOn.pullbackLocalSection`.

## Purpose and provenance

This is an internal helper for the diagonal branch of the proof of
`Langlands.AlgebraicGeometry.Picard.FieldPicardSheafAlgebraicSpaceStatement`.
There one must show that the locus of a base where a line bundle `N` becomes
trivial fppf-locally is open. The fppf-local data provide a trivializing section
of the fibre over some field `K` over `B`, typically a residue field of a point
of an fppf cover, together with its coefficients in `K`. The polynomial trick
works directly with these `K`-data. It does not choose a trivializing section
over the residue field `κ(q)` of the image point and does not descend one. For a
proper fibre, triviality over `K` does imply triviality over `κ(q)` (Stacks
Project, Lemma 33.30.3, tag 0CC5), but that result is not used here, and a
particular trivializing section over `K` need not come from `κ(q)`. If the
sections of the fibre over `K` are `K`-linear combinations of finitely many
global sections `m i` from the base, the generic combination `∑ T_i • m i` over
the polynomial ring `B[T_i]` specializes, at the point `T ↦ c` with values in
`K`, to the given trivializing section. Frame lifting then spreads this to a
basic open set of `B[T_i]`. That basic open set is flat and of finite
presentation over `B`.

No literature theorem is claimed. The argument is a standard generic-section
argument, written here for the FLT port's notions of frames and invertible
modules. The use in the main proof is not part of this unit.

## Conventions

- `IsFrameOn s V`, for a section `s` of `M` over `U`, means that for every open
  `W ≤ U` with `W ≤ V` the map `g ↦ g • s|_W` from `Γ(X, W)` to `Γ(M, W)` is
  bijective. This is the FLT port's definition.
- `specMap R A` is `Spec.map (CommRingCat.ofHom (algebraMap R A))`.
- `SheafOfModules.unit X.ringCatSheaf` is the structure sheaf as a module, and
  `𝟙_ X.Modules` is the monoidal unit, which is the same object.

## Frames

- `Langlands.SchemeModule.sectionHom M s` is the published morphism sending
  `1` to the global section `s`, reused without a second definition. It is built with Mathlib's `SheafOfModules.unitHomEquiv`
  from the compatible family of restrictions `s|_U`.
- `Langlands.SchemeModule.sectionHom_app_one`: on an open `W` it sends `unitSection W`
  to `s|_W`.
- `nonempty_iso_unit_of_forall_isFrameOn`: if every point of `X` has an open
  neighbourhood `U` with `IsFrameOn s U`, then `M` is isomorphic to the
  structure sheaf. The proof applies the FLT theorem
  `isIso_of_isFrameOn_of_iSup_eq_top` to `Langlands.SchemeModule.sectionHom M s`, with the unit
  sections as frames of the source and the restrictions of `s` as frames of the
  target.
- `exists_isFrameOn_top_of_iso_unit`: an isomorphism `e : M ≅ 𝒪_X` gives a
  global section framing `M` on `⊤`, namely the image of `unitSection ⊤` under
  `e.inv`.

## Combinations of pulled-back sections

Let `φ : Y ⟶ X`, `N` a module on `X` and `s` a global section of `N`.

- `pullbackGlobalSection φ s` is the FLT section `pullbackLocalSection φ s`,
  viewed as a section of `φ^* N` over `⊤`. The lemmas `pullbackGlobalSection_def`,
  `pullbackGlobalSection_sum` and `pullbackGlobalSection_smul` restate the FLT
  lemmas; the last one reads
  `φ^*(g • s) = φ.appTop g • φ^* s` for `g : Γ(X, ⊤)`.
- `pullbackComp_app_pullbackGlobalSection`: the comparison isomorphism
  `pullbackComp φ a : φ^* a^* N ≅ (φ ≫ a)^* N` sends `φ^*(a^* s)` to
  `(φ ≫ a)^* s`. This restates a lemma of the FLT solution module.
- `comb φ N m k` is `∑ i, k i • φ^*(m i)` for a finite family `m i` of global
  sections of `N` and functions `k i : Γ(Y, ⊤)`; the scalar action is the module
  structure of `Γ(φ^* N, ⊤)` over `Γ(Y, ⊤)`.
- `pullbackComp_app_comb`: for `φ : Z ⟶ Y` and `a : Y ⟶ X`, the comparison
  isomorphism sends `φ^*(comb a N m k)` to
  `comb (φ ≫ a) N m (fun i => φ.appTop (k i))`.
- `isFrameOn_pullbackGlobalSection_comb_iff`: consequently `φ^*(comb a N m k)`
  frames on `V` exactly when `comb (φ ≫ a) N m (φ.appTop ∘ k)` does. Frames are
  transported along the isomorphism in both directions.
- `specMap_comp`: for a scalar tower `B → C → K`,
  `specMap C K ≫ specMap B C = specMap B K`.

## The polynomial trick

`exists_flat_trivialization_of_span` has the following hypotheses.

- `B : Type u` is a commutative ring, `f : X ⟶ Spec B` is universally closed and
  `N` is an invertible module on `X` (`Scheme.Modules.IsInvertible`).
- `m : ι → Γ(N, ⊤)` is a family of global sections, with `ι : Type` finite.
- `K` is a field with an algebra structure over `B`. Write `X_K` for
  `pullback f (specMap B K)`, `π` for its first projection to `X` and `κ` for its
  second projection to `Spec K`.
- `htriv`: `π^* N` is isomorphic to the structure sheaf of `X_K`.
- `hspan`: every global section of `π^* N` equals `∑ i, c i • π^*(m i)` for some
  `c : ι → K`. Here `K` acts on `Γ(π^* N, ⊤)` through `κ`, by the FLT instance
  `moduleSectionsOfHom κ`.

The conclusion provides a commutative ring `A` with a `B`-algebra structure such
that

- `A` is flat and of finite presentation over `B`;
- some prime `q` of `A` contracts to the kernel of `B → K`;
- for every scheme `Z` with morphisms `a : Z ⟶ X` and `b : Z ⟶ Spec A` such that
  `a ≫ f = b ≫ specMap B A`, the module `a^* N` is isomorphic to the structure
  sheaf of `Z`.

The last clause applies in particular to `X ×_B A`.

### Proof

1. `htriv` and `exists_isFrameOn_top_of_iso_unit` give a global section `τ` of
   `π^* N` that frames on `⊤`. By `hspan`, `τ = ∑ i, c i • π^*(m i)`.
2. Let `C = MvPolynomial ι B` and let `C → K` be evaluation at `c`; then
   `B → C → K` is a scalar tower and `X_i ↦ c i`.
3. Let `X_C = pullback f (specMap B C)` with projections `pC` to `X` and `fC` to
   `Spec C`, and `N_C = pC^* N`, which is invertible. Let `xC i` be the image of
   the variable `X_i` in `Γ(X_C, ⊤)`, and let `σ = comb pC N m xC`; this is the
   generic combination.
4. Let `qK` and `sK` be the projections of `pullback fC (specMap C K)`, the fibre
   of `X_C` over the `K`-point of `Spec C`. The morphism
   `ψ = pullback.lift (qK ≫ pC) sK` goes from it to `X_K`; the square commutes
   by `specMap_comp`.
5. Let `kK i` be the image of `c i` in `Γ(X_K, ⊤)` under `κ`. Then step 1 reads
   `τ = comb π N m kK`.
   Naturality of the inverse of `Scheme.ΓSpecIso` and `X_i ↦ c i` give
   `ψ.appTop (kK i) = qK.appTop (xC i)`.
6. `ψ^* τ` frames on `⊤` by the FLT theorem `IsFrameOn.pullbackLocalSection`.
   By `isFrameOn_pullbackGlobalSection_comb_iff`, `ψ ≫ π = qK ≫ pC` and step 5,
   `qK^* σ` frames on `⊤`.
7. The FLT theorem `exists_basicOpen_forall_exists_frame_of_frame_pullback`,
   applied to `fC`, `N_C`, the one-element family `σ`, the field `K` and the
   prime `ker(C → K)`, yields `g ∈ C` outside this prime such that every point of
   `X_C` over `D(g)` has an open neighbourhood on which `σ` frames `N_C`. Its
   hypothesis is step 6, with `⊤` as the neighbourhood of every point.
8. Take `A = C[1/g]` (`Localization.Away g`). It is flat over `C`
   (`IsLocalization.flat`) and of finite presentation over `C`
   (`IsLocalization.Away.finitePresentation`), hence flat and of finite
   presentation over `B` by transitivity. The prime `ker(C → K)` avoids `g`, so
   it is the contraction of a prime `q` of `A`
   (`PrimeSpectrum.localization_away_comap_range`), and `q` contracts to
   `ker(B → K)`.
9. Given `a` and `b` with `a ≫ f = b ≫ specMap B A`, let
   `θ = pullback.lift a (b ≫ specMap C A) : Z ⟶ X_C`. Every point of `Z` maps
   into the preimage of `D(g)`, because `g` is a unit in `A`. The local frames of
   step 7 pull back along `θ` (`IsFrameOn.pullbackLocalSection`), so
   `nonempty_iso_unit_of_forall_isFrameOn` trivializes `θ^* N_C`. Finally
   `a^* N ≅ θ^* N_C` by `Scheme.Modules.pullbackCongr` (for `θ ≫ pC = a`) and
   `Scheme.Modules.pullbackComp`.
