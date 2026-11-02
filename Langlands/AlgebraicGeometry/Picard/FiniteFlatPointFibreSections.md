# Sections of a line bundle twisted by the pullback of a rational point

Author: Worker 935.

Module `Langlands.AlgebraicGeometry.Picard.FiniteFlatPointFibreSections`, namespace
`Langlands.AlgebraicGeometry.Picard.FiniteFlatPointFibre`. Throughout, `K` is a field,
`𝒪` is the structure sheaf (`structureSheaf`), `Γ_π` is the Library's
`relativeGlobalSections π`, the global sections as a `K`-module for `π : X ⟶ Spec K`, and
`f.finrank y` is Mathlib's native degree `Scheme.Hom.finrank` of a finite flat morphism at a
point.

## Role and provenance

This is internal infrastructure for task `6b1ab3e8-b3b0-4567-9251-7566e7a6dba3`, which
proves the published `Langlands.AbelianScheme.AlgClosedFieldMumfordDualEulerStatement`.
The module is Step 6 of that task's route. Step 6 computes the dimension of the global
sections of the one nonzero higher direct image `R^g p_* Q`, after Steps 1–4 identify it
with `N ⊗ f^*(e_* 𝒪_K)`. Here `f` is the finite flat Mumford map and `e` is the origin of
the dual. Step 6 also shows that this module has finite closed support. The final proof
of the task will use this module; it is not that proof.

Source: B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), proof of (9.11), printed p.132
(PDF p.136). There, flat base change gives `R^g p_{2,*}Λ(L) = φ_L^*(R^g p'_{2,*}P) = i_*𝒪_{K(L)}`,
whose space of sections has dimension `deg(φ_L)`, giving formula (8). The source's
second computation trivializes a line bundle over the finite scheme `K(L)`. This
module proves the general form of these facts. Here `f` is any finite flat morphism of
schemes over `K` and `e` any `K`-point of the target. Flat base change is not yet proved
in the Library. Its published statement `FlatHigherDirectImageBaseChangeStatement` is an
explicit hypothesis, used only in degree `0` and only along the closed immersion `e`. On
the finite fibre the line bundle is not trivialized. Instead its sections are compared
with those of `𝒪` through the Library's Euler-polynomial theory. No literature definition
is formalized here. The anchor proposition `FiniteFlatPointFibreSectionsStatement` is
internal. It only collects the two main theorems into one proposition, and it is proved
in the same module.

## The anchor statement

```lean
def FiniteFlatPointFibreSectionsStatement : Prop :=
  FlatHigherDirectImageBaseChangeStatement.{u} →
    ∀ (K : Type u) [Field K] (Y D : Scheme.{u}) (πY : Y ⟶ Spec (CommRingCat.of K))
      (πD : D ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ D), IsFinite f → Flat f → f ≫ πD = πY →
    ∀ (e : Spec (CommRingCat.of K) ⟶ D), e ≫ πD = 𝟙 _ → ∀ (N : LineBundle Y),
      HasFiniteClosedSupport (tensorObj N.obj ((Scheme.Modules.pullback f).obj
          ((Scheme.Modules.pushforward e).obj (structureSheaf (Spec (CommRingCat.of K)))))) ∧
        ∀ x : Spec (CommRingCat.of K),
          Module.finrank K ((relativeGlobalSections πY).obj
            (tensorObj N.obj ((Scheme.Modules.pullback f).obj
              ((Scheme.Modules.pushforward e).obj
                (structureSheaf (Spec (CommRingCat.of K))))))) = f.finrank (e x)
```

In words: assume flat base change for higher direct images. Let `Y` and `D` be schemes over
`K`, let `f : Y ⟶ D` be finite and flat over `K`, let `e` be a `K`-point of `D` (a section of
`πD`), and let `N` be a line bundle on `Y`. Then `N ⊗ f^*(e_* 𝒪_K)` has finite closed support,
and its global sections over `K` have dimension `f.finrank (e x)`, the native degree of `f`
at the point `e x`. Since `Spec K` has exactly one point, the quantifier over `x` just
names that point. The theorem `finiteFlatPointFibreSections` proves the statement by
pairing the two theorems below.

## Finite schemes over a field

Let `j : F ⟶ Spec K` be finite.

- `discreteTopology_of_isFinite`: `F` is discrete. A finite morphism is locally
  quasi-finite, so `F` is locally Artinian (`IsLocallyArtinian.of_locallyQuasiFinite`).
- `isNoetherian_of_isFinite`: `F` is Noetherian. It is affine because `j` is affine, and
  locally Noetherian because `j` is locally of finite type over a field.
- `hasSupportDimensionLT_one_of_isFinite` and `hasFiniteClosedSupport_of_isFinite`: every
  `𝒪_F`-module has support of dimension `< 1`, using that a discrete space has Krull
  dimension `0`. Hence, `F` being Noetherian, it has finite closed support
  (`HasSupportDimensionLT.hasFiniteClosedSupport`).
- `eulerCharacteristic_eq_finrank_of_isFinite`: for a module `M` with finite cohomology,
  `eulerCharacteristic j M = dim_K Γ_j(M)`. This is the published
  `eulerCharacteristic_eq_finrank_of_finiteClosedSupport` composed with
  `relativeCohomologyZeroIso`.
- `finrank_relativeGlobalSections_lineBundle`: for every line bundle `L` on `F`,
  `dim_K Γ_j(L) = dim_K Γ_j(𝒪_F)`. Proof: `𝒪_F` has support of dimension `< 1`, so by the
  published `hasVanishingEulerDifference_of_support` with `e = 1`, the first forward
  difference of the Euler sequence `n ↦ χ(𝒪_F ⊗ L^{⊗n})` vanishes. In particular its values at
  `n = 1` and `n = 0` agree. At `n = 1` the module is `𝒪_F ⊗ L^{⊗1} ≅ L` (`tensorPowOneIso`,
  `tensorLeftUnitor`), and at `n = 0` it is `χ(𝒪_F)`
  (`coherentEulerSequence_eval_zero`). Both Euler characteristics equal dimensions of global
  sections by the previous item.
- `finrank_relativeGlobalSections_structureSheaf`: if `j` is moreover flat, then
  `dim_K Γ_j(𝒪_F) = j.finrank x` for the point `x` of `Spec K`. This is the published
  `FiniteEtale.homFinrank_eq_coordinateFinrank`.

## Base change to the fibre

Let `f : Y ⟶ D` be flat and `e : Spec K ⟶ D` a closed immersion. Write `F = pullback e f`
for the fibre, `i = pullback.snd e f : F ⟶ Y` and `j = pullback.fst e f : F ⟶ Spec K`.

- `pullbackPushforwardUnitIso flat f e : f^*(e_* 𝒪_K) ≅ i_* 𝒪_F`. It applies the hypothesis
  `flat` in degree `0` to the cartesian square `IsPullback.of_hasPullback e f`. The
  hypothesis needs `e` quasi-compact and separated, which holds since `e` is a closed
  immersion, and `f` flat. The degree-`0` direct images are identified with
  pushforwards (`higherDirectImageZeroIso`), and `j^* 𝒪_K ≅ 𝒪_F` by `pullbackUnitIso`.
- `tensorPullbackPushforwardUnitIso flat f e N : N ⊗ f^*(e_* 𝒪_K) ≅ i_*(i^* N)`. It
  composes the previous isomorphism with the published projection formula
  `lineBundleProjectionIso i N 𝒪_F : N ⊗ i_* 𝒪_F ≅ i_*(i^* N ⊗ 𝒪_F)` and the right unitor.
- `relativeGlobalSectionsPushforwardIso i π M : Γ_π(i_* M) ≅ Γ_{i ≫ π}(M)` comes from
  Mathlib's `Scheme.Modules.pushforwardComp`.

## Main theorems

`finrank_relativeGlobalSections_tensor_pullback_pushforward flat πY πD f hf e he N x`
assumes that `f` is finite and flat, `hf : f ≫ πD = πY` and `he : e ≫ πD = 𝟙`, and proves

`dim_K Γ_{πY}(N ⊗ f^*(e_* 𝒪_K)) = f.finrank (e x)`.

Proof. `e` is a closed immersion by Mathlib's `isClosedImmersion_of_comp_eq_id`, because it
is a section of `πD` and `Spec K` is a single point. From the pullback square,
`i ≫ πY = j`. The two isomorphisms above turn the left side into `dim_K Γ_j(i^* N)`. The
morphism `j` is finite and flat, being a base change of `f`, so the finite-scheme results
give `dim_K Γ_j(i^* N) = dim_K Γ_j(𝒪_F) = j.finrank x`. Here `i^* N` is a line bundle by
`LineBundle.pullback`. Finally, Mathlib's `Scheme.Hom.finrank_pullback_fst` gives
`j.finrank x = f.finrank (e x)`.

`hasFiniteClosedSupport_tensor_pullback_pushforward flat πD f e he N` proves that
`N ⊗ f^*(e_* 𝒪_K)` has finite closed support, under the same hypotheses on `f` and `e`.
Proof. Finite closed support is invariant under isomorphism
(`hasFiniteClosedSupport_iff_of_iso`), so it suffices to treat `i_*(i^* N)`. Its stalk
support is the image under `i` of the stalk support of `i^* N`
(`stalkSupport_pushforward`, since `i` is a closed embedding). That support is a finite
set of closed points of `F` because `j` is finite. A closed embedding maps it to a finite
set of closed points of `Y`.

## Assumptions

The only hypothesis beyond those on `f`, `e` and `N` is
`FlatHigherDirectImageBaseChangeStatement`, which is not proved here. The field `K` is
arbitrary; it need not be algebraically closed. The module uses no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`.
