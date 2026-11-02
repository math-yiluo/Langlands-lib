# Extension of scalars on `Ext` groups: direct summands of finite sums

Author: Worker 61. Built on the Library module
`Langlands.Cohomology.HyperextExtBaseChange` (`HasResolutionBy`,
`HasResolutionBy.of_prop`, `extBaseChangeMap_baseChange_precompOfLinear_mk₀`,
`extBaseChangeMap_zero_bijective_iff`,
`extBaseChangeMap_injective_of_hasResolutionBy`,
`extBaseChangeMap_bijective_of_hasResolutionBy`,
`extBaseChangeEquivOfHasResolutionBy`, `HasFiniteBasis`,
`HasFiniteBasis.projective`, `HasFiniteBasis.projective_repExtendScalars`,
`repHomBaseChangeMap_bijective_of_hasFiniteBasis`; Worker 61). Through it, it
also uses `Langlands.Cohomology.HyperextScalarExtension` (`IsSemilinear`,
`extBaseChangeMap`, `repExtendScalars_isSemilinear` and the exactness
instances of `repExtendScalars`; Worker 61) and
`Langlands.Cohomology.DivisibleSystem.ScalarExtension` (`repExtendScalars`;
Worker 61). It has no direct Mathlib imports; the Mathlib lemmas named below
come in through these modules.

The module `HyperextExtBaseChange` proves that, for `S` flat over `R`, the
comparison map `extBaseChangeMap F hF X Y n : S ⊗[R] Ext^n(X, Y) → Ext^n(F X, F Y)`
is injective, respectively bijective, when `X` has a resolution of length `n`,
respectively `n + 1`, by objects in a class `Q` of projective objects `P` such
that `F P` is projective and `S ⊗[R] Hom(P, Y) → Hom(F P, F Y)` is bijective.
For representations of a monoid `G` it takes for `Q` the representations that
are free of finite rank over `R[G]` (`HasFiniteBasis`).

This module shows that the three conditions on `Q` pass to the direct summands
of finite direct sums of objects in `Q` (`IsSummandOfFiniteSum Q`), and in fact
that the comparison map in every degree passes from the objects of `Q` to these
summands. Hence the dimension-shifting theorems also hold for resolutions by
such summands, in particular, for representations, by direct summands of
finite sums of representations that are free of finite rank over `R[G]`. The
existence of the resolutions remains a hypothesis.

All declarations are in namespace `Langlands.Cohomology.HyperextScalarExtension`.

## Conventions

`Ext^n(X, Y)` is Mathlib's `Abelian.Ext.{t} X Y n`, `Ext.mk₀ g ∈ Ext^0` is the
class of a morphism `g`, and `α.comp e h` is Mathlib's composition of `Ext`
classes. For `α : Ext^0(X₁, X₂)`, `α^*` denotes Mathlib's
`α.precompOfLinear R Y (zero_add n) : Ext^n(X₂, Y) →ₗ[R] Ext^n(X₁, Y)`,
`e ↦ α.comp e (zero_add n)`. For an `R`-linear map `f`, `S ⊗ f` is Mathlib's
`f.baseChange S`. `∑ i` is a sum over all elements of a `Fintype`; for
morphisms it is the sum in the preadditive category. A resolution "of length
`n`" is as in `HyperextExtBaseChange`: an exact sequence
`P_n → ⋯ → P_0 → X → 0`.

## Summands of finite sums

Section `Summand` takes a preadditive category `C : Type uC`
(`[Category.{vC} C] [Preadditive C]`) and `Q Q' : C → Prop` (implicit).

| Declaration | Statement |
| --- | --- |
| `IsSummandOfFiniteSum Q X` | A `def` (a `Prop`): there are `ι : Type` with `Fintype ι`, objects `P : ι → C` and morphisms `a : ∀ i, X ⟶ P i`, `b : ∀ i, P i ⟶ X` such that `Q (P i)` for all `i` and `∑ i, a i ≫ b i = 𝟙 X`. |
| `IsSummandOfFiniteSum.of_prop hX` | For `hX : Q X`: `IsSummandOfFiniteSum Q X`. |
| `isSummandOfFiniteSum_of_isZero hX` | For `hX : IsZero X`: `IsSummandOfFiniteSum Q X` (for every `Q`). |
| `IsSummandOfFiniteSum.mono h hX` | For `h : ∀ P, Q P → Q' P`: `IsSummandOfFiniteSum Q X → IsSummandOfFiniteSum Q' X`. |
| `IsSummandOfFiniteSum.of_retract r hY` | For a retract `r : Retract X Y` (Mathlib: `r.i : X ⟶ Y`, `r.r : Y ⟶ X`, `r.i ≫ r.r = 𝟙 X`) and `hY : IsSummandOfFiniteSum Q Y`: `IsSummandOfFiniteSum Q X`. |
| `IsSummandOfFiniteSum.biproduct X hX` | For `J : Type` with `Fintype J`, `X : J → C` with `[HasBiproduct X]` and `hX : ∀ j, IsSummandOfFiniteSum Q (X j)`: `IsSummandOfFiniteSum Q (⨁ X)`. |
| `projective_of_sum_comp_eq_id a b hab hP` | For a finite type `ι`, `P : ι → C`, `a : ∀ i, X ⟶ P i`, `b : ∀ i, P i ⟶ X`, `hab : ∑ i, a i ≫ b i = 𝟙 X` and `hP : ∀ i, Projective (P i)`: `Projective X`. |
| `IsSummandOfFiniteSum.projective hproj hX` | For `hproj : ∀ P, Q P → Projective P` and `hX : IsSummandOfFiniteSum Q X`: `Projective X`. |
| `IsSummandOfFiniteSum.projective_map F hFproj hX` | For a preadditive category `D` and an additive functor `F : C ⥤ D` (`[F.Additive]`), `hFproj : ∀ P, Q P → Projective (F.obj P)` and `hX : IsSummandOfFiniteSum Q X`: `Projective (F.obj X)`. |

Section `SummandResolution` takes an abelian category `C` and `Q` (implicit).

| Declaration | Statement |
| --- | --- |
| `IsSummandOfFiniteSum.hasResolutionBy hX n` | For `hX : IsSummandOfFiniteSum Q X`: `HasResolutionBy (IsSummandOfFiniteSum Q) n X`, for every `n : ℕ`. |

In a category with finite biproducts, `IsSummandOfFiniteSum Q X` says that `X`
is a retract of a finite biproduct `⨁ P` of objects in `Q` (with `a` and `b`
the components of the two maps); the definition avoids choosing biproducts.

Proofs.

- `of_prop`: `ι = Unit`, `P = X`, `a = b = 𝟙 X`.
- `isSummandOfFiniteSum_of_isZero`: `ι = Empty`; the empty sum `0` equals
  `𝟙 X` because `X` is a zero object (`IsZero.eq_of_src`).
- `mono`: the same data.
- `of_retract`: take `r.i ≫ a i` and `b i ≫ r.r`. Then
  `∑ i, (r.i ≫ a i) ≫ b i ≫ r.r = r.i ≫ (∑ i, a i ≫ b i) ≫ r.r = r.i ≫ r.r = 𝟙 X`
  (Mathlib's `Preadditive.sum_comp`, `Preadditive.comp_sum`).
- `biproduct`: choose the data `ι j, P j, a j, b j` for each `X j` and index by
  the sigma type `Σ j, ι j`, with `biproduct.π X j ≫ a j i` and
  `b j i ≫ biproduct.ι X j`. The double sum (`Fintype.sum_sigma`) is
  `∑ j, biproduct.π X j ≫ (∑ i, a j i ≫ b j i) ≫ biproduct.ι X j =
  ∑ j, biproduct.π X j ≫ biproduct.ι X j = 𝟙 (⨁ X)` (`biproduct.total`).
- `projective_of_sum_comp_eq_id`: given `f : X ⟶ Z` and an epimorphism
  `e : E ⟶ Z`, lift each `b i ≫ f` through `e` to `l i : P i ⟶ E`; then
  `(∑ i, a i ≫ l i) ≫ e = (∑ i, a i ≫ b i) ≫ f = f`.
- `projective` and `projective_map`: `projective_of_sum_comp_eq_id`; for
  `projective_map` with `F.map (a i)` and `F.map (b i)`, whose sum of
  composites is `F.map (𝟙 X) = 𝟙 (F.obj X)` because `F` is additive
  (`Functor.map_sum`).
- `hasResolutionBy`: the Library's `HasResolutionBy.of_prop` with the zero
  object, which is such a summand by `isSummandOfFiniteSum_of_isZero`.

## `Ext` of summands

Section `Ext` begins with a lemma for an abelian category `C` with
`[HasExt.{t} C]`:

| Declaration | Statement |
| --- | --- |
| `sum_mk₀_comp_mk₀_comp_eq_self a b hab e` | For a finite type `ι`, `P : ι → C`, `a : ∀ i, X ⟶ P i`, `b : ∀ i, P i ⟶ X` with `hab : ∑ i, a i ≫ b i = 𝟙 X` and `e : Ext^n(X, Y)`: `∑ i, (Ext.mk₀ (a i)).comp ((Ext.mk₀ (b i)).comp e (zero_add n)) (zero_add n) = e`. |

The rest of the section takes commutative rings `R`, `S` with `[Algebra R S]`
(implicit), an `R`-linear abelian category `C`, an `S`-linear abelian category
`D`, a functor `F : C ⥤ D` (explicit) with `[F.Additive]
[PreservesFiniteLimits F] [PreservesFiniteColimits F]`, `[HasExt.{t} C]`,
`[HasExt.{t'} D]`, `hF : IsSemilinear R S F` and `Y : C` (both explicit), as in
`HyperextExtBaseChange`. Write `φ_X^n = extBaseChangeMap F hF X Y n`. In the
first two theorems `ι` is a finite type, `P : ι → C`, and `a`, `b`, `hab` are
as in `sum_mk₀_comp_mk₀_comp_eq_self`; no flatness is assumed in them.

| Declaration | Statement |
| --- | --- |
| `extBaseChangeMap_injective_of_sum_comp_eq_id F hF Y a b hab n h` | For `h : ∀ i, Function.Injective (φ_{P i}^n)`: `φ_X^n` is injective. |
| `extBaseChangeMap_surjective_of_sum_comp_eq_id F hF Y a b hab n h` | For `h : ∀ i, Function.Surjective (φ_{P i}^n)`: `φ_X^n` is surjective. |
| `IsSummandOfFiniteSum.extBaseChangeMap_bijective F hF Y n hQ hX` | For `Q : C → Prop`, `hQ : ∀ P, Q P → Function.Bijective (φ_P^n)` and `hX : IsSummandOfFiniteSum Q X`: `φ_X^n` is bijective. |

From `extBaseChangeMap_injective_of_hasResolutionBy_summand` on the section
takes `Q : C → Prop` (implicit) and the hypotheses of
`HyperextExtBaseChange` on `Q`:

- `hproj : ∀ P, Q P → Projective P`,
- `hFproj : ∀ P, Q P → Projective (F.obj P)`,
- `hQ : ∀ P, Q P → Function.Bijective (φ_P^0)`.

| Declaration | Statement |
| --- | --- |
| `extBaseChangeMap_injective_of_hasResolutionBy_summand F hF Y hproj hFproj hQ n hX` | For `[Module.Flat R S]` and `hX : HasResolutionBy (IsSummandOfFiniteSum Q) n X`: `φ_X^n` is injective. |
| `extBaseChangeMap_bijective_of_hasResolutionBy_summand F hF Y hproj hFproj hQ n hX` | For `[Module.Flat R S]` and `hX : HasResolutionBy (IsSummandOfFiniteSum Q) (n + 1) X`: `φ_X^n` is bijective. |
| `extBaseChangeEquivOfHasResolutionBySummand F hF Y hproj hFproj hQ n hX` | Under the same hypotheses, the `S`-linear equivalence `S ⊗[R] Ext^n(X, Y) ≃ₗ[S] Ext^n(F X, F Y)` with underlying map `φ_X^n`. A `def`. |
| `extBaseChangeEquivOfHasResolutionBySummand_apply F hF Y hproj hFproj hQ n hX z` | Its value at `z` is `φ_X^n z` (a `simp` lemma, by definition). |

Proofs.

- `sum_mk₀_comp_mk₀_comp_eq_self`: by associativity with a degree-`0` class
  (Mathlib's `Ext.comp_assoc_of_second_deg_zero`) and `Ext.mk₀_comp_mk₀`, the
  left side is `∑ i, (Ext.mk₀ (a i ≫ b i)).comp e _ =
  (Ext.mk₀ (∑ i, a i ≫ b i)).comp e _` (`Ext.sum_comp`, `Ext.mk₀_sum`), which
  is `(Ext.mk₀ (𝟙 X)).comp e _ = e` (`Ext.mk₀_id_comp`).
- `extBaseChangeMap_injective_of_sum_comp_eq_id`: by the previous lemma and
  induction on tensors (`TensorProduct.inductionOn`; on `s ⊗ e` with
  `LinearMap.baseChange_tmul` and `TensorProduct.tmul_sum`), every
  `z ∈ S ⊗[R] Ext^n(X, Y)` satisfies
  `z = ∑ i, (S ⊗ (Ext.mk₀ (a i))^*) ((S ⊗ (Ext.mk₀ (b i))^*) z)`. If
  `φ_X^n z = 0`, then by the Library's naturality lemma
  `extBaseChangeMap_baseChange_precompOfLinear_mk₀`,
  `φ_{P i}^n ((S ⊗ (Ext.mk₀ (b i))^*) z) =
  (Ext.mk₀ (F.map (b i))).comp (φ_X^n z) _ = 0` (`Ext.comp_zero`), so
  `(S ⊗ (Ext.mk₀ (b i))^*) z = 0` by injectivity of `φ_{P i}^n`, and `z = 0`.
- `extBaseChangeMap_surjective_of_sum_comp_eq_id`: since `F` is additive,
  `∑ i, F.map (a i) ≫ F.map (b i) = 𝟙 (F.obj X)`. Given
  `y : Ext^n(F X, F Y)`, choose `t i` with
  `φ_{P i}^n (t i) = (Ext.mk₀ (F.map (b i))).comp y _`. By naturality,
  `φ_X^n (∑ i, (S ⊗ (Ext.mk₀ (a i))^*) (t i)) =
  ∑ i, (Ext.mk₀ (F.map (a i))).comp ((Ext.mk₀ (F.map (b i))).comp y _) _`,
  which is `y` by `sum_mk₀_comp_mk₀_comp_eq_self` in `D`.
- `IsSummandOfFiniteSum.extBaseChangeMap_bijective`: the two previous theorems.
- `extBaseChangeMap_injective_of_hasResolutionBy_summand`,
  `extBaseChangeMap_bijective_of_hasResolutionBy_summand` and
  `extBaseChangeEquivOfHasResolutionBySummand`: the Library's
  `extBaseChangeMap_injective_of_hasResolutionBy`,
  `extBaseChangeMap_bijective_of_hasResolutionBy` and
  `extBaseChangeEquivOfHasResolutionBy` applied to the class
  `IsSummandOfFiniteSum Q`, whose three hypotheses hold by
  `IsSummandOfFiniteSum.projective`, `IsSummandOfFiniteSum.projective_map` and
  `IsSummandOfFiniteSum.extBaseChangeMap_bijective` (degree `0`).

## Representations

Section `Rep` takes a commutative ring `R : Type uR` and a monoid
`G : Type uG` (implicit), a commutative ring `S : Type uS` with
`[Algebra R S]` (explicit), `[Module.Flat R S]`,
`[HasExt.{t} (Rep.{max uS w} R G)]`, `[HasExt.{t'} (Rep.{max uS w} S G)]` and
`Y : Rep.{max uS w} R G` (explicit); `X : Rep.{max uS w} R G` is implicit. As
in `HyperextExtBaseChange`, `E = repExtendScalars.{max uS w} R S G` is the
Library's extension of scalars `Rep.{max uS w} R G ⥤ Rep.{max uS w} S G`,
`X ↦ S ⊗[R] X`, `hE = repExtendScalars_isSemilinear.{max uS w} R S G`, and
`HasFiniteBasis P` says that `P` is free of finite rank over `R[G]`.

| Declaration | Statement |
| --- | --- |
| `repExtBaseChangeMap_injective_of_hasResolutionBy_summand S Y n hX` | For `hX : HasResolutionBy (IsSummandOfFiniteSum HasFiniteBasis) n X`: `extBaseChangeMap E hE X Y n : S ⊗[R] Ext^n(X, Y) → Ext^n(E.obj X, E.obj Y)` is injective. |
| `repExtBaseChangeMap_bijective_of_hasResolutionBy_summand S Y n hX` | For `hX : HasResolutionBy (IsSummandOfFiniteSum HasFiniteBasis) (n + 1) X`: `extBaseChangeMap E hE X Y n` is bijective. |
| `repExtBaseChangeEquivOfHasResolutionBySummand S Y n hX` | Under the same hypotheses, the `S`-linear equivalence `S ⊗[R] Ext^n(X, Y) ≃ₗ[S] Ext^n(E.obj X, E.obj Y)` with underlying map `extBaseChangeMap E hE X Y n`. A `def`. |
| `repExtBaseChangeEquivOfHasResolutionBySummand_apply S Y n hX z` | Its value at `z` is `extBaseChangeMap E hE X Y n z` (a `simp` lemma, by definition). |

Proofs. The general theorems of the previous section for `F = E` and
`Q = HasFiniteBasis`, with the Library's `HasFiniteBasis.projective`,
`HasFiniteBasis.projective_repExtendScalars`, and
`extBaseChangeMap_zero_bijective_iff` combined with
`repHomBaseChangeMap_bijective_of_hasFiniteBasis`.

## Provenance and interpretation

The statements, definitions and proofs are ours, assembled from Mathlib and the
Library. That additive invariants such as the comparison map on `Ext` pass to
direct summands of finite sums is standard homological algebra.

Motivation from Harris 1999 (source
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`; Harris,
*Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39-2 (1999), 299-318). In the proof of Proposition 4.4 (the spectral
sequence (4.4.1) of `𝒪_m`-modules with `E_2` terms `Ext^i` in the category of
smooth `𝒪_m[GJ]`-modules, printed p.309, one-based PDF page 11), Harris
computes `H_c^•(M̆_N, 𝒪_m)` by complexes of projective modules. Printed p.310
(one-based PDF page 12), read in the rendered scan:

- "Projectivity of the modules `Z^{i,j}` is shown by realizing them as
  compactly induced from smooth representations `N^{i,j}` of compact (mod
  center) open subgroups `U^{i,j}` of `GJ`."
- "For general `ℓ`, we need to replace `N^{i,j}` by `U^{i,j}`-projective
  resolutions. More precisely, let `C^•(ẽ)` be the complex
  `C_m^•(U(ẽ)_F̄) ⊗_{ℤ/ℓ^mℤ} 𝒪_m`, where `C_m^•` is the complex constructed in
  §2. Then `C^•(ẽ)` is projective and computes the finite `S(ẽ)`-module
  `H_c^j(U(ẽ), 𝒪_m)`."
- "Since (recalling that `ẽ = (e, N, δ)`) (4.4.4)
  `Z^{i,j} = ⊕_{dim(e)=n-1-i} C^j(ẽ) = ⊕_{(e,δ)∈O_i} c-Ind_{S(ẽ)}^{GJ} C^j(ẽ)`
  is a sum of compactly induced modules, the argument goes through as before."

Interpretation (explanation only). The terms of these resolutions are
projective modules and direct sums of compactly induced modules, rather than
free modules of finite rank. Over a group ring, a finitely generated projective
module is a direct summand of a free module of finite rank; this module
extends the comparison theorems of `HyperextExtBaseChange` from resolutions by
objects of a class `Q` to resolutions by direct summands of finite sums of
objects of `Q`, so that projective terms of this kind are allowed. That every
finitely generated projective `R[G]`-module is such a summand is not
formalized, and the smooth setting of Harris's `GJ`-modules is not treated
here.

## Scope

- Only finite sums are treated. Harris's sums in (4.4.4) are indexed by the
  orbits `O_i`; whether they are finite, and the identification of `Z^{i,j}`
  or `C^j(ẽ)` with objects of the Library, are not addressed.
- The Rep corollaries concern representations of an abstract monoid `G`;
  smooth representations of a topological group are not treated in this
  module.
- The existence of resolutions by summands of finite sums is a hypothesis; it
  is not verified for any object.
- `HasExt` is a hypothesis; the results hold for each such instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.309-310 (one-based PDF pages 11-12), read in the rendered scans.

Dependencies: `Langlands.Cohomology.HyperextExtBaseChange`, with Mathlib
pinned to Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
