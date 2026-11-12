# Coproducts in localizations with a right calculus of fractions

Author: Worker 21.

This module shows that a localization functor `L : C ⥤ D` at a class `W` with
a right calculus of fractions sends suitable chosen coproducts in `C` to
coproducts in `D`. It is the categorical input for disjoint unions of analytic
spaces in the Library's localized category, which are needed for Berkovich's
induced spaces `X_{G/H}`. Everything is stated for arbitrary categories in the
namespace `Langlands.CategoryTheory`.

## Data: `RightFractionCoproducts W J`

For a morphism property `W` on `C` and an index type `J`, a term
`R : RightFractionCoproducts W J` consists of:

- `replace : C → C` and `π T : replace T ⟶ T` with `W (π T)` (`π_mem`). Every
  object is replaced by a `W`-equivalent one, for example a normalized
  presentation;
- for every family `T : J → C`, a cofan `sum T` of the family
  `j ↦ replace (T j)`, with `isColimit T : IsColimit (sum T)`;
- `desc_mem`: for families `T`, `X` and morphisms
  `s j : replace (T j) ⟶ replace (X j)` with `W (s j)` for all `j`, the induced
  morphism between the chosen coproducts,
  `Cofan.IsColimit.desc (isColimit T) (fun j => s j ≫ (sum X).inj j)`, lies in
  `W`.

Coproducts are only required for families of replacements. In the analytic
application, coproducts exist only for presentations without empty charts.
Every presentation is quasi-isomorphic to such a presentation.

## Results

Assume `[L.IsLocalization W]` and `[W.HasRightCalculusOfFractions]`.

- `localizedCofan R L T`: the cofan
  `Cofan.mk (L.obj (sum T).pt) (fun j => L.map ((sum T).inj j))` of the family
  `j ↦ L.obj (replace (T j))`.
- `map_eq_of_denominator`: let `t : Z ⟶ (sum T).pt` be in `W`, and let
  `b b' : Z ⟶ Y`. Suppose that for every `j`,
  `L.map (inj j) ≫ (L t)⁻¹ ≫ L.map b = L.map (inj j) ≫ (L t)⁻¹ ≫ L.map b'`.
  Then `L.map b = L.map b'`.
- `hom_ext`: two morphisms `L.obj (sum T).pt ⟶ Y`, for any object `Y` of `D`,
  are equal once their composites with all `L.map (inj j)` are equal.
- With `[L.EssSurj]` (true for every localization functor,
  `Localization.essSurj`):
  - `fraction W L f` and `fraction_spec`: a chosen right fraction for
    `f : L.obj X ⟶ Y`, after composing with the inverse of
    `L.objObjPreimageIso Y`;
  - `localizedDesc R T f`: the morphism out of `L.obj (sum T).pt` induced by
    a family `f j : L.obj (replace (T j)) ⟶ Y`;
  - `inj_localizedDesc`: `L.map (inj j) ≫ localizedDesc R T f = f j`;
  - `isColimitLocalizedCofan`: `localizedCofan R L T` is a colimit cofan;
  - `originalCofan R L T` and `isColimitOriginalCofan`: the same object
    `L.obj (sum T).pt` is a coproduct of the family `j ↦ L.obj (T j)`, with
    injections `(L (π (T j)))⁻¹ ≫ L.map (inj j)`.
    `originalCofan_inj_comp` gives the composite of an injection with a
    morphism.

## Proofs

Uniqueness (`map_eq_of_denominator`). For each `j`, the right Ore condition
applied to `inj j` and `t` gives `ψ_j` with
`ψ_j.s ≫ inj j = ψ_j.f ≫ t`. Hence
`L.map (inj j) ≫ (L t)⁻¹ = (L ψ_j.s)⁻¹ ≫ L ψ_j.f`, so
`L (ψ_j.f ≫ b) = L (ψ_j.f ≫ b')`. By Mathlib's `map_eq_iff_precomp`, some
`r_j ∈ W` satisfies `r_j ≫ ψ_j.f ≫ b = r_j ≫ ψ_j.f ≫ b'`. Let `u` be the
morphism out of the chosen coproduct of the replacements of the sources of
the `r_j`, with components `π ≫ r_j ≫ ψ_j.f`. Then `u ≫ b = u ≫ b'`. Also,
`u ≫ t` is the morphism induced by the `W`-morphisms `π ≫ r_j ≫ ψ_j.s`, so it
lies in `W` by `desc_mem`. Since `L (u ≫ t)` and `L t` are isomorphisms, so
is `L u`, and cancelling it gives `L b = L b'`.

`hom_ext`. Replace `Y` by `L.obj` of a preimage. Write both morphisms as right
fractions, and use the Ore condition to give them a common denominator
`t ∈ W`. Then apply `map_eq_of_denominator`.

Existence (`localizedDesc`). Write each `f j` as a right fraction
`(L s_j)⁻¹ ≫ L a_j`. Let `σ` be the morphism between chosen coproducts induced
by `π ≫ s_j`; it lies in `W` by `desc_mem`. Let `a` have components
`π ≫ a_j`. The induced morphism is `(L σ)⁻¹ ≫ L a`, followed by the
comparison isomorphism of the target. The component equation follows from
`inj j ≫ σ = (π ≫ s_j) ≫ inj j`.

## Provenance

This is an internal construction. It uses only Mathlib's right calculus of
fractions (`MorphismProperty.HasRightCalculusOfFractions`,
`Localization.exists_rightFraction`,
`MorphismProperty.map_eq_iff_precomp`). Mathlib's
`Mathlib/CategoryTheory/Localization/FiniteProducts.lean` treats finite
products without a calculus of fractions. The index type here is arbitrary,
and the right calculus of fractions replaces finiteness. No external
mathematical claim is made beyond the proved Lean statements.
