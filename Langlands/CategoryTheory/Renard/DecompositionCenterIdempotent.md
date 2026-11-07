# The central idempotent of a two-factor decomposition

Author: Worker 1842.

Module `Langlands.CategoryTheory.Renard.DecompositionCenterIdempotent`, namespace
`Langlands.Renard`.

This module is the category-theoretic part of the proof of the Corollary of Renard
VI.4.5 (printed p.160 / PDF p.166): "when an abelian category splits as a direct sum of
two categories, the projections onto the two factors are idempotents in the center of
the category. Since Z is a domain (Lemma VI.4.3), it has no nontrivial idempotent."
The statements are made for an arbitrary preadditive category `C` (object universe
`u`, Hom universe `v`). It does not prove the VI.4.5 target
`RationalInertiaBlockIndecomposableStatement`. That also needs the VI.4.1 equivalence
and the irreducible summand of VI.3.2(i), as in
`RationalInertiaBlockIndecomposableReduction`.

Source: David Renard, *Représentations des groupes réductifs p-adiques* (registered
source `renard-2026-representations-groupes-reductifs-padiques`, French version dated
9 July 2026), VI.4.5, Corollary and its proof (printed p.160 / PDF p.166); A.IX for
decompositions (printed p.268 / PDF p.274); A.X for the center of a category (printed
p.269 / PDF p.275).

Provenance: derived. Renard's proof is two sentences and is made for abelian
categories. Here the decomposition is the published `IsCategoryDecomposition` of A.IX
with two factors indexed by `Bool`. Only the preadditive structure is used, and the
domain property is replaced by two hypotheses on one test object `Q`: evaluation of the
center at `Q` is injective, and `End Q` has no zero divisors. In VI.4.5, `Q` is
`Π = ind ρ`, so the center `Z[π]` embeds into `End Π`, which is a domain.

## Conventions

`CatCenter C` is Mathlib's `End (𝟭 C)`. Its multiplication is reverse composition,
`(x * y).app X = y.app X ≫ x.app X`, and so is the multiplication of `End Q`. The Hom
functor is Mathlib's `preadditiveCoyonedaObj Q : C ⥤ ModuleCat (End Q)ᵐᵒᵖ`. It sends
`X` to `Q ⟶ X` and `f` to `φ ↦ φ ≫ f`. `IsCategoryDecomposition P` asks that every
object be the vertex of an actual coproduct cofan with one component in each `P b`, and
that every morphism between objects of `P b` and `P b'` for `b ≠ b'` be zero.

## Projections

Let `ι : ∀ b, Y b ⟶ X` be a coproduct cofan with colimit proof `hc`.

- `decompositionProj hc b : X ⟶ Y b` is the map out of the coproduct that is the
  identity on `Y b` (as `eqToHom`) and zero on the other component.
- `inj_decompositionProj_self` gives `ι b ≫ p_b = 𝟙`, and `inj_decompositionProj_ne`
  gives `ι b' ≫ p_b = 0` for `b' ≠ b`. Both follow from the universal property
  (`Cofan.IsColimit.fac`).
- `decompositionProj_sum` says `p_false ≫ ι_false + p_true ≫ ι_true = 𝟙 X`. It is
  checked on both legs of the cofan with `Cofan.IsColimit.hom_ext`.
- `comp_decompositionIdem` assumes off-diagonal Homs are zero and `Y b ∈ P b`. For
  `g : W ⟶ X` with `W ∈ P b`, `g ≫ p_true ≫ ι_true` is `g` if `b = true` and `0` if
  `b = false`. For `b = false`, `g ≫ p_true : W ⟶ Y true` is an off-diagonal Hom, hence
  zero. For `b = true`, compose the sum formula with `g` and use that
  `g ≫ p_false : W ⟶ Y false` is zero.

## The central idempotent

Fix `hP : IsCategoryDecomposition P` with `P : Bool → ObjectProperty C`.

- `decompositionIdemApp hP X` is `p_true ≫ ι_true` for the cofan chosen (by choice)
  from `hP.1 X`. `comp_decompositionIdemApp` is `comp_decompositionIdem` for it: the
  value `g ≫ e_X` does not depend on the chosen cofan.
- `decompositionIdem hP : CatCenter C` has components `decompositionIdemApp hP X`.
  Naturality at `f : X ⟶ X'` is checked on the legs `ι b` of the chosen cofan of `X`.
  Apply `comp_decompositionIdemApp` at `X'` to `ι b ≫ f` and at `X` to `ι b`, using
  `Y b ∈ P b`. Both sides are `ι b ≫ f` for `b = true` and `0` for `b = false`.
- `decompositionIdem_app_of_true` / `decompositionIdem_app_of_false`: the component is
  `𝟙 X` on objects of `P true` and `0` on objects of `P false` (apply
  `comp_decompositionIdemApp` to `𝟙 X`).
- `decompositionIdem_isIdempotentElem` is checked componentwise on the legs of the
  chosen cofan, with the same lemma.
- `isZero_of_decompositionIdem_eq_zero` / `isZero_of_decompositionIdem_eq_one`: if
  the idempotent is `0`, every object of `P true` has `𝟙 X = 0`, so it is zero. If it is
  `1`, the same holds for `P false`.

## Indecomposability from one test object

- `exists_isZero_of_decomposition Q hinj hP`: assume `[NoZeroDivisors (End Q)]` and
  that `hinj` makes `z ↦ z.app Q` injective on `CatCenter C`. Then some `b : Bool` has
  only zero objects in `P b`. The component of `decompositionIdem hP` at `Q` is an
  idempotent of `End Q`, hence `0` or `1` by `IsIdempotentElem.iff_eq_zero_or_one`. By
  injectivity the idempotent itself is `0` or `1`, and the previous lemmas conclude.
- `catCenter_app_injective_of_faithful Q`: if `preadditiveCoyonedaObj Q` is faithful,
  `z ↦ z.app Q` is injective. If `z₁.app Q = z₂.app Q`, then for every `φ : Q ⟶ X`,
  naturality gives `φ ≫ z₁.app X = z₁.app Q ≫ φ = z₂.app Q ≫ φ = φ ≫ z₂.app X`. So the
  images of `z₁.app X` and `z₂.app X` under the Hom functor agree, and faithfulness
  gives `z₁.app X = z₂.app X`.
- `exists_isZero_of_decomposition_of_faithful Q hP` combines the two.
- `exists_isZero_of_decomposition_fullSubcategory X₀ hP` is the same statement for a
  full subcategory `Q.FullSubcategory` of a preadditive `D`, with test object `X₀`.
  Its Hom functor in the full subcategory is faithful, and the *ambient* ring
  `End X₀.obj` has no zero divisors. The map `f ↦ f.hom : End X₀ → End X₀.obj` is
  injective (`ObjectProperty.hom_ext`) and preserves `0` and multiplication by `rfl`,
  so `End X₀` has no zero divisors (`Function.Injective.noZeroDivisors`).
