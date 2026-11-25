/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.LocalDuality
public import WeilConjectures.WeilSheaf.RealPurity

/-!
# Exactness of the ordinary direct image at a fixed pure weight

The ordinary direct image `j_*` along a dense open immersion of smooth curves is only left
exact in general. The obstruction to surjectivity on the right is the connecting map
`δ : j_*F₂ → R¹j_*F₁` of the long exact sequence of cohomology sheaves of the derived direct
image `Rj_*` applied to the triangle `F₁ → F → F₂ →`. It vanishes on the open, where `j_*F → j_*F₂`
restricts to the epimorphism `F → F₂`. At a missing point the source has weights at most `w` by
semicontinuity, while local boundary duality
(`AlgebraicGeometry.exists_linearEquiv_dual_stalk_higherDirectImage`) identifies `(R¹j_*F₁)_s̄`
with the dual of the middle-extension stalk of `F₁^∨`, twisted by `(-1)`, whose weights are
therefore at least `w + 2`. A Frobenius-equivariant map across this strict weight gap is zero
(`FrobeniusModule.eq_zero_of_hasWeightsAtMost_of_dual`), so `δ` vanishes on every geometric
stalk, hence vanishes, and `j_*` is exact on short exact sequences of lisse sheaves of one and
the same pure weight.

Purity of the middle term is not needed: only the outer two terms enter the weight estimates.

## Main statements

- `AlgebraicGeometry.shortExact_map_directImage`: exactness of `j_*` at a fixed pure weight.

## Implementation notes

The curve is assumed separated, quasi-compact and geometrically connected over `k₀`, the
hypotheses under which boundary semicontinuity
(`AlgebraicGeometry.WeilSheaf.IsLisse.hasWeightsAtMost_directImage`) is stated; quasi-compactness
is also needed for the derived direct image `Rj_*` to be defined. The blueprint reduces the
general case to this one by restricting to a connected affine neighbourhood of the missing point
and replacing `k₀` by its algebraic closure in the function field; neither the compatibility of
`j_*` and `R¹j_*` with restriction to opens nor the change of the base field of Weil sheaves is
available, and the case needed (`C₀ = 𝔸¹_{k₀}`) satisfies these hypotheses.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/--
For a short exact sequence `0 → F₁ → F → F₂ → 0` of lisse Weil sheaves on a dense open `U₀` of
a smooth curve, with `F₁` and `F₂` punctually `ι`-pure of one and the same weight `w`, the
ordinary direct images form a short exact sequence on the curve:

```
  0 ──▶ F₁ ──▶ F ──▶ F₂ ──▶ 0        on U₀
        │      │      │
     j_*│   j_*│   j_*│
        ▼      ▼      ▼
  0 ▶ j_*F₁ ▶ j_*F ▶ j_*F₂ ▶ 0        on X
```
The curve is assumed separated, quasi-compact and geometrically connected over `k₀` (see the
implementation notes of this file).
(blueprint: `proposition-exactness-fixed-pure-weight--1`)
-/
theorem shortExact_map_directImage (ι : PadicAlgCl l →+* ℂ)
    {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [IsDominant j]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]
    (S : ShortComplex (WeilSheaf k₀ l U)) (hS : S.ShortExact)
    (h₁ : S.X₁.IsLisse) (_h₂ : S.X₂.IsLisse) (h₃ : S.X₃.IsLisse) {w : ℝ}
    (p₁ : S.X₁.IsPunctuallyPureOfWeight ι w)
    (p₃ : S.X₃.IsPunctuallyPureOfWeight ι w) :
    (S.map (WeilSheaf.directImage j)).ShortExact := by
  change (S.map (WeilSheaf.lowerStar j)).ShortExact
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over j (Spec (CommRingCat.of k₀))]
    infer_instance
  have := hS.epi_g
  -- Step 1: the triangle `Rj_*F₁ → Rj_*F → Rj_*F₂ →` and its sequence of cohomology sheaves
  let T := (WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) j).mapTriangle.obj
    (WeilSheaf.singleTriangle hS)
  have hT : T ∈ distTriang _ := (WeilComplex.derivedLowerStar j).map_distinguished _
    (WeilSheaf.singleTriangle_distinguished hS)
  have h01 : (0 : ℤ) + 1 = ((1 : ℕ) : ℤ) := by norm_num
  -- `𝓗⁰(Rj_* -)` is `j_*`, naturally
  have n₁ : (WeilComplex.homologySheaf 0).map T.mor₁ ≫
      (WeilSheaf.homologySheafZeroDerivedLowerStarIso j S.X₂).hom =
      (WeilSheaf.homologySheafZeroDerivedLowerStarIso j S.X₁).hom ≫
        (WeilSheaf.lowerStar j).map S.f :=
    WeilSheaf.homologySheafZeroDerivedLowerStarIso_hom_naturality j S.f
  have n₂ : (WeilComplex.homologySheaf 0).map T.mor₂ ≫
      (WeilSheaf.homologySheafZeroDerivedLowerStarIso j S.X₃).hom =
      (WeilSheaf.homologySheafZeroDerivedLowerStarIso j S.X₂).hom ≫
        (WeilSheaf.lowerStar j).map S.g :=
    WeilSheaf.homologySheafZeroDerivedLowerStarIso_hom_naturality j S.g
  -- the connecting morphism `δ : j_*F₂ ⟶ R¹j_*F₁` vanishes on every stalk at a closed point
  have hδ : WeilComplex.homologySheafδ T 0 _ h01 = 0 := by
    apply WeilSheaf.eq_zero_of_forall_stalkAtMap
    intro x c
    by_cases hx : x.1 ∈ Set.range j.base
    · -- Step 2: on the open, `j_*F → j_*F₂` restricts to the epimorphism `F → F₂`
      have : Epi ((WeilSheaf.upperStar j).map ((WeilComplex.homologySheaf 0).map T.mor₂)) := by
        have h := congrArg (WeilSheaf.upperStar j).map n₂
        rw [Functor.map_comp, Functor.map_comp] at h
        have := WeilSheaf.epi_upperStar_map_lowerStar_map j S.g
        have h' : Epi ((WeilSheaf.upperStar j).map ((WeilComplex.homologySheaf 0).map T.mor₂) ≫
            (WeilSheaf.upperStar j).map
              (WeilSheaf.homologySheafZeroDerivedLowerStarIso j S.X₃).hom) := by
          rw [h]
          infer_instance
        exact (epi_comp_iff_of_isIso _ _).1 h'
      obtain ⟨d, rfl⟩ := WeilSheaf.surjective_stalkAtMap_of_mem_range j
        ((WeilComplex.homologySheaf 0).map T.mor₂) x hx c
      rw [← WeilSheaf.stalkAtMap_comp, WeilComplex.homologySheaf_map_mor₂_comp_δ T 0 _ hT h01,
        WeilSheaf.stalkAtMap_zero]
    · -- Steps 4–6: at a missing point, the weight gap
      have hE := exists_linearEquiv_dual_stalk_higherDirectImage j S.X₁ h₁ x hx
      have hq : 1 < (X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 :=
        Nat.one_lt_pow ((X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2)
          Finite.one_lt_card
      -- the source `(j_*F₂)_s̄` has weights at most `w`
      have hA : (((WeilComplex.homologySheaf 0).obj T.obj₃).stalk x).HasWeightsAtMost ι
          ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w :=
        FrobeniusModule.HasWeightsAtMost.of_surjective
          (WeilSheaf.stalkAtMap _ _ _ (WeilSheaf.homologySheafZeroDerivedLowerStarIso j S.X₃).inv)
          (WeilSheaf.stalkAtMap_frobenius _ _ _ _) (WeilSheaf.surjective_stalkAtMap _ _ _ _)
          (WeilSheaf.IsLisse.hasWeightsAtMost_directImage j j.denseRange h₃ p₃.hasWeightsAtMost x)
      -- `(j_*F₁^∨)_s̄` has weights at most `-w`, `F₁^∨` being pure of weight `-w`
      have hD := WeilSheaf.IsLisse.hasWeightsAtMost_directImage (ι := ι) j j.denseRange
        h₁.dual (β := -w) (fun y ↦ by
          obtain ⟨e⟩ := WeilSheaf.nonempty_equiv_stalk_dual h₁ y
          exact (((p₁ y).dual).of_equiv e).hasWeightsAtMost) x
      have e₁ := WeilSheaf.higherDirectImage_obj_eq j S.X₁ 1
      have h0 := WeilSheaf.stalkAtMap_eq_zero_of_dual
        (WeilComplex.homologySheafδ T 0 _ h01 ≫ eqToHom e₁.symm) x hq hA hD hE
      apply WeilSheaf.injective_stalkAtMap _ _ _ (eqToHom e₁.symm)
      exact ((WeilSheaf.stalkAtMap_comp _ _ _ _ _ c).symm.trans
        ((LinearMap.congr_fun h0 c).trans (LinearMap.zero_apply c))).trans (map_zero _).symm
  -- conclusion: `0 → 𝓗⁰(Rj_*F₁) → 𝓗⁰(Rj_*F) → 𝓗⁰(Rj_*F₂) → 0` is short exact
  have hZ : IsZero ((WeilComplex.homologySheaf (-1)).obj T.obj₃) := by
    rw [WeilComplex.isZero_homologySheaf_obj_iff]
    have := (ProEtaleWeilSheaf.lowerStar k₀ l j).isGE_rightDerivedFunctor_obj_singleFunctor
      S.X₃.obj
    exact DerivedCategory.isZero_of_isGE (hX := this) _ 0 (-1) (by norm_num)
  have hS' := ShortComplex.ShortExact.mk' (WeilComplex.homologySheaf_exact₂ T 0 hT)
    ((WeilComplex.homologySheaf_exact₁ T (-1) 0 hT (by norm_num)).mono_g
      (hZ.eq_of_src _ _))
    ((WeilComplex.homologySheaf_exact₃ T 0 _ hT h01).epi_f hδ)
  exact ShortComplex.shortExact_of_iso (ShortComplex.isoMk
    (WeilSheaf.homologySheafZeroDerivedLowerStarIso j S.X₁)
    (WeilSheaf.homologySheafZeroDerivedLowerStarIso j S.X₂)
    (WeilSheaf.homologySheafZeroDerivedLowerStarIso j S.X₃) n₁.symm n₂.symm) hS'

end AlgebraicGeometry
