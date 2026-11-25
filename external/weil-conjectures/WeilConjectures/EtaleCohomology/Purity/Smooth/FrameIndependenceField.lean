/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependence
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClassField

/-!
# Frame independence of the class of a frame over a field

Over a base separated and locally of finite type over a field, the Thom class of the zero
section of affine space is known
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_coord_of_field`). This
file reruns the proof of frame independence of
`WeilConjectures/EtaleCohomology/Purity/Smooth/FrameIndependence.lean` (Step 3 of the proof of
`lemma-class-of-point--1`) with this input: for functions `f₁, …, f_c` on `U` and an invertible
matrix `M`, the cup products of Kummer boundaries of `f` and of `M f` agree.

## Main statements

- `AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_glMatrix_of_field`
- `AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_mulVec_of_field`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-- `GL_{c,S} ⟶ S` is locally of finite type: it is an open of `𝔸^{c × c}_S`. -/
instance locallyOfFiniteType_generalLinearOpen_toBase (c : ℕ) (S : Scheme.{u}) :
    LocallyOfFiniteType (generalLinearOpen.toBase c S) := by
  unfold generalLinearOpen.toBase
  infer_instance

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {c : ℕ}

/-- **Universal frame independence over a field** (Step 3 of the proof of
`lemma-class-of-point--1`). For `S` separated and locally of finite type over a field, on
`𝔸^c_{GL_{c,S}}`, with coordinates `t` and universal matrix `A`, the frames `t` and `A t` of the
zero section have the same class: restricting `∂κ(At₁) ∪ ⋯` to the support `V(t)` gives
`∂κ(t₁) ∪ ⋯`. Same proof as
`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_glMatrix`, using the Thom
class isomorphism over a field
`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_coord_of_field`. -/
theorem restrictSupportedClass_kummerBoundaryProduct_glMatrix_of_field {k : Type u} [Field k]
    {S : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [IsSeparated aS] [LocallyOfFiniteType aS]
    [HasInvertibleExponent Λ S]
    (g : (glAffine c S).zeroLocusSubscheme (Set.range (glCoord c S)) ⟶
      (glAffine c S).zeroLocusSubscheme (Set.range ((glMatrix c S).mulVec (glCoord c S))))
    (hg : IsPullback g ((glAffine c S).zeroLocusSubschemeι (Set.range (glCoord c S)))
      ((glAffine c S).zeroLocusSubschemeι (Set.range ((glMatrix c S).mulVec (glCoord c S))))
      (𝟙 _)) :
    restrictSupportedClass Λ (𝟙 _) _ _ g hg
        (leftDerivedUpperStarConstantComplexIso Λ (𝟙 _)).inv
        (leftDerivedUpperStarTateShiftIso Λ (𝟙 _) c)
        (kummerBoundaryProduct Λ ((glMatrix c S).mulVec (glCoord c S))) =
      kummerBoundaryProduct Λ (glCoord c S) := by
  set ι := (glAffine c S).zeroLocusSubschemeι (Set.range (glCoord c S))
  set ιS := 𝔸(ULift.{u} (Fin c); S).zeroLocusSubschemeι
    (Set.range fun a : Fin c ↦ AffineSpace.coord S (ULift.up a))
  have ha : IsIso (supportedClassMap Λ ι (kummerBoundaryProduct Λ (glCoord c S))) :=
    isIso_supportedClassMap_kummerBoundaryProduct_coord_of_field Λ c _
      (generalLinearOpen.toBase c S ≫ aS)
  have haS := isIso_supportedClassMap_kummerBoundaryProduct_coord_of_field Λ c S aS
  set y := restrictSupportedClass Λ (𝟙 _) _ _ g hg
    (leftDerivedUpperStarConstantComplexIso Λ (𝟙 _)).inv
    (leftDerivedUpperStarTateShiftIso Λ (𝟙 _) c)
    (kummerBoundaryProduct Λ ((glMatrix c S).mulVec (glCoord c S)))
  set a := supportedClassMap Λ ι (kummerBoundaryProduct Λ (glCoord c S))
  set b := supportedClassMap Λ ι y
  suffices hb : b = a from (supportedClassMap_bijective Λ ι _).1 hb
  obtain ⟨h', hh'⟩ := exists_constantComplexEndPullback_zeroLocusSubschemeι_eq Λ _ _
    range_glCoord (b ≫ inv a)
  -- the pullback squares along the identity section
  obtain ⟨gε, hgε⟩ : ∃ g, IsPullback g _ _ _ :=
    ⟨_, isPullback_zeroLocusSubschemeι glOneAffine
      (Set.range (glCoord c S)) (Set.range fun a : Fin c ↦ AffineSpace.coord S (ULift.up a)) (by
        rw [← Set.range_comp]
        exact congrArg Set.range (funext glOneAffine_appTop_glCoord))⟩
  obtain ⟨g', hg'⟩ : ∃ g, IsPullback g _ _ _ :=
    ⟨_, isPullback_zeroLocusSubschemeι glOneAffine
      (Set.range ((glMatrix c S).mulVec (glCoord c S)))
      (Set.range fun a : Fin c ↦ AffineSpace.coord S (ULift.up a)) (by
        rw [← Set.range_comp]
        exact congrArg Set.range glOneAffine_appTop_mulVec)⟩
  -- restricting both adjoints along the identity section gives the coordinate class of `𝔸^c_S`
  have hra : restrictSupportedHom Λ glOneAffine ι ιS gε hgε
      (leftDerivedUpperStarTateShiftIso Λ glOneAffine c) a =
        supportedClassMap Λ ιS
          (kummerBoundaryProduct Λ fun a : Fin c ↦ AffineSpace.coord S (ULift.up a)) := by
    rw [restrictSupportedHom, show (supportedClassMapEquiv Λ ι _).symm a = _ from
      (supportedClassMapEquiv Λ ι _).symm_apply_apply _,
      restrictSupportedClass_kummerBoundaryProduct Λ glOneAffine _ _
        glOneAffine_appTop_glCoord gε hgε]
  have hrb : restrictSupportedHom Λ glOneAffine ι ιS gε hgε
      (leftDerivedUpperStarTateShiftIso Λ glOneAffine c) b =
        supportedClassMap Λ ιS
          (kummerBoundaryProduct Λ fun a : Fin c ↦ AffineSpace.coord S (ULift.up a)) := by
    rw [restrictSupportedHom, show (supportedClassMapEquiv Λ ι _).symm b = y from
      (supportedClassMapEquiv Λ ι _).symm_apply_apply _]
    congr 1
    have := restrictSupportedClass_restrictSupportedClass Λ (𝟙 _)
      glOneAffine glOneAffine (by simp) _ ι ιS g hg gε hgε g' hg'
      (leftDerivedUpperStarConstantComplexIso Λ (𝟙 _)).inv
      (leftDerivedUpperStarConstantComplexIso Λ glOneAffine).inv
      (leftDerivedUpperStarTateShiftIso Λ (𝟙 _) c)
      (leftDerivedUpperStarTateShiftIso Λ glOneAffine c)
      (kummerBoundaryProduct Λ ((glMatrix c S).mulVec (glCoord c S)))
    rw [← this]
    have hσ : (leftDerivedUpperStarConstantComplexIso Λ glOneAffine).inv ≫
        (L((glOneAffine (c := c) (S := S))^*[ModuleCat.{u + 1} Λ])).map
          (leftDerivedUpperStarConstantComplexIso Λ (𝟙 _)).inv ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) glOneAffine (𝟙 _) glOneAffine
          (by simp)).inv.app _ = (leftDerivedUpperStarConstantComplexIso Λ glOneAffine).inv := by
      conv_rhs => rw [leftDerivedUpperStarConstantComplexIso_comp Λ glOneAffine (𝟙 _) glOneAffine
        (by simp)]
      simp
    have hτ := (leftDerivedUpperStarTateShiftIso_comp Λ (glOneAffine (c := c) (S := S)) (𝟙 _)
      glOneAffine (by simp)
      (c : ℤ)).symm
    rw [hσ, hτ]
    exact restrictSupportedClass_kummerBoundaryProduct Λ glOneAffine _ _
      (congrFun glOneAffine_appTop_mulVec) g' hg'
  have hb : b = constantComplexEndPullback Λ ι h' ≫ a := by
    rw [hh', Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hgι : gε ≫ ι = ιS ≫ glOneAffine := hgε.w
  have key : constantComplexEndPullback Λ gε (b ≫ inv a) = 𝟙 _ := by
    have := hrb
    rw [hb, restrictSupportedHom_constantComplexEndPullback_comp, hra] at this
    have h2 : constantComplexEndPullback Λ ιS (constantComplexEndPullback Λ glOneAffine h') =
        𝟙 _ := by
      rw [← cancel_mono (supportedClassMap Λ ιS
        (kummerBoundaryProduct Λ fun a : Fin c ↦ AffineSpace.coord S (ULift.up a))), this,
        Category.id_comp]
    rw [← hh', constantComplexEndPullback_constantComplexEndPullback gε ι _ hgι.symm,
      ← constantComplexEndPullback_constantComplexEndPullback ιS glOneAffine _ rfl, h2]
  -- `L gε^* (b ≫ inv a) = 𝟙`
  have key' : (L((gε)^*[ModuleCat.{u + 1} Λ])).map (b ≫ inv a) = 𝟙 _ := by
    have := key
    simp only [constantComplexEndPullback] at this
    calc (L((gε)^*[ModuleCat.{u + 1} Λ])).map (b ≫ inv a)
        = (leftDerivedUpperStarConstantComplexIso Λ gε).hom ≫
            ((leftDerivedUpperStarConstantComplexIso Λ gε).inv ≫
              (L((gε)^*[ModuleCat.{u + 1} Λ])).map (b ≫ inv a) ≫
                (leftDerivedUpperStarConstantComplexIso Λ gε).hom) ≫
            (leftDerivedUpperStarConstantComplexIso Λ gε).inv := by simp
      _ = 𝟙 _ := by rw [this]; simp
  have : IsClosedImmersion gε :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hgε.flip inferInstance
  have hinv : DerivedCategory.isInvertible Λ _ (constantComplex Λ
      ((glAffine c S).zeroLocusSubscheme (Set.range (glCoord c S)))) :=
    ⟨_, ⟨derivedTensorLeftUnitor _ _ _⟩, ⟨derivedTensorLeftUnitor _ _ _⟩⟩
  -- every point lies in a preconnected set meeting the identity section
  have hi : ∀ x, ∃ T : Set ((glAffine c S).zeroLocusSubscheme (Set.range (glCoord c S))),
      _root_.IsPreconnected T ∧ x ∈ T ∧ (T ∩ Set.range gε.base).Nonempty := by
    intro x
    let ζ := AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin c))
      (generalLinearOpen c S).toScheme range_glCoord
    let ζS := AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin c)) S
      (s := Set.range fun a : Fin c ↦ AffineSpace.coord S (ULift.up a)) (by
        ext x; simp only [Set.mem_range]
        exact ⟨fun ⟨a, h⟩ ↦ ⟨a.down, h⟩, fun ⟨a, h⟩ ↦ ⟨_, h⟩⟩)
    obtain ⟨T, hT, hyT, _, hsT, s', rfl⟩ := exists_isPreconnected_glOne (ζ.inv.base x)
    have heq : ζS.hom ≫ gε ≫ ι = glOne ≫ ζ.hom ≫ ι := by
      rw [hgι, AffineSpace.zeroSectionIsoZeroLocusSubscheme_hom_zeroLocusSubschemeι,
        ← Category.assoc, AffineSpace.zeroSectionIsoZeroLocusSubscheme_hom_zeroLocusSubschemeι,
        glOneAffine, AffineSpace.zeroSection_comp_map]
    refine ⟨ζ.hom.base '' T, hT.image _ ζ.hom.base.hom.continuous.continuousOn,
      ⟨_, hyT, by rw [← Scheme.Hom.comp_apply, ζ.inv_hom_id]; rfl⟩, ζ.hom.base (glOne.base s'),
      ⟨_, hsT, rfl⟩, ζS.hom.base s', ι.isClosedEmbedding.injective ?_⟩
    have := congrArg (fun φ : S ⟶ (glAffine c S) ↦ φ.base s') heq
    simpa only [Scheme.Hom.comp_apply] using this
  have hid := eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible gε hi hinv _ key'
  calc b = (b ≫ inv a) ≫ a := by simp
    _ = a := by rw [hid, Category.id_comp]

/-- **Frame independence over a field** (Step 3 of the proof of `lemma-class-of-point--1`). For `U`
separated and locally of finite type over a field, functions `f₁, …, f_c` on `U` and an invertible
matrix `M`, the frames `f` and `M f` cut out the same closed subscheme and have the same class:
restricting `∂κ((Mf)₁) ∪ ⋯ ∪ ∂κ((Mf)_c)` to the support `V(f)` gives `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)`.
This is the pullback of the universal case
`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_glMatrix_of_field` along
`(M, f) : U ⟶ 𝔸^c_{GL_c}`. -/
theorem restrictSupportedClass_kummerBoundaryProduct_mulVec_of_field {k : Type u} [Field k]
    {U : Scheme.{u}} (aU : U ⟶ Spec (.of k)) [IsSeparated aU] [LocallyOfFiniteType aU]
    [HasInvertibleExponent Λ U] (f : Fin c → Γ(U, ⊤)) (M : Matrix (Fin c) (Fin c) Γ(U, ⊤))
    (hM : IsUnit M.det)
    (g : U.zeroLocusSubscheme (Set.range f) ⟶ U.zeroLocusSubscheme (Set.range (M.mulVec f)))
    (hg : IsPullback g (U.zeroLocusSubschemeι (Set.range f))
      (U.zeroLocusSubschemeι (Set.range (M.mulVec f))) (𝟙 _)) :
    restrictSupportedClass Λ (𝟙 _) _ _ g hg
        (leftDerivedUpperStarConstantComplexIso Λ (𝟙 _)).inv
        (leftDerivedUpperStarTateShiftIso Λ (𝟙 _) c) (kummerBoundaryProduct Λ (M.mulVec f)) =
      kummerBoundaryProduct Λ f := by
  obtain ⟨Φ, hΦt, hΦA⟩ := exists_glAffine_point f M hM
  obtain ⟨g₁, hg₁⟩ : ∃ g, IsPullback g _ _ _ :=
    ⟨_, isPullback_zeroLocusSubschemeι Φ
      (Set.range ((glMatrix c U).mulVec (glCoord c U))) (Set.range (M.mulVec f)) (by
        rw [← Set.range_comp]; exact congrArg Set.range (funext hΦA))⟩
  obtain ⟨g₂, hg₂⟩ : ∃ g, IsPullback g _ _ _ :=
    ⟨_, isPullback_zeroLocusSubschemeι Φ
      (Set.range (glCoord c U)) (Set.range f) (by
        rw [← Set.range_comp]; exact congrArg Set.range (funext hΦt))⟩
  obtain ⟨gE, hgE⟩ := Scheme.exists_isPullback_zeroLocusSubschemeι_of_span_eq
    (Ideal.span_range_mulVec_of_isUnit_det _ (isUnit_det_glMatrix c U) (glCoord c U))
  have hcomp₁ : Φ = 𝟙 U ≫ Φ := by simp
  have hcomp₂ : Φ = Φ ≫ 𝟙 _ := by simp
  have e₁ := restrictSupportedClass_restrictSupportedClass Λ Φ (𝟙 U) Φ
    hcomp₁ _ _ _ g₁ hg₁ g hg (g ≫ g₁) ((Category.id_comp Φ) ▸ hg.paste_horiz hg₁)
    (leftDerivedUpperStarConstantComplexIso Λ Φ).inv
    (leftDerivedUpperStarConstantComplexIso Λ (𝟙 U)).inv
    (leftDerivedUpperStarTateShiftIso Λ Φ c) (leftDerivedUpperStarTateShiftIso Λ (𝟙 U) c)
    (kummerBoundaryProduct Λ ((glMatrix c U).mulVec (glCoord c U)))
  rw [restrictSupportedClass_kummerBoundaryProduct Λ Φ _ _ hΦA g₁ hg₁] at e₁
  have e₂ := restrictSupportedClass_restrictSupportedClass Λ (𝟙 _) Φ Φ
    hcomp₂ _ _ _ gE hgE g₂ hg₂ (g₂ ≫ gE) ((Category.comp_id Φ) ▸ hg₂.paste_horiz hgE)
    (leftDerivedUpperStarConstantComplexIso Λ (𝟙 _)).inv
    (leftDerivedUpperStarConstantComplexIso Λ Φ).inv
    (leftDerivedUpperStarTateShiftIso Λ (𝟙 _) c) (leftDerivedUpperStarTateShiftIso Λ Φ c)
    (kummerBoundaryProduct Λ ((glMatrix c U).mulVec (glCoord c U)))
  rw [restrictSupportedClass_kummerBoundaryProduct_glMatrix_of_field Λ aU gE hgE,
    restrictSupportedClass_kummerBoundaryProduct Λ Φ _ _ hΦt g₂ hg₂] at e₂
  have hσ₁ : (leftDerivedUpperStarConstantComplexIso Λ (𝟙 U)).inv ≫
      (L((𝟙 U)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ Φ).inv ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (𝟙 U) Φ Φ hcomp₁).inv.app _ =
        (leftDerivedUpperStarConstantComplexIso Λ Φ).inv := by
    conv_rhs => rw [leftDerivedUpperStarConstantComplexIso_comp Λ (𝟙 U) Φ Φ hcomp₁]
    simp
  have hσ₂ : (leftDerivedUpperStarConstantComplexIso Λ Φ).inv ≫
      (L((Φ)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ (𝟙 _)).inv ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) Φ (𝟙 _) Φ hcomp₂).inv.app _ =
        (leftDerivedUpperStarConstantComplexIso Λ Φ).inv := by
    conv_rhs => rw [leftDerivedUpperStarConstantComplexIso_comp Λ Φ (𝟙 _) Φ hcomp₂]
    simp
  rw [hσ₁, ← leftDerivedUpperStarTateShiftIso_comp Λ (𝟙 U) Φ Φ hcomp₁] at e₁
  rw [hσ₂, ← leftDerivedUpperStarTateShiftIso_comp Λ Φ (𝟙 _) Φ hcomp₂] at e₂
  rw [← e₁]
  exact e₂

end Etale

end AlgebraicGeometry
