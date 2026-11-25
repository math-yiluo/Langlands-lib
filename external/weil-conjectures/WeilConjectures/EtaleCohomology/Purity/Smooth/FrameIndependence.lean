/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClass
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Ideal
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# Frame independence of the class of a frame

Let `f₁, …, f_c` be functions on a scheme `U` and `M` an invertible `c × c` matrix of functions.
The tuples `f` and `M f` cut out the same closed subscheme, and the cup products of Kummer
boundaries `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)` and `∂κ((Mf)₁) ∪ ⋯ ∪ ∂κ((Mf)_c)` agree
(`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_mulVec`). This is Step 3
of the proof of `lemma-class-of-point--1`.

The proof is universal: on `𝔸^c` over the general linear group `GL_{c,S}`, the coordinate frame
`t` and the frame `A t` given by the universal matrix differ by an endomorphism of `Λ` on the
zero section (the adjoint of the coordinate class being an isomorphism,
`proposition-purity-vector-bundles`), which is the identity along the identity section, hence
everywhere since `GL_{c,S} ⟶ S` has connected fibres. Pulling back along
`(M, f) : U ⟶ 𝔸^c_{GL_{c,U}}` gives the general case.

## Main definitions

- `AlgebraicGeometry.generalLinearOpen`: `GL_{c,S}` as an open of `𝔸^{c × c}_S`.

## Main statements

- `AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_glMatrix`
- `AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_mulVec`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-- Closed subschemes cut out by sets of sections spanning the same ideal agree. -/
lemma Scheme.exists_isPullback_zeroLocusSubschemeι_of_span_eq {U : Scheme.{u}}
    {s s' : Set Γ(U, ⊤)} (h : Ideal.span s = Ideal.span s') :
    ∃ g, IsPullback g (U.zeroLocusSubschemeι s') (U.zeroLocusSubschemeι s) (𝟙 U) := by
  change ∃ g, IsPullback g (IdealSheafData.ofIdealTop (Ideal.span s')).subschemeι
    (IdealSheafData.ofIdealTop (Ideal.span s)).subschemeι (𝟙 U)
  rw [h]
  exact ⟨𝟙 _, IsPullback.of_horiz_isIso ⟨by simp⟩⟩

variable (c : ℕ) (S : Scheme.{u})

/-- The matrix of coordinates of `𝔸^{c × c}_S`. -/
noncomputable def matrixCoord :
    Matrix (Fin c) (Fin c) Γ(𝔸(ULift.{u} (Fin c × Fin c); S), ⊤) :=
  fun a b ↦ AffineSpace.coord S (ULift.up (a, b))

/-- The general linear group `GL_{c,S}`: the open of `𝔸^{c × c}_S` where the determinant is
invertible.

The repository also has `AlgebraicGeometry.GeneralLinearGroup` (`𝔾𝕃(n; k)`), a group scheme over
an affine base `Spec k`. Here the base `S` is an arbitrary scheme, and only the scheme together
with its universal matrix and identity section is needed, not the group structure, so the
relative open model inside `𝔸^{c × c}_S` is used. -/
noncomputable def generalLinearOpen : 𝔸(ULift.{u} (Fin c × Fin c); S).Opens :=
  𝔸(ULift.{u} (Fin c × Fin c); S).basicOpen (matrixCoord c S).det

/-- The structure morphism `GL_{c,S} ⟶ S`. -/
noncomputable def generalLinearOpen.toBase : (generalLinearOpen c S).toScheme ⟶ S :=
  (generalLinearOpen c S).ι ≫ 𝔸(ULift.{u} (Fin c × Fin c); S) ↘ S

variable {c S}

/-- The point of `GL_{c,S}` given by an invertible matrix of functions on `T` over `f`. -/
noncomputable def generalLinearOpen.lift {T : Scheme.{u}} (f : T ⟶ S)
    (N : Matrix (Fin c) (Fin c) Γ(T, ⊤)) (hN : IsUnit N.det) :
    T ⟶ (generalLinearOpen c S).toScheme :=
  IsOpenImmersion.lift (generalLinearOpen c S).ι
    (AffineSpace.homOfVector f fun ab : ULift.{u} (Fin c × Fin c) ↦ N ab.down.1 ab.down.2) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      change x ∈ (AffineSpace.homOfVector f fun ab : ULift.{u} (Fin c × Fin c) ↦
        N ab.down.1 ab.down.2) ⁻¹ᵁ (generalLinearOpen c S)
      rw [generalLinearOpen, Scheme.preimage_basicOpen_top]
      have : (AffineSpace.homOfVector f fun ab : ULift.{u} (Fin c × Fin c) ↦
          N ab.down.1 ab.down.2).appTop (matrixCoord c S).det = N.det := by
        rw [RingHom.map_det]
        congr 1
        ext a b
        simp [matrixCoord, AffineSpace.homOfVector_appTop_coord]
      rw [this, Scheme.basicOpen_of_isUnit _ hN]
      trivial)

@[reassoc (attr := simp)]
lemma generalLinearOpen.lift_ι {T : Scheme.{u}} (f : T ⟶ S)
    (N : Matrix (Fin c) (Fin c) Γ(T, ⊤)) (hN : IsUnit N.det) :
    generalLinearOpen.lift f N hN ≫ (generalLinearOpen c S).ι =
      AffineSpace.homOfVector f fun ab : ULift.{u} (Fin c × Fin c) ↦ N ab.down.1 ab.down.2 :=
  IsOpenImmersion.lift_fac _ _ _

variable (c S)

/-- `𝔸^c` over `GL_{c,S}`. -/
noncomputable abbrev glAffine := 𝔸(ULift.{u} (Fin c); (generalLinearOpen c S).toScheme)

/-- The projection `𝔸^c_{GL_c} ⟶ GL_c`. -/
noncomputable abbrev glProj : glAffine c S ⟶ (generalLinearOpen c S).toScheme :=
  𝔸(ULift.{u} (Fin c); (generalLinearOpen c S).toScheme) ↘ (generalLinearOpen c S).toScheme

/-- The coordinates `t` of `𝔸^c_{GL_c}`. -/
noncomputable def glCoord : Fin c → Γ(glAffine c S, ⊤) :=
  fun a ↦ AffineSpace.coord _ (ULift.up a)

/-- The universal matrix on `𝔸^c_{GL_c}`. -/
noncomputable def glMatrix : Matrix (Fin c) (Fin c) Γ(glAffine c S, ⊤) :=
  ((glProj c S ≫ (generalLinearOpen c S).ι).appTop.hom.mapMatrix (matrixCoord c S))

lemma isUnit_det_glMatrix : IsUnit (glMatrix c S).det := by
  have h := (𝔸(ULift.{u} (Fin c × Fin c); S)).isUnit_ι_appTop_basicOpen (matrixCoord c S).det
  have h2 := h.map (glProj c S).appTop.hom
  rw [glMatrix, ← RingHom.map_det]
  convert h2 using 1
  simp [generalLinearOpen]

variable {c S}

/-- The identity section `S ⟶ GL_{c,S}`. -/
noncomputable def glOne : S ⟶ (generalLinearOpen c S).toScheme :=
  generalLinearOpen.lift (𝟙 S) 1 (by simp)

@[reassoc (attr := simp)]
lemma glOne_toBase : glOne (c := c) (S := S) ≫ generalLinearOpen.toBase c S = 𝟙 S := by
  rw [generalLinearOpen.toBase, glOne, generalLinearOpen.lift_ι_assoc, AffineSpace.homOfVector_over]

/-- The identity section `𝔸^c_S ⟶ 𝔸^c_{GL_{c,S}}`. -/
noncomputable def glOneAffine : 𝔸(ULift.{u} (Fin c); S) ⟶ glAffine c S :=
  AffineSpace.map _ glOne

lemma glOneAffine_appTop_glCoord (a : Fin c) :
    (glOneAffine (c := c) (S := S)).appTop (glCoord c S a) = AffineSpace.coord S (ULift.up a) :=
  AffineSpace.map_appTop_coord _ _

lemma glOneAffine_appTop_glMatrix :
    (glOneAffine (c := c) (S := S)).appTop.hom.mapMatrix (glMatrix c S) = 1 := by
  ext a b
  have h : glOneAffine ≫ glProj c S ≫ (generalLinearOpen c S).ι =
      (𝔸(ULift.{u} (Fin c); S) ↘ S) ≫ glOne ≫ (generalLinearOpen c S).ι := by
    rw [glOneAffine, ← Category.assoc, AffineSpace.map_over, Category.assoc]
  have h' := congrArg (fun φ ↦ φ.appTop (matrixCoord c S a b)) h
  simp only [glOne, generalLinearOpen.lift_ι, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    at h'
  simp only [glMatrix, RingHom.mapMatrix_apply, Matrix.map_apply, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.comp_apply]
  erw [h']
  simp only [matrixCoord, AffineSpace.homOfVector_appTop_coord, Matrix.one_apply]
  split_ifs <;> simp

lemma range_glCoord : Set.range (AffineSpace.coord (generalLinearOpen c S).toScheme) =
    Set.range (glCoord c S) := by
  ext x
  simp only [Set.mem_range, glCoord]
  exact ⟨fun ⟨a, h⟩ ↦ ⟨a.down, h⟩, fun ⟨a, h⟩ ↦ ⟨_, h⟩⟩

instance : IsSeparated (generalLinearOpen.toBase c S) := by
  unfold generalLinearOpen.toBase
  infer_instance

instance : IsClosedImmersion (glOne (c := c) (S := S)) := by
  have : IsClosedImmersion (glOne (c := c) (S := S) ≫ generalLinearOpen.toBase c S) := by
    rw [glOne_toBase]
    infer_instance
  exact IsClosedImmersion.of_comp _ (generalLinearOpen.toBase c S)

instance : IsClosedImmersion (glOneAffine (c := c) (S := S)) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin c)) glOne).flip
    inferInstance

lemma glOneAffine_appTop_mulVec :
    (fun a ↦ (glOneAffine (c := c) (S := S)).appTop ((glMatrix c S).mulVec (glCoord c S) a)) =
      fun a ↦ AffineSpace.coord S (ULift.up a) := by
  ext a
  have h := congrArg (fun M : Matrix (Fin c) (Fin c) _ ↦ (M.mulVec
    (fun b ↦ AffineSpace.coord S (ULift.up b))) a) (glOneAffine_appTop_glMatrix (c := c) (S := S))
  simp only [Matrix.one_mulVec] at h
  rw [← h, ← funext glOneAffine_appTop_glCoord]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, RingHom.mapMatrix_apply,
    Matrix.map_apply]

/-- Every point of `GL_{c,S}` lies in a preconnected set meeting the identity section: its
fibre over `S`, an open subset of an irreducible fibre of `𝔸^{c × c}_S ⟶ S`. -/
lemma exists_isPreconnected_glOne (x : (generalLinearOpen c S).toScheme) :
    ∃ T : Set (generalLinearOpen c S).toScheme, _root_.IsPreconnected T ∧ x ∈ T ∧
      (T ∩ Set.range (glOne (c := c) (S := S)).base).Nonempty := by
  let π := 𝔸(ULift.{u} (Fin c × Fin c); S) ↘ S
  let s := generalLinearOpen.toBase c S x
  refine ⟨(generalLinearOpen c S).ι.base ⁻¹' (π.base ⁻¹' {s}),
    ((π.isIrreducible_preimage (AffineSpace.isOpenMap_over (n := ULift.{u} (Fin c × Fin c)) S)
      isIrreducible_singleton).isPreirreducible.preimage
        (generalLinearOpen c S).ι.isOpenEmbedding).isPreconnected, rfl, glOne s, ?_, s, rfl⟩
  change (glOne ≫ generalLinearOpen.toBase c S).base s = s
  rw [glOne_toBase]
  rfl

namespace Etale

/-- The exponent of `Λ` stays invertible on `GL_{c,S}`. -/
instance hasInvertibleExponent_generalLinearOpen {Λ : Type (u + 1)} [CommRing Λ]
    [HasInvertibleExponent Λ S] : HasInvertibleExponent Λ (generalLinearOpen c S).toScheme :=
  .of_hom (generalLinearOpen.toBase c S)

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]

variable [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ S]

/-- **Universal frame independence.** On `𝔸^c_{GL_{c,S}}`, with coordinates `t` and universal
matrix `A`, the frames `t` and `A t` of the zero section have the same class: restricting
`∂κ(At₁) ∪ ⋯` to the support `V(t)` gives `∂κ(t₁) ∪ ⋯`. Both adjoints differ by an endomorphism
`h` of `Λ` on `V(t) ≅ GL_{c,S}`, the adjoint of the latter being an isomorphism
(`proposition-purity-vector-bundles`); along the identity section both classes become the coordinate
class of `𝔸^c_S`, so `h` is the identity along the identity section, hence everywhere, the fibres of
`GL_{c,S} ⟶ S` being connected. -/
theorem restrictSupportedClass_kummerBoundaryProduct_glMatrix
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
    isIso_supportedClassMap_kummerBoundaryProduct_coord Λ c _
  have haS := isIso_supportedClassMap_kummerBoundaryProduct_coord Λ c S
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

omit [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ S] in
/-- The point `(M, f)` of `𝔸^c_{GL_c}` defined by an invertible matrix and a vector of functions. -/
lemma exists_glAffine_point {U : Scheme.{u}} (f : Fin c → Γ(U, ⊤))
    (M : Matrix (Fin c) (Fin c) Γ(U, ⊤)) (hM : IsUnit M.det) :
    ∃ Φ : U ⟶ glAffine c U, (∀ a, Φ.appTop (glCoord c U a) = f a) ∧
      ∀ a, Φ.appTop ((glMatrix c U).mulVec (glCoord c U) a) = M.mulVec f a := by
  let Φ := AffineSpace.homOfVector (generalLinearOpen.lift (𝟙 U) M hM)
    fun a : ULift.{u} (Fin c) ↦ f a.down
  have h₁ : ∀ a, Φ.appTop (glCoord c U a) = f a := fun a ↦
    AffineSpace.homOfVector_appTop_coord _ _ _
  refine ⟨Φ, h₁, fun a ↦ ?_⟩
  have hM' : ∀ a b, Φ.appTop (glMatrix c U a b) = M a b := by
    intro a b
    have h : Φ ≫ glProj c U ≫ (generalLinearOpen c U).ι =
        AffineSpace.homOfVector (𝟙 U)
          (fun ab : ULift.{u} (Fin c × Fin c) ↦ M ab.down.1 ab.down.2) := by
      rw [← Category.assoc, AffineSpace.homOfVector_over, generalLinearOpen.lift_ι]
    have h' := congrArg (fun φ ↦ φ.appTop (matrixCoord c U a b)) h
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h'
    simp only [glMatrix, RingHom.mapMatrix_apply, Matrix.map_apply, Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp]
    erw [h']
    simp [matrixCoord, AffineSpace.homOfVector_appTop_coord]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hM', h₁]

/-- **Frame independence.** For functions `f₁, …, f_c` on `U` and an invertible matrix `M`, the
frames `f` and `M f` cut out the same closed subscheme and have the same class: restricting
`∂κ((Mf)₁) ∪ ⋯ ∪ ∂κ((Mf)_c)` to the support `V(f)` gives `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)`. This is the
pullback of the universal case along `(M, f) : U ⟶ 𝔸^c_{GL_c}`. -/
theorem restrictSupportedClass_kummerBoundaryProduct_mulVec {U : Scheme.{u}}
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
  rw [restrictSupportedClass_kummerBoundaryProduct_glMatrix Λ gE hgE,
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
