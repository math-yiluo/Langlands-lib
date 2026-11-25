/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdIntegralScalarLiftProperty
import Mathlib.CategoryTheory.Triangulated.Adjunction
import all WeilConjectures.FourierTransform.FdIntegralOrdinaryScalarModel.FdIntegralOrdinaryScalarModel
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import all WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.IntrinsicAssociatorShiftSquare
import all WeilConjectures.FourierTransform.FdIntegralStageExact

/-! # Shifts and exactness of the integral scalar comparison

Source: trace-definition coefficient-category comparison, integral steps 1--6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.FdRawLocalization
namespace WeilConjectures
open FdIntegralOrdinaryScalarModel
attribute [local instance] restrictionShift detailedShift

-- Ring-presentation comparisons use the common completed sheaf, not its limit cone.
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

private theorem commShift_of_sandwich
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    {F₀ F₁ F₂ F₃ : A ⥤ B}
    [F₀.CommShift ℤ] [F₁.CommShift ℤ] [F₂.CommShift ℤ] [F₃.CommShift ℤ]
    (a : F₀ ≅ F₁) (b : F₁ ≅ F₂) (c : F₂ ≅ F₃)
    [NatTrans.CommShift a.hom ℤ] [NatTrans.CommShift c.hom ℤ]
    [NatTrans.CommShift (a ≪≫ b ≪≫ c).hom ℤ] : NatTrans.CommShift b.hom ℤ := by
  have hb : b.hom = (a.symm ≪≫ (a ≪≫ b ≪≫ c) ≪≫ c.symm).hom := by
    ext K
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
      Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [hb]
  change NatTrans.CommShift (a.inv ≫ (a ≪≫ b ≪≫ c).hom ≫ c.inv) ℤ
  have : NatTrans.CommShift ((a ≪≫ b ≪≫ c).hom ≫ c.inv) ℤ :=
    NatTrans.CommShift.comp _ _ ℤ
  exact NatTrans.CommShift.comp _ _ ℤ

private theorem scalarExact
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    (C l Ω T h).IsTriangulated := by
  have := (pbcDerivedScalarAdjunction
    (pbcCompletedScalarMap l Ω T h)).commShift_of_rightAdjoint ℤ
  have : (pbcDerivedRestrict (pbcCompletedScalarMap l Ω T h)).IsTriangulated :=
    inferInstanceAs
      (((pbcRestrict (pbcCompletedScalarMap l Ω T h)).mapDerivedCategory).IsTriangulated)
  have : (pbcAmbientScalarExtension l Ω T h).IsTriangulated :=
    (pbcDerivedScalarAdjunction
      (pbcCompletedScalarMap l Ω T h)).isTriangulated_leftAdjoint
  have hc := Functor.CommShift.ofComp_compatibility
    (F := C l Ω T h) (G := pbcStageInclusion l Ω T L)
    (Iso.refl (pbcStageInclusion l Ω T E ⋙ pbcAmbientScalarExtension l Ω T h)) ℤ
  exact (Functor.isTriangulated_iff_comp_right
    (F := C l Ω T h) (G := pbcStageInclusion l Ω T L)
    (Iso.refl (pbcStageInclusion l Ω T E ⋙ pbcAmbientScalarExtension l Ω T h))).mpr
      inferInstance

attribute [local irreducible] integralScalarExtension integralOrdinaryScalar
  sfIntegralOrdinaryComparison

private theorem scalarShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (ordinary : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      FdOrdinaryScalarTransport l Ω T h)
    (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
    (hlift : fdIntegralScalarLiftProperty l Ω T stage ordinary b)
    {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    NatTrans.CommShift (b h).hom ℤ := by
  let E' := pbcFiniteField.{u} l Ω E
  let L' := pbcFiniteField.{u} l Ω L
  let i := pbcFiniteFieldInclusion l Ω h
  let jE := (sfIntegralConstructible l E' T).ι
  let jL := (sfIntegralConstructible l L' T).ι
  let dE := integralDetailedTransport T l E'
  let dL := integralDetailedTransport T l L'
  let H := integralOrdinaryDerivedScalar l E' L' i T
  obtain ⟨e, he, hn⟩ := ordinaryTransportModel l Ω T h (ordinary h)
  let aE : I l Ω T stage E ⋙ pbcStageInclusion l Ω T E ≅ jE ⋙ dE :=
    eqToIso (stage E).integral_identity
  let aL : I l Ω T stage L ⋙ pbcStageInclusion l Ω T L ≅ jL ⋙ dL :=
    eqToIso (stage L).integral_identity
  have haE : NatTrans.CommShift aE.hom ℤ := by
    apply commShift_eqToIso _ _ (stage E).integral_identity
    intro n K
    simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
      ObjectProperty.ι_obj]
    dsimp only [detailedShift, integralDetailedTransport, fdCoefficientTransport]
    exact (stage E).integral_shift_normalization n K
  have haL : NatTrans.CommShift aL.hom ℤ := by
    apply commShift_eqToIso _ _ (stage L).integral_identity
    intro n K
    simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
      ObjectProperty.ι_obj]
    dsimp only [detailedShift, integralDetailedTransport, fdCoefficientTransport]
    exact (stage L).integral_shift_normalization n K
  let r : C l Ω T h ⋙ pbcStageInclusion l Ω T L ≅
      pbcStageInclusion l Ω T E ⋙ pbcAmbientScalarExtension l Ω T h := Iso.refl _
  have hr : NatTrans.CommShift r.hom ℤ :=
    Functor.CommShift.ofComp_compatibility r ℤ
  let pre : (jE ⋙ H) ⋙ dL ≅
      (I l Ω T stage E ⋙ C l Ω T h) ⋙ pbcStageInclusion l Ω T L :=
    Functor.associator jE H dL ≪≫ Functor.isoWhiskerLeft jE e ≪≫
      (Functor.associator jE dE (pbcAmbientScalarExtension l Ω T h)).symm ≪≫
      Functor.isoWhiskerRight aE.symm (pbcAmbientScalarExtension l Ω T h) ≪≫
      Functor.associator (I l Ω T stage E) (pbcStageInclusion l Ω T E)
        (pbcAmbientScalarExtension l Ω T h) ≪≫
      Functor.isoWhiskerLeft (I l Ω T stage E) r.symm ≪≫
      (Functor.associator (I l Ω T stage E) (C l Ω T h)
        (pbcStageInclusion l Ω T L)).symm
  have hpre : NatTrans.CommShift pre.hom ℤ := by
    dsimp only [pre, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom]
    have : NatTrans.CommShift aE.inv ℤ := NatTrans.CommShift.of_iso_inv aE ℤ
    have : NatTrans.CommShift r.inv ℤ := NatTrans.CommShift.of_iso_inv r ℤ
    have h6 : NatTrans.CommShift ((I l Ω T stage E).whiskerLeft r.inv ≫
        ((I l Ω T stage E).associator (C l Ω T h) (pbcStageInclusion l Ω T L)).inv) ℤ :=
      NatTrans.CommShift.comp _ _ ℤ
    have h5 : NatTrans.CommShift (((I l Ω T stage E).associator (pbcStageInclusion l Ω T E)
        (pbcAmbientScalarExtension l Ω T h)).hom ≫
        (I l Ω T stage E).whiskerLeft r.inv ≫
        ((I l Ω T stage E).associator (C l Ω T h) (pbcStageInclusion l Ω T L)).inv) ℤ :=
      NatTrans.CommShift.comp _ _ ℤ
    have h4 : NatTrans.CommShift
        (Functor.whiskerRight aE.inv (pbcAmbientScalarExtension l Ω T h) ≫
        ((I l Ω T stage E).associator (pbcStageInclusion l Ω T E)
        (pbcAmbientScalarExtension l Ω T h)).hom ≫
        (I l Ω T stage E).whiskerLeft r.inv ≫
        ((I l Ω T stage E).associator (C l Ω T h) (pbcStageInclusion l Ω T L)).inv) ℤ :=
      NatTrans.CommShift.comp _ _ ℤ
    have h3 : NatTrans.CommShift ((jE.associator dE (pbcAmbientScalarExtension l Ω T h)).inv ≫
        Functor.whiskerRight aE.inv (pbcAmbientScalarExtension l Ω T h) ≫
        ((I l Ω T stage E).associator (pbcStageInclusion l Ω T E)
        (pbcAmbientScalarExtension l Ω T h)).hom ≫
        (I l Ω T stage E).whiskerLeft r.inv ≫
        ((I l Ω T stage E).associator (C l Ω T h) (pbcStageInclusion l Ω T L)).inv) ℤ :=
      NatTrans.CommShift.comp _ _ ℤ
    have h2 : NatTrans.CommShift (jE.whiskerLeft e.hom ≫
        (jE.associator dE (pbcAmbientScalarExtension l Ω T h)).inv ≫
        Functor.whiskerRight aE.inv (pbcAmbientScalarExtension l Ω T h) ≫
        ((I l Ω T stage E).associator (pbcStageInclusion l Ω T E)
        (pbcAmbientScalarExtension l Ω T h)).hom ≫
        (I l Ω T stage E).whiskerLeft r.inv ≫
        ((I l Ω T stage E).associator (C l Ω T h) (pbcStageInclusion l Ω T L)).inv) ℤ :=
      NatTrans.CommShift.comp _ _ ℤ
    exact NatTrans.CommShift.comp _ _ ℤ
  let post : (U l Ω T h ⋙ I l Ω T stage L) ⋙ pbcStageInclusion l Ω T L ≅
      (U l Ω T h ⋙ jL) ⋙ dL :=
    Functor.associator (U l Ω T h) (I l Ω T stage L) (pbcStageInclusion l Ω T L) ≪≫
      Functor.isoWhiskerLeft (U l Ω T h) aL ≪≫
      (Functor.associator (U l Ω T h) jL dL).symm
  have hpost : NatTrans.CommShift post.hom ℤ := by
    dsimp only [post, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom]
    have : NatTrans.CommShift ((U l Ω T h).whiskerLeft aL.hom ≫
        ((U l Ω T h).associator jL dL).inv) ℤ :=
      NatTrans.CommShift.comp _ _ ℤ
    exact NatTrans.CommShift.comp _ _ ℤ
  let y : (jE ⋙ H) ⋙ dL ≅ (U l Ω T h ⋙ jL) ⋙ dL :=
    pre ≪≫ Functor.isoWhiskerRight (b h) (pbcStageInclusion l Ω T L) ≪≫ post
  let W := (Functor.whiskeringRight (sfIntegralConstructibleCategory l E' T)
    (DerivedCategory (integralTowerModules l L' T))
    (pbcAmbientStage l Ω T L)).obj dL
  let c : jE ⋙ H ≅ U l Ω T h ⋙ jL := W.preimageIso y
  have hc : Functor.isoWhiskerRight c dL = y := by
    apply Iso.ext
    exact W.map_preimage _
  have hc' : c = sfIntegralOrdinaryComparison l E' L' i T := by
    apply (sfIntegralOrdinaryComparison_existsUnique l E' L' i T).unique
    · intro P hP
      let K : sfIntegralConstructibleCategory l E' T := ⟨DerivedCategory.Q.obj P.obj, hP⟩
      let t := (integralScalarExtensionComparison l E' L' i T).hom.app P
      let f := (fdCoefficientTransportFactors l L' T).hom.app
        ((integralScalarComplexFunctor l E' L' i T).obj P.obj)
      have hf : IsIso f := (fdCoefficientTransportFactors l L' T).app
        ((integralScalarComplexFunctor l E' L' i T).obj P.obj) |>.isIso_hom
      apply dL.map_injective
      apply (cancel_mono f).mp
      have hcy := congrArg (fun z ↦ z.hom.app K) hc
      dsimp only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] at hcy
      erw [Functor.map_comp, hcy]
      dsimp only [y, pre, post, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
        Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom]
      dsimp only [r, Iso.refl_hom, NatTrans.id_app, Iso.refl_inv,
        Functor.associator_hom_app, Functor.associator_inv_app]
      -- Normalize the composite before the rewrites that unfold coefficient-category definitions.
      simp only [Category.id_comp, Category.comp_id, Category.assoc]
      repeat erw [Category.id_comp]
      repeat erw [Category.assoc]
      have hl := hlift h P hP
      let z := ((b h).hom.app K).hom ≫ aL.hom.app ((U l Ω T h).obj K) ≫
        dL.map t ≫ f
      have hz : HEq
          ((pbcAmbientScalarExtension l Ω T h).map (aE.inv.app K) ≫ z) z := by
        dsimp only [aE, eqToIso, Iso.symm_inv]
        erw [eqToHom_app, eqToHom_map]
        exact eqToHom_comp_heq _ _
      have hlz : HEq z
          ((pbcAmbientScalarExtension l Ω T h).map
            ((fdCoefficientTransportFactors l E' T).hom.app P.obj) ≫
            pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
              (((fdCoefficientTransport l E' T).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
            DerivedCategory.Q.map ((ordinary h).completion l Ω P.obj)) := by
        dsimp only [z, aL, eqToIso]
        erw [eqToHom_app]
        exact hl
      have hl' := eq_of_heq (hz.trans hlz)
      exact (congrArg (fun v ↦ e.hom.app (DerivedCategory.Q.obj P.obj) ≫ v) hl').trans
        (hn P.obj)
    · delta sfIntegralOrdinaryComparison
      exact (sfIntegralOrdinaryComparison_existsUnique l E' L' i T).exists.choose_spec
  have hcs : NatTrans.CommShift c.hom ℤ := by
    rw [hc']
    exact GeneralAlgebraicallyClosedCoefficients.integral_comparison_commShift l E' L' i T
  have hy : NatTrans.CommShift y.hom ℤ := by
    rw [← hc]
    dsimp only [Functor.isoWhiskerRight_hom]
    infer_instance
  have : NatTrans.CommShift
      (Functor.whiskerRight (b h).hom (pbcStageInclusion l Ω T L)) ℤ :=
    commShift_of_sandwich pre
      (Functor.isoWhiskerRight (b h) (pbcStageInclusion l Ω T L)) post
  exact NatTrans.CommShift.of_whiskerRight _ (pbcStageInclusion l Ω T L)

/-- A comparison fixed on good representatives by the actual completion map preserves
its prescribed shifts; its two endpoint composites are exact.
Source: trace-definition coefficient comparison, integral step 1
(blueprint: lem-fd-integral-scalar-restriction-exact).

Proof: The proved ordinary model (lem-fd-integral-ordinary-scalar-model) gives the
exact derived coefficient square, with the prescribed ambient shift, and its equation
on every cochain representative after the actual ordinary.completion. Conjugate b by
the two stage integral_identity isomorphisms and this square; lift the result through
the fully faithful coefficient transport to a comparison c of the intrinsic ordinary
and completed extensions. On each good representative, faithfulness, cancellation of
the invertible localization factor and the supplied lift equation give the defining
equation of sfIntegralOrdinaryComparison; its uniqueness identifies c with it. That
comparison commutes with all integer shifts; the stage integral_shift_normalization
and the explicit associators make every other factor shift-compatible, so b commutes
with shifts after the target inclusion, and faithfulness reflects this to b; inversion
gives b inverse. Scalar restriction is exact, hence so is its left adjoint, ambient
scalar extension; the inclusion reflects distinguished triangles, so C is exact and,
with hI, so is I followed by C. Transport along the shift-compatible b gives exactness
of U followed by I. No inclusion is required to be strict.
-/
theorem fdIntegralScalarRestrictionExact
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (ordinary : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      FdOrdinaryScalarTransport l Ω T h)
    (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
    (hlift : fdIntegralScalarLiftProperty l Ω T stage ordinary b)
    (hI : ∀ E : Padic.FiniteCoefficientFields l Ω,
      (I l Ω T stage E).IsTriangulated) :
    (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      NatTrans.CommShift (b h).hom ℤ ∧ NatTrans.CommShift (b h).inv ℤ) ∧
    (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      (I l Ω T stage E ⋙ C l Ω T h).IsTriangulated ∧
        (U l Ω T h ⋙ I l Ω T stage L).IsTriangulated) := by
  have _ := hl
  have he {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
      (I l Ω T stage E ⋙ C l Ω T h).IsTriangulated := by
    have := hI E
    have := scalarExact l Ω T h
    infer_instance
  have hs {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :=
    scalarShift l Ω T stage ordinary b hlift h
  refine ⟨?_, ?_⟩
  · intro E L h
    have := hs h
    exact ⟨hs h, inferInstance⟩
  · intro E L h
    have := he h
    have := hs h
    exact ⟨he h, Functor.isTriangulated_of_iso (b h)⟩

end WeilConjectures
