/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
import all WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealizationExact
import WeilConjectures.AlgebraicGeometry.CompactAdicContinuousIdentification
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis

/-! # A scalar-compatible section-ideal comparison

Source: Stacks Tags 093M and 099L.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

attribute [local irreducible] upperStarFromPoint
  upperStarFromPointComp monoidal_upperStarFromPoint monoidal_pointUpperStar
  oplaxMonoidal_pointUpperStar

private theorem iso_hom_inv {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u}}
    (e : R ≅ S) (U : Cᵒᵖ) (a : R.obj.obj U) :
    e.inv.hom.app U (e.hom.hom.app U a) = a :=
  ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app U) e.hom_inv_id) a

private theorem iso_inv_hom {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u}}
    (e : R ≅ S) (U : Cᵒᵖ) (a : S.obj.obj U) :
    e.hom.hom.app U (e.inv.hom.app U a) = a :=
  iso_hom_inv e.symm U a

private theorem iso_inv_surjective {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u}}
    (e : R ≅ S) (U : Cᵒᵖ) : Function.Surjective (e.inv.hom.app U) :=
  fun a ↦ ⟨e.hom.hom.app U a, iso_hom_inv e U a⟩

private theorem iso_hom_injective {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u}}
    (e : R ≅ S) (U : Cᵒᵖ) : Function.Injective (e.hom.hom.app U) := by
  intro a b h
  simpa only [iso_hom_inv] using congrArg (e.inv.hom.app U) h

private theorem kernel_sections {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u}}
    (q : R ⟶ S) (U : C) :
    (ConstantCompletion.kernelIdeal q).sections U = RingHom.ker (q.hom.app (op U)).hom :=
  (ConstantCompletion.kernelIdeal_existsUnique q).exists.choose_spec U

private theorem kernel_mem_transport {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S R₀ S₀ : Sheaf J CommRingCat.{u}}
    (q : R ⟶ S) (q₀ : R₀ ⟶ S₀) (α : R ≅ R₀) (γ : S ≅ S₀)
    (hq : q ≫ γ.hom = α.hom ≫ q₀) (U : C) (a : R.obj.obj (op U)) :
    a ∈ (ConstantCompletion.kernelIdeal q).sections U ↔
      α.hom.hom.app (op U) a ∈ (ConstantCompletion.kernelIdeal q₀).sections U := by
  rw [kernel_sections, kernel_sections]
  change q.hom.app (op U) a = 0 ↔ q₀.hom.app (op U) (α.hom.hom.app (op U) a) = 0
  have hc := congrArg (fun f ↦ f.hom.app (op U) a) hq
  change γ.hom.hom.app (op U) (q.hom.app (op U) a) =
    q₀.hom.app (op U) (α.hom.hom.app (op U) a) at hc
  rw [← hc, ← map_zero (γ.hom.hom.app (op U)).hom]
  exact (iso_hom_injective γ (op U)).eq_iff.symm

private theorem kernel_extension_span {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (U : C) :
    (ConstantCompletion.kernelIdeal (ConstantCompletion.projection J A I 0)).sections U =
      Ideal.span (Set.range
        (fun a : (ConstantCompletion.kernelIdeal
          (ConstantCompletion.quotient J A I 0)).sections U ↦
            (ConstantCompletion.coefficientMap J A I).hom.app (op U) a)) := by
  rw [kernel_sections, ((ConstantCompletion.flat_and_quotients J A I).2.1 0 U).2]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    apply Ideal.subset_span
    refine ⟨⟨(ConstantCompletion.constantSection (J := J) a.val).val (op U), ?_⟩, rfl⟩
    rw [kernel_sections, ((ConstantCompletion.flat_and_quotients J A I).2.2 0 U).2]
    exact Ideal.subset_span ⟨a, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have ha := a.property
    simp only [kernel_sections,
      ((ConstantCompletion.flat_and_quotients J A I).2.2 0 U).2] at ha
    have hle : Ideal.span (Set.range (fun b : ↥(I ^ (0 + 1)) ↦
        (ConstantCompletion.constantSection (J := J) (b : A)).val (op U))) ≤
      Ideal.comap ((ConstantCompletion.coefficientMap J A I).hom.app (op U)).hom
        (Ideal.span (Set.range (fun b : ↥(I ^ (0 + 1)) ↦
          (ConstantCompletion.algebraSection (ConstantCompletion.coefficientMap J A I)
            b).val (op U)))) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨b, rfl⟩
      exact Ideal.subset_span ⟨b, rfl⟩
    exact hle ha

private def transportIdeal {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {B B₀ : Sheaf J CommRingCat.{u}}
    (β : B ≅ B₀) (K : RingedSiteIdeal B₀) : RingedSiteIdeal B where
  sections U := Ideal.comap (β.hom.hom.app (op U)).hom (K.sections U)
  restriction {U V} f a ha := by
    change β.hom.hom.app (op V) (B.obj.map f.op a) ∈ K.sections V
    have hn : B₀.obj.map f.op (β.hom.hom.app (op U) a) =
        β.hom.hom.app (op V) (B.obj.map f.op a) :=
      (ConcreteCategory.congr_hom (β.hom.hom.naturality f.op) a).symm
    rw [← hn]
    exact K.restriction f _ ha
  local_mem U a S hS ha := by
    apply K.local_mem U (β.hom.hom.app (op U) a) S hS
    intro V f hf
    have hn : B₀.obj.map f.op (β.hom.hom.app (op U) a) =
        β.hom.hom.app (op V) (B.obj.map f.op a) :=
      (ConcreteCategory.congr_hom (β.hom.hom.naturality f.op) a).symm
    erw [hn]
    exact ha V f hf

private theorem extension_span_transport {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {R B S : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (q : R ⟶ S)
    (α : R ≅ ConstantCompletion.constant J A)
    (β : B ≅ ConstantCompletion.completed J A I)
    (γ : S ≅ ConstantCompletion.finite J A I 0)
    (hc : φ ≫ β.hom = α.hom ≫ ConstantCompletion.coefficientMap J A I)
    (hq : q ≫ γ.hom = α.hom ≫ ConstantCompletion.quotient J A I 0)
    (U : C) :
    (transportIdeal β (ConstantCompletion.kernelIdeal
      (ConstantCompletion.projection J A I 0))).sections U =
      Ideal.span (Set.range (fun a : (ConstantCompletion.kernelIdeal q).sections U ↦
        φ.hom.app (op U) a)) := by
  let K := ConstantCompletion.kernelIdeal q
  let K₀ := ConstantCompletion.kernelIdeal (ConstantCompletion.quotient J A I 0)
  let p := (ConstantCompletion.projection J A I 0).hom.app (op U)
  let c := (ConstantCompletion.coefficientMap J A I).hom.app (op U)
  have hscalar (a : R.obj.obj (op U)) :
      β.hom.hom.app (op U) (φ.hom.app (op U) a) = c (α.hom.hom.app (op U) a) :=
    congrArg (fun f ↦ f.hom.app (op U) a) hc
  have hspan : Ideal.span (Set.range (fun a : K.sections U ↦
      β.hom.hom.app (op U) (φ.hom.app (op U) a))) =
      Ideal.span (Set.range (fun a : K₀.sections U ↦ c a)) := by
    congr 1
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨⟨α.hom.hom.app (op U) a,
        (kernel_mem_transport q _ α γ hq U a).mp a.property⟩, ?_⟩
      exact (hscalar a).symm
    · rintro ⟨a, rfl⟩
      refine ⟨⟨α.inv.hom.app (op U) a, ?_⟩, ?_⟩
      · apply (kernel_mem_transport q _ α γ hq U _).mpr
        simpa only [iso_inv_hom] using a.property
      · change β.hom.hom.app (op U) (φ.hom.app (op U)
          (α.inv.hom.app (op U) a.val)) = c a.val
        rw [hscalar, iso_inv_hom]
  have hspan' := kernel_extension_span (J := J) A I U
  change _ = Ideal.span (Set.range (fun a : K₀.sections U ↦ c a)) at hspan'
  have ht : Ideal.map (β.hom.hom.app (op U)).hom
      (Ideal.span (Set.range (fun a : K.sections U ↦ φ.hom.app (op U) a))) =
      (ConstantCompletion.kernelIdeal (ConstantCompletion.projection J A I 0)).sections U := by
    rw [Ideal.map_span, ← Set.range_comp', hspan, ← hspan']
  ext b
  change β.hom.hom.app (op U) b ∈
    (ConstantCompletion.kernelIdeal (ConstantCompletion.projection J A I 0)).sections U ↔
      b ∈ Ideal.span (Set.range (fun a : K.sections U ↦ φ.hom.app (op U) a))
  rw [← ht, Ideal.mem_map_iff_of_surjective _ (show Function.Surjective
    (β.hom.hom.app (op U)).hom from iso_inv_surjective β.symm _)]
  constructor
  · rintro ⟨a, ha, he⟩
    exact (iso_hom_injective β (op U) he) ▸ ha
  · intro hb
    exact ⟨b, hb, rfl⟩

private def pointConstantAbIso (A : Type u) [CommRing A] :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ≅ discreteObj A := by
  have : (coherentTopology Profinite.{u}).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  exact ((constantCommuteCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).app
        (CommRingCat.of (ULift.{u + 1} A))).symm

private theorem pointConstantAbIso_monoidal (A : Type u) [CommRing A] :
    IsMonHom (pointConstantAbIso A).hom := by
  let J := coherentTopology Profinite.{u}
  let B := ULift.{u + 1} A
  have : J.PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  let P := (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of B)
  let S := discreteSheaf A
  let g : P ⟶ S.obj := Functor.whiskerRight
    (toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of B)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let h : (constantSheaf J Ab.{u + 1}).obj (AddCommGrpCat.of B) ⟶ discreteObj A :=
    (presheafToSheaf J Ab.{u + 1}).map
      (Functor.whiskerRight g (forget₂ RingCat.{u + 1} Ab.{u + 1})) ≫
        (Sheaf.sheafifyRingPresheafIso J S).hom
  have hm : @IsMonHom _ _ _ _ _
      (Sheaf.monObj_presheafToSheaf_obj J
        (P ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) inferInstance h := by
    infer_instance
  have hm' : IsMonHom h := IsMonHom.of_eq h
    (constantSheafRingMonObj J B).symm rfl (hf := hm)
  have he : (pointConstantAbIso A).hom = h := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ (discreteObj A).property
    change _ ≫ (pointConstantAbIso A).hom.hom = _ ≫ h.hom
    have hleft : toSheafify J
        ((Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of B)) ≫
        (pointConstantAbIso A).hom.hom =
      Functor.whiskerRight
        (toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of B)))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
            forget₂ RingCat.{u + 1} Ab.{u + 1}) := by
      change _ ≫ (sheafifyMap J (Functor.constComp Profinite.{u}ᵒᵖ
        (CommRingCat.of B)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
            forget₂ RingCat.{u + 1} Ab.{u + 1})).inv ≫
          (sheafifyComposeIso J
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
              forget₂ RingCat.{u + 1} Ab.{u + 1}) _).hom) = _
      rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
        sheafComposeIso_hom_fac]
      ext U a
      rfl
    rw [hleft]
    let wg := Functor.whiskerRight g (forget₂ RingCat.{u + 1} Ab.{u + 1})
    have ht := (sheafificationAdjunction J Ab.{u + 1}).right_triangle_components
      ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj S)
    change toSheafify J (S.obj ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) ≫
      (Sheaf.sheafifyRingPresheafIso J S).hom.hom = 𝟙 _ at ht
    change wg = toSheafify J (P ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) ≫
      ((presheafToSheaf J Ab.{u + 1}).map wg).hom ≫
        (Sheaf.sheafifyRingPresheafIso J S).hom.hom
    erw [← Category.assoc, ← toSheafify_naturality, Category.assoc, ht,
      Category.comp_id]
  rw [he]
  exact hm'

private def discreteAbIso (A : Type u) [CommRing A] (X : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ≅ condensedRingObj (discreteObj A) X :=
  (constantSchemeIso X).app _ ≪≫ (upperStarFromPoint X).mapIso (pointConstantAbIso A)

private theorem discreteAbIso_mon (A : Type u) [CommRing A] (X : Scheme.{u}) :
    IsMonHom (discreteAbIso A X).hom := by
  let B := AddCommGrpCat.of (ULift.{u + 1} A)
  let P := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let F := upperStarFromPoint X
  let Q := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let transfer (m : MonObj (P.obj B)) : MonObj (F.obj (P.obj B)) :=
    @Functor.monObjObj _ _ _ _ _ _ F _ _ m
  have hi : @IsMonHom _ _ _ _ _ (transfer (P.monObjObj B)) (Q.monObjObj B)
      ((constantSchemeIso X).inv.app B) :=
    Functor.isMonHom_compAlgHom P F (constantSchemeIso X).inv B
  have hh := monHomInvExplicit (transfer (P.monObjObj B)) (Q.monObjObj B)
    ((constantSchemeIso X).app B).symm hi
  let := pointConstantAbIso_monoidal A
  have hmap : IsMonHom (F.map (pointConstantAbIso A).hom) := inferInstance
  dsimp only [discreteAbIso, Iso.trans_hom, Functor.mapIso_hom]
  exact FiniteDiscreteOrdinary.monHomCompExplicit _ _ _ _ _ hh hmap

private def discreteRingIso (A : Type u) [CommRing A] (X : Scheme.{u}) :
    Scheme.adicLisseConstantRing X (ULift.{u + 1} A) ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj (discreteObj A) X) := by
  let := discreteAbIso_mon A X
  let := AdmissibleScalarRealization.constantRingMap_isIso A X _ (discreteAbIso A X).hom
  exact asIso (AdmissibleScalarRealization.constantRingMap A X _ (discreteAbIso A X).hom)

private theorem discreteRingIso_unit (A : Type u) [CommRing A] (X : Scheme.{u})
    (U : X.ProEtᵒᵖ) (a : ULift.{u + 1} A) :
    (discreteRingIso A X).hom.hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U a) =
      (discreteAbIso A X).hom.hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a) := by
  let := discreteAbIso_mon A X
  exact AdmissibleScalarRealization.constantRingMap_normalization A X _
    (discreteAbIso A X).hom U a

attribute [local irreducible] discreteRingIso

private theorem discreteAbIso_naturality {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (X : Scheme.{u}) :
    (discreteAbIso A X).hom ≫ (upperStarFromPoint X).map (discreteMap f) =
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          (f.comp ULift.ringEquiv.toRingHom)).toAddMonoidHom) ≫
            (discreteAbIso B X).hom := by
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  have : (coherentTopology Profinite.{u}).PreservesSheafification V :=
    GrothendieckTopology.instPreservesSheafification _ _
  let g : CommRingCat.of (ULift.{u + 1} A) ⟶
      CommRingCat.of (ULift.{u + 1} B) := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    (f.comp ULift.ringEquiv.toRingHom))
  have hp := (constantCommuteCompose (coherentTopology Profinite.{u}) V).inv.naturality g
  have hs := (constantSchemeIso X).hom.naturality (V.map g)
  dsimp only [discreteAbIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp]
  change _ ≫ (upperStarFromPoint X).map
    (((constantCommuteCompose (coherentTopology Profinite.{u}) V).inv.app
      (CommRingCat.of (ULift.{u + 1} A))) ≫
        (constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} ⋙
          sheafCompose _ V).map g) = _
  rw [← hp, Functor.map_comp, ← Category.assoc]
  exact congrArg (fun h ↦ h ≫ (upperStarFromPoint X).map (pointConstantAbIso B).hom) hs.symm

private theorem discreteRingIso_naturality {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (X : Scheme.{u}) :
    (discreteRingIso A X).hom ≫ sectionMap X ((upperStarFromPoint X).map (discreteMap f)) =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          (f.comp ULift.ringEquiv.toRingHom))) ≫ (discreteRingIso B X).hom := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _
    (InternalAbelianSheafModule.sectionRingSheaf (Scheme.ProEt.topology X)
      (condensedRingObj (discreteObj B) X)).property
  ext U a
  change ((upperStarFromPoint X).map (discreteMap f)).hom.app U
    ((discreteRingIso A X).hom.hom.app U
      ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} A)))).app U a)) = _
  rw [discreteRingIso_unit]
  have hn := congrArg (fun h ↦ h.hom.app U
    ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) (discreteAbIso_naturality f X)
  change ((upperStarFromPoint X).map (discreteMap f)).hom.app U
    ((discreteAbIso A X).hom.hom.app U
      ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) =
    (discreteAbIso B X).hom.hom.app U
    (((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (AddCommGrpCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        (f.comp ULift.ringEquiv.toRingHom)).toAddMonoidHom)).hom.app U
          ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) at hn
  erw [hn]
  have : (sheafToPresheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).IsRightAdjoint :=
    (sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).isRightAdjoint
  let g : ULift.{u + 1} A →+* ULift.{u + 1} B :=
    ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)
  have hc := congr_app (toSheafify_naturality (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom g))) U
  have ha := congr_app (toSheafify_naturality (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).map (AddCommGrpCat.ofHom g.toAddMonoidHom))) U
  have hc' := ConcreteCategory.congr_hom hc a
  have ha' := ConcreteCategory.congr_hom ha a
  change (toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} B)))).app U (g a) =
    ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom g)).hom.app U
        ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} A)))).app U a) at hc'
  change (toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} B)))).app U (g a) =
    ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (AddCommGrpCat.ofHom g.toAddMonoidHom)).hom.app U
        ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a) at ha'
  change (discreteAbIso B X).hom.hom.app U
    (((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (AddCommGrpCat.ofHom g.toAddMonoidHom)).hom.app U
        ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) =
    (discreteRingIso B X).hom.hom.app U
      (((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom g)).hom.app U
          ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} A)))).app U a))
  erw [← hc', ← ha', discreteRingIso_unit]

private theorem pointConstantAbIso_scalar (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    (pointConstantAbIso A).hom ≫
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (constantToContinuous A) = FiniteConstantModel.scalarToContinuous A := by
  let J := coherentTopology Profinite.{u}
  have : J.PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (Profinite.continuousCoefficientRingObj A).property
  ext U a
  let he := (sheafificationAdjunction J Ab.{u + 1}).homEquiv
    ((Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))
      (Profinite.continuousCoefficientRingObj A)
  have hs := he.apply_symm_apply (FiniteConstantModel.constantFunctions A)
  dsimp only [he] at hs
  rw [Adjunction.homEquiv_unit] at hs
  have hc := ((sheafificationAdjunction J RingCat.{u + 1}).homEquiv
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A)))
    (Profinite.continuousMapRingSheafOfUniverse A)).apply_symm_apply
    (show (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A)) ⟶
      (Profinite.continuousMapRingSheafOfUniverse A).obj from
      { app S := RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ContinuousMap.C (α := S.unop)).comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ RingCat.hom_ext (by ext x; rfl) })
  have hu : toSheafify J
      ((Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
      (pointConstantAbIso A).hom.hom =
    Functor.whiskerRight
      (toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} A))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1}) := by
    change _ ≫ (sheafifyMap J (Functor.constComp Profinite.{u}ᵒᵖ _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).inv ≫
        (sheafifyComposeIso J _ _).hom) = _
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
      sheafComposeIso_hom_fac]
    ext S x
    rfl
  have hunit := congr_app hu U
  have hscalar := ConcreteCategory.congr_hom (congr_app hs U) a
  change (FiniteConstantModel.scalarToContinuous A).hom.app U
    ((toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a) =
      (FiniteConstantModel.constantFunctions A).app U a at hscalar
  erw [hscalar]
  change (constantToContinuous A).hom.app U
    ((pointConstantAbIso A).hom.hom.app U
      ((toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) = _
  erw [ConcreteCategory.congr_hom hunit a]
  dsimp only [constantToContinuous, NatTrans.comp_app]
  have huRing : Functor.whiskerRight (toSheafify J
      ((Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫
      (((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
        (CommRingCat.of (ULift.{u + 1} A))).hom.hom) =
    (Functor.constComp Profinite.{u}ᵒᵖ (CommRingCat.of (ULift.{u + 1} A))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom ≫
        toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
          (RingCat.of (ULift.{u + 1} A))) := by
    change _ ≫ ((sheafifyComposeIso J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).inv ≫
        sheafifyMap J (Functor.constComp Profinite.{u}ᵒᵖ
          (CommRingCat.of (ULift.{u + 1} A))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom) = _
    erw [← Category.assoc, sheafComposeIso_inv_fac, toSheafify_naturality]
  have hr := ConcreteCategory.congr_hom (congr_app huRing U) a
  change (((constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
      (CommRingCat.of (ULift.{u + 1} A))).hom.hom.app U)
    (((toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} A)))).app U) a) =
      ((toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} A)))).app U) a at hr
  change (((sheafificationAdjunction J RingCat.{u + 1}).homEquiv _ _).symm
    { app S := RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((ContinuousMap.C (α := S.unop)).comp ULift.ringEquiv.toRingHom))
      naturality := fun _ _ _ ↦ RingCat.hom_ext (by ext x; rfl) }).hom.app U
      ((((constantCommuteCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (ULift.{u + 1} A))).hom.hom.app U)
        (((toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} A)))).app U) a)) =
            (FiniteConstantModel.constantFunctions A).app U a
  erw [hr]
  rw [Adjunction.homEquiv_unit] at hc
  exact ConcreteCategory.congr_hom (congr_app hc U) a

private theorem discreteAbIso_scalar (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (X : Scheme.{u}) :
    (discreteAbIso A X).hom ≫ (upperStarFromPoint X).map
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (constantToContinuous A)) = FiniteDiscreteOrdinary.canonicalAbelianMap A X := by
  dsimp only [discreteAbIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp, pointConstantAbIso_scalar]
  rfl

private instance continuousPoint_comm (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : IsCommMonObj
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (Profinite.continuousMapRingSheafOfUniverse A)) :=
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafOfUniverse A) (fun S a b ↦
    @mul_comm (ULift.{u + 1} C(S.unop, A)) _ a b)

private theorem discreteRingIso_scalar (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (X : Scheme.{u}) :
    (discreteRingIso A X).hom ≫ sectionMap X ((upperStarFromPoint X).map
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (constantToContinuous A))) = FiniteDiscreteOrdinary.canonicalRingMap A X := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _
    (InternalAbelianSheafModule.sectionRingSheaf (Scheme.ProEt.topology X)
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) X)).property
  ext U a
  change ((upperStarFromPoint X).map
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (constantToContinuous A))).hom.app U
    ((discreteRingIso A X).hom.hom.app U
      ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} A)))).app U a)) = _
  rw [discreteRingIso_unit]
  exact (congrArg (fun h ↦ h.hom.app U
    ((toSheafify _ ((Functor.const X.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) (discreteAbIso_scalar A X)).trans
        (FiniteDiscreteOrdinary.canonicalRingMap_normalization A X U a).symm

private theorem continuousIntegers_identification (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    let := spectralNorm.normedField (Padic l) E
    AdmissibleScalarRealization.CompletedIdentification
      (Padic.coefficientExtensionIntegers l E) X
      (Padic.coefficientExtensionUniformizer l E) := by
  let := spectralNorm.normedField (Padic l) E
  let A := Padic.coefficientExtensionIntegers l E
  let p := Padic.coefficientExtensionUniformizer l E
  have hd := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span ({p} : Set A) = Padic.coefficientExtensionMaximalIdeal l E :=
    hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hp : p ≠ 0 := by
    intro hz
    rw [hz, Ideal.span_singleton_zero] at hgen
    exact hd.2.2.2.2.2.2.2.2.2.1 hgen.symm
  have : CompactSpace A := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).2.1
  exact compact_adic_continuous_identification A p hp
    (fun n ↦ Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n))
    (Padic.coefficientExtension_integers_coset_basis l E) X

private theorem completedScalar_projection (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ∃ e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj (integersObj l E) X) ≅
        Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E),
      ∀ n : ℕ,
        (discreteRingIso (Padic.coefficientExtensionIntegers l E) X).hom ≫
          sectionMap X (scalarMap l E X) ≫ e.hom ≫
            limit.π (Scheme.adicLisseRingSystem X (IntegralConstantCompletion.ideal l E))
              (op n) =
          (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom (Ideal.Quotient.mk
              (IntegralConstantCompletion.ideal l E ^ (n + 1)))) := by
  let := spectralNorm.normedField (Padic l) E
  obtain ⟨e, he, _⟩ := continuousIntegers_identification l E X
  refine ⟨e, ?_⟩
  intro n
  rw [← Category.assoc, ← Category.assoc]
  have hc := discreteRingIso_scalar (Padic.coefficientExtensionIntegers l E) X
  change (discreteRingIso (Padic.coefficientExtensionIntegers l E) X).hom ≫
    sectionMap X (scalarMap l E X) = _ at hc
  erw [hc]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _
    ((Scheme.adicLisseRingSystem X (IntegralConstantCompletion.ideal l E)).obj
      (op n)).property
  ext U a
  cases a with
  | up a =>
    have hn := he U a n
    rw [← FiniteDiscreteOrdinary.canonicalRingMap_normalization _ X U (ULift.up a)] at hn
    exact hn.trans (ConcreteCategory.congr_hom
      (congr_app (toSheafify_naturality (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IntegralConstantCompletion.ideal l E ^ (n + 1)))))) U) (ULift.up a))

private def residueLiftIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    CommRingCat.of (IntegralConstantCompletion.integers l E ⧸
      IntegralConstantCompletion.ideal l E ^ (0 + 1)) ≅
        CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)) := by
  let e : IntegralConstantCompletion.integers l E ≃+*
      Padic.coefficientExtensionIntegers l E := ULift.ringEquiv
  have hI : Padic.coefficientExtensionIdeal l E 1 =
      Ideal.map e.toRingHom (IntegralConstantCompletion.ideal l E ^ (0 + 1)) := by
    rw [Ideal.map_pow, IntegralConstantCompletion.ideal, Ideal.map_span,
      Set.image_singleton]
    rfl
  exact ((Ideal.quotientEquiv _ _ e hI).trans ULift.ringEquiv.symm).toCommRingCatIso

private theorem residueLiftIso_mk (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    CommRingCat.ofHom (Ideal.Quotient.mk
      (IntegralConstantCompletion.ideal l E ^ (0 + 1))) ≫ (residueLiftIso l E).hom =
        CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)).comp
            ULift.ringEquiv.toRingHom)) := by
  let e : IntegralConstantCompletion.integers l E ≃+*
      Padic.coefficientExtensionIntegers l E := ULift.ringEquiv
  have hI : Padic.coefficientExtensionIdeal l E 1 =
      Ideal.map e.toRingHom (IntegralConstantCompletion.ideal l E ^ (0 + 1)) := by
    rw [Ideal.map_pow, IntegralConstantCompletion.ideal, Ideal.map_span,
      Set.image_singleton]
    rfl
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change ULift.up ((Ideal.quotientEquiv
    (IntegralConstantCompletion.ideal l E ^ (0 + 1))
      (Padic.coefficientExtensionIdeal l E 1) e hI)
        (Ideal.Quotient.mk _ a)) = ULift.up (Ideal.Quotient.mk _ a.down)
  rw [Ideal.quotientEquiv_mk]
  rfl

attribute [local irreducible] discreteAbIso pointConstantAbIso residueLiftIso

/-- A scalar-compatible completion comparison identifies the extended discrete
residue kernel with the first completed residue kernel in section coordinates.

Source: Stacks Tags 093M and 099L, integral-models proof (1).
(auxiliary; not a blueprint node).

Proof: use the discrete coefficient comparisons, their naturality for the residue
map, and the compact-adic comparison normalized on constant scalars. The small-site
constant and limit comparisons give commuting scalar and residue squares. Apply
flat_and_quotients: the first completed kernel is generated by images of elements
of the discrete kernel. Transport this span through the ring isomorphisms and use
the local characterization of extension. This works also on empty objects. -/
theorem integralModels_residueIdealComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ∃ β : (Arrow.mk (smallMap X (scalarMap l E X))).right ≅
        ConstantCompletion.completed (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          (IntegralConstantCompletion.integers l E) (IntegralConstantCompletion.ideal l E),
      ∀ U : Scheme.coefficientProEtaleSiteModel.{u, u} X,
        ((ConstantCompletion.kernelIdeal (smallMap X (residueMap l E X))).extension
          (smallMap X (scalarMap l E X))).sections U =
        Ideal.comap (β.hom.hom.app (op U)).hom
          ((ConstantCompletion.kernelIdeal (ConstantCompletion.projection
            (Scheme.coefficientProEtaleModelTopology.{u, u} X)
            (IntegralConstantCompletion.integers l E)
            (IntegralConstantCompletion.ideal l E) 0)).sections U) := by
  classical
  let A := IntegralConstantCompletion.integers l E
  let I := IntegralConstantCompletion.ideal l E
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let F := Scheme.CompletedConstantAlgebra.pushRing X
  let i := discreteRingIso (Padic.coefficientExtensionIntegers l E) X
  let j := discreteRingIso (Padic.coefficientExtensionRing l E 1) X
  let c := sectionMap X (scalarMap l E X)
  let q := sectionMap X (residueMap l E X)
  obtain ⟨e, he⟩ := completedScalar_projection l E X
  let α := F.mapIso i.symm ≪≫ (Scheme.CompletedConstantAlgebra.constantsIso X).app
    (CommRingCat.of A)
  let β := F.mapIso e ≪≫ Scheme.CompletedConstantAlgebra.completionIso X I
  let γ := F.mapIso j.symm ≪≫ (Scheme.CompletedConstantAlgebra.constantsIso X).app
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))) ≪≫
      (constantSheaf J CommRingCat.{u + 1}).mapIso (residueLiftIso l E).symm
  have hscalar : F.map c ≫ β.hom = α.hom ≫
      ConstantCompletion.coefficientMap J A I := by
    apply (cancel_epi (F.map i.hom)).mp
    have h := Scheme.CompletedConstantAlgebra.coefficientMap_eq X I
      (i.hom ≫ c ≫ e.hom) he
    dsimp only [α, β, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    have hi : F.map i.hom ≫ F.map i.inv = 𝟙 _ := by
      rw [← F.map_comp, i.hom_inv_id, F.map_id]
    simp only [Category.assoc]
    rw [← Category.assoc (F.map i.hom) (F.map i.inv), hi, Category.id_comp]
    change F.map (i.hom ≫ c ≫ e.hom) ≫
      (Scheme.CompletedConstantAlgebra.completionIso X I).hom =
        ((Scheme.CompletedConstantAlgebra.constantsIso X).app (CommRingCat.of A)).hom ≫
          ConstantCompletion.coefficientMap J A I at h
    simpa only [F.map_comp, Category.assoc, Iso.app_hom] using h
  have hresidue : F.map q ≫ γ.hom = α.hom ≫
      ConstantCompletion.quotient J A I 0 := by
    apply (cancel_epi (F.map i.hom)).mp
    have hn := discreteRingIso_naturality
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)) X
    have hq : i.hom ≫ q ≫ j.inv =
        (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
            ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)).comp
              ULift.ringEquiv.toRingHom))) := by
      change i.hom ≫ q = _ at hn
      erw [← Category.assoc, hn, Category.assoc, j.hom_inv_id, Category.comp_id]
    let g : CommRingCat.of A ⟶ CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)) :=
      CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)).comp
          ULift.ringEquiv.toRingHom))
    have hm := (Scheme.CompletedConstantAlgebra.constantsIso X).hom.naturality g
    have hm' : F.map (i.hom ≫ q ≫ j.inv) ≫
        (Scheme.CompletedConstantAlgebra.constantsIso X).hom.app
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))) =
      (Scheme.CompletedConstantAlgebra.constantsIso X).hom.app (CommRingCat.of A) ≫
        (constantSheaf J CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))) ≫
            (constantSheaf J CommRingCat.{u + 1}).map (residueLiftIso l E).hom := by
      rw [hq]
      rw [← Functor.map_comp, residueLiftIso_mk]
      exact hm
    dsimp only [α, γ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    have h := congrArg (fun t ↦ t ≫
      (constantSheaf J CommRingCat.{u + 1}).map (residueLiftIso l E).inv) hm'
    have hi : F.map i.hom ≫ F.map i.inv = 𝟙 _ := by
      rw [← F.map_comp, i.hom_inv_id, F.map_id]
    simp only [Category.assoc]
    rw [← Category.assoc (F.map i.hom) (F.map i.inv), hi, Category.id_comp]
    have heq : (constantSheaf J CommRingCat.{u + 1}).map (residueLiftIso l E).hom ≫
        (constantSheaf J CommRingCat.{u + 1}).map (residueLiftIso l E).inv = 𝟙 _ := by
      rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id]
    simp only [Category.assoc] at h
    rw [heq, Category.comp_id] at h
    change _ = _ ≫ ConstantCompletion.quotient J A I 0 at h
    simpa only [F.map_comp, Category.assoc, Iso.app_hom] using h
  let : IsNoetherianRing A := IntegralConstantCompletion.integers_noetherian l E
  let K := ConstantCompletion.kernelIdeal (F.map q)
  let L := transportIdeal β
    (ConstantCompletion.kernelIdeal (ConstantCompletion.projection J A I 0))
  have hL : K.extension (F.map c) = L :=
    ConstantCompletion.extension_eq_of_span _ _ _
      (extension_span_transport A I (F.map c) (F.map q) α β γ hscalar hresidue)
  refine ⟨β, fun U ↦ ?_⟩
  change (K.extension (F.map c)).sections U = L.sections U
  exact congrArg (fun M ↦ M.sections U) hL

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
