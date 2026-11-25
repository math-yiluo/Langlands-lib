/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainMap
public import WeilConjectures.AlgebraicGeometry.DirectImageSquareUnitTransport
import WeilConjectures.AlgebraicGeometry.RingedSpaceDirectImageKInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparisonIntersection
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVResolvedRoofMateComparisons

/-! # Vertex normalization for the concrete resolved row roof

## References

* Stacks Project, Tags 08FE, 08HY, 08HZ and 0D5T
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AlgebraicGeometry

attribute [local instance 2000] schemeMVModuleAbelian

private lemma image_localization_isIso
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] :
    IsIso ((schemeMVDirectImageLocalization g).app
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).obj I)) := by
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
  let e := F.mapHomotopyCategoryFactors (.up ℤ)
  let β := G.rightDerivedFunctorUnit
  have : IsIso (β.app ((HomotopyCategory.quotient _ (.up ℤ) ⋙
      F.mapHomotopyCategory (.up ℤ)).obj I)) :=
    RingedSpace.isIso_moduleDirectImage_unit_on_kInjective
      f.toLRSHom.toShHom g.toLRSHom.toShHom I
  have hn := β.naturality (e.hom.app I)
  have : IsIso ((G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map (e.hom.app I) ≫
      β.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj I))) := by
    have hi : IsIso (β.app ((HomotopyCategory.quotient _ (.up ℤ) ⋙
        F.mapHomotopyCategory (.up ℤ)).obj I) ≫
      (DerivedCategory.Qh ⋙ G.rightDerivedFunctor).map (e.hom.app I)) := inferInstance
    rw [← hn] at hi
    exact hi
  have : IsIso (β.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj I))) :=
    IsIso.of_isIso_comp_left
      ((G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map (e.hom.app I)) _
  dsimp only [schemeMVDirectImageLocalization, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

private lemma openImage_isKInjective (X : Scheme.{u}) (W : X.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] : (schemeOpenModuleImageComplex X W I).IsKInjective := by
  have : (Scheme.Modules.pushforward W.ι).Additive :=
    Functor.additive_of_preserves_binary_products _
  have := isKInjective_schemeOpenRestriction X W I
  have := (schemeOpenModuleAdjunction X W).preservesKInjectiveComplexes
  change CochainComplex.IsKInjective
    (((Scheme.Modules.pushforward W.ι).mapHomologicalComplex (.up ℤ)).obj
      (((schemeOpenRestriction X W).mapHomologicalComplex (.up ℤ)).obj I))
  infer_instance

private lemma biprod_isKInjective {C : Type*} [Category C] [Abelian C]
    (I J : CochainComplex C ℤ) [I.IsKInjective] [J.IsKInjective] :
    (I ⊞ J).IsKInjective := by
  constructor
  intro K f hK
  have hI := (CochainComplex.IsKInjective.homotopyZero (f ≫ biprod.fst) hK).compRight
    (biprod.inl : I ⟶ I ⊞ J)
  have hJ := (CochainComplex.IsKInjective.homotopyZero (f ≫ biprod.snd) hK).compRight
    (biprod.inr : J ⟶ I ⊞ J)
  have he : (f ≫ biprod.fst) ≫ biprod.inl + (f ≫ biprod.snd) ≫ biprod.inr = f := by
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add,
      biprod.total, Category.comp_id]
  have ht := hI.add hJ
  rw [he] at ht
  exact ⟨ht.trans (Homotopy.ofEq (by simp))⟩

attribute [local instance] openImage_isKInjective biprod_isKInjective

private lemma map_image_quasiIso
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (s : ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj I ⟶ J) (hs : IsIso (DerivedCategory.Q.map s)) :
    IsIso (DerivedCategory.Q.map
      (((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).map s)) := by
  have := hs
  have := image_localization_isIso f g I
  have : IsIso ((schemeMVDirectImageLocalization g).app J) := by
    rw [schemeMVDirectImageLocalization_app]
    infer_instance
  have hn := (schemeMVDirectImageLocalization g).naturality s
  dsimp only [Functor.comp_map] at hn
  have hi : IsIso (DerivedCategory.Q.map
      (((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).map s) ≫ (schemeMVDirectImageLocalization g).app J) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((schemeMVDirectImageLocalization g).app J)

private lemma image_intersection_component_isIso
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y : Scheme.{u}} (h : X ⟶ Y) (U V : Y.Opens) (E : schemeDerivedCategory X)
    (s : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj (schemeMVResolution X E) ⟶
      schemeMVResolution Y ((schemeDerivedDirectImage h).obj E))
    (hs : (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
        (schemeMVResolution X E)).hom ≫ DerivedCategory.Q.map s ≫
        (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).hom =
      (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).hom) :
    IsIso (DerivedCategory.Q.map
      (schemeMVImageComponent h (U ⊓ V) (schemeMVResolution X E)
        (schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)) s)) := by
  let I := schemeMVResolution X E
  let J := schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)
  let W := U ⊓ V
  let W' := (h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)
  let a := (schemeDerivedDirectImage h).map
    (((schemeMVDerivedRestriction X W') ⋙ schemeDerivedDirectImage W'.ι).map
      (schemeMVResolutionIso X E).inv ≫
      (schemeOpenModuleImageComplexComparison X W' I (schemeMVAdjunction X W')).inv)
  let b := RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
    (schemeOpenModuleImageComplex X W' I)
  let c := ((schemeMVDerivedRestriction Y W) ⋙ schemeDerivedDirectImage W.ι).map
    (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).inv ≫
      (schemeOpenModuleImageComplexComparison Y W J (schemeMVAdjunction Y W)).inv
  have hn : a ≫ b.hom ≫ DerivedCategory.Q.map (schemeMVImageComponent h W I J s) =
      (schemeMVOpenComparison h W E).hom ≫ c :=
    schemeMV_image_resolution_comparison_intersection X Y h U V E s hs
  have : IsIso a := by dsimp only [a]; infer_instance
  have : IsIso c := by dsimp only [c]; infer_instance
  have : IsIso (a ≫ b.hom ≫ DerivedCategory.Q.map
      (schemeMVImageComponent h W I J s)) := by
    rw [hn]
    infer_instance
  have : IsIso (b.hom ≫ DerivedCategory.Q.map
      (schemeMVImageComponent h W I J s)) := IsIso.of_isIso_comp_left a _
  exact IsIso.of_isIso_comp_left b.hom _

private lemma image_component_isIso
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y : Scheme.{u}} (h : X ⟶ Y) (W : Y.Opens) (E : schemeDerivedCategory X)
    (s : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj (schemeMVResolution X E) ⟶
      schemeMVResolution Y ((schemeDerivedDirectImage h).obj E))
    (hs : (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
        (schemeMVResolution X E)).hom ≫ DerivedCategory.Q.map s ≫
        (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).hom =
      (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).hom) :
    IsIso (DerivedCategory.Q.map
      (schemeMVImageComponent h W (schemeMVResolution X E)
        (schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)) s)) := by
  let P : Y.Opens → Prop := fun T => IsIso (DerivedCategory.Q.map
    (schemeMVImageComponent h T (schemeMVResolution X E)
      (schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)) s))
  exact Eq.mp (congrArg P (inf_idem W))
    (image_intersection_component_isIso h W W E s hs)

private lemma map_biprod_isIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {X₁ X₂ Y₁ Y₂ : C}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    [IsIso (F.map f)] [IsIso (F.map g)] : IsIso (F.map (biprod.map f g)) := by
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  have he : F.map (biprod.map f g) ≫ (F.mapBiprod Y₁ Y₂).hom =
      (F.mapBiprod X₁ X₂).hom ≫ biprod.map (F.map f) (F.map g) := by
    apply biprod.hom_ext
    · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst,
        biprod.map_fst, biprod.lift_fst_assoc]
      rw [← F.map_comp, ← F.map_comp, biprod.map_fst]
    · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_snd,
        biprod.map_snd, biprod.lift_snd_assoc]
      rw [← F.map_comp, ← F.map_comp, biprod.map_snd]
  have : IsIso (biprod.map (F.map f) (F.map g)) :=
    (biprod.mapIso (asIso (F.map f)) (asIso (F.map g))).isIso_hom
  have : IsIso (F.map (biprod.map f g) ≫ (F.mapBiprod Y₁ Y₂).hom) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.mapBiprod Y₁ Y₂).hom

private lemma image_row_vertex_isIso
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y : Scheme.{u}} (h : X ⟶ Y) (U V : Y.Opens) (E : schemeDerivedCategory X)
    (s : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj (schemeMVResolution X E) ⟶
      schemeMVResolution Y ((schemeDerivedDirectImage h).obj E))
    (hs : DerivedCategory.Q.map s =
      (schemeMVDirectImageLocalization h).app (schemeMVResolution X E) ≫
      (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).hom ≫
      (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).inv) :
    let m := schemeMVImageChainMap h U V (schemeMVResolution X E)
      (schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)) s
    IsIso (DerivedCategory.Q.map m.τ₁) ∧ IsIso (DerivedCategory.Q.map m.τ₂) ∧
      IsIso (DerivedCategory.Q.map m.τ₃) := by
  classical
  let I := schemeMVResolution X E
  let J := schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)
  let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
  have hnorm : (RingedSpace.derivedModuleDirectImageKInjectiveIso
        h.toLRSHom.toShHom I).hom ≫ DerivedCategory.Q.map s ≫ (schemeMVResolutionIso Y
        ((schemeDerivedDirectImage h).obj E)).hom =
      (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).hom := by
    dsimp only [I]
    rw [hs, schemeMVDirectImageLocalization_app]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have hi₁ : IsIso (DerivedCategory.Q.map s) := by
    rw [hs, schemeMVDirectImageLocalization_app]
    infer_instance
  have hiU := image_component_isIso h U E s hnorm
  have hiV := image_component_isIso h V E s hnorm
  have hi₃ := image_component_isIso h (U ⊓ V) E s hnorm
  let cU := schemeMVImageComponent h U I J s
  let cV := schemeMVImageComponent h V I J s
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  have h₂ : (schemeMVImageChainMap h U V I J s).τ₂ =
      (F.mapBiprod (schemeOpenModuleImageComplex X (h ⁻¹ᵁ U) I)
        (schemeOpenModuleImageComplex X (h ⁻¹ᵁ V) I)).hom ≫ biprod.map cU cV := by
    change biprod.lift (F.map biprod.fst ≫ cU) (F.map biprod.snd ≫ cV) = _
    apply biprod.hom_ext <;> simp [Category.assoc]
  have : IsIso (DerivedCategory.Q.map (biprod.map cU cV)) :=
    map_biprod_isIso DerivedCategory.Q cU cV
  refine ⟨hi₁, ?_, hi₃⟩
  rw [h₂, DerivedCategory.Q.map_comp]
  infer_instance

/-- An isomorphic change of row functors preserves invertibility of all vertices. -/
private theorem row_roof_vertices_isIso
    {C D E T H : Type*}
    [Category C] [Category D] [Category E] [Category T] [Category H]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    [HasZeroMorphisms E] [HasZeroMorphisms T]
    (G : C ⥤ D) [G.PreservesZeroMorphisms]
    (F : D ⥤ E) [F.PreservesZeroMorphisms]
    (G' : C ⥤ T) [G'.PreservesZeroMorphisms]
    (F' : T ⥤ E) [F'.PreservesZeroMorphisms]
    (c : G' ⋙ F' ≅ G ⋙ F) (Q : E ⥤ H)
    (A : ShortComplex C) (R : ShortComplex D) (s : A.map G ⟶ R)
    (h₁ : IsIso (Q.map (F.map s.τ₁)))
    (h₂ : IsIso (Q.map (F.map s.τ₂)))
    (h₃ : IsIso (Q.map (F.map s.τ₃))) :
    let v := (A.mapNatIso c).hom ≫ F.mapShortComplex.map s
    IsIso (Q.map v.τ₁) ∧ IsIso (Q.map v.τ₂) ∧ IsIso (Q.map v.τ₃) := by
  have : IsIso (Q.map (A.mapNatIso c).hom.τ₁) :=
    (Q.mapIso (ShortComplex.π₁.mapIso (A.mapNatIso c))).isIso_hom
  have : IsIso (Q.map (A.mapNatIso c).hom.τ₂) :=
    (Q.mapIso (ShortComplex.π₂.mapIso (A.mapNatIso c))).isIso_hom
  have : IsIso (Q.map (A.mapNatIso c).hom.τ₃) :=
    (Q.mapIso (ShortComplex.π₃.mapIso (A.mapNatIso c))).isIso_hom
  have := h₁
  have := h₂
  have := h₃
  dsimp only
  change IsIso (Q.map ((A.mapNatIso c).hom.τ₁ ≫ F.map s.τ₁)) ∧
    IsIso (Q.map ((A.mapNatIso c).hom.τ₂ ≫ F.map s.τ₂)) ∧
    IsIso (Q.map ((A.mapNatIso c).hom.τ₃ ≫ F.map s.τ₃))
  simp only [Q.map_comp]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Insert the three denominator witnesses into an existing vertex comparison. -/
private theorem combine_vertex_comparisons
    {A₁ A₂ A₃ B₁ B₂ B₃ : Sort*} {H₁ H₂ H₃ : Prop}
    {P : A₁ → A₂ → A₃ → B₁ → B₂ → B₃ → H₁ → H₂ → H₃ → Prop}
    (h₁ : H₁) (h₂ : H₂) (h₃ : H₃)
    (h : ∃ a₁ a₂ a₃ b₁ b₂ b₃, P a₁ a₂ a₃ b₁ b₂ b₃ h₁ h₂ h₃) :
    ∃ a₁ a₂ a₃ b₁ b₂ b₃, ∃ (h₁ : H₁) (h₂ : H₂) (h₃ : H₃),
      P a₁ a₂ a₃ b₁ b₂ b₃ h₁ h₂ h₃ := by
  obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, h⟩ := h
  exact ⟨a₁, a₂, a₃, b₁, b₂, b₃, h₁, h₂, h₃, h⟩

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh RingedSpace.moduleDirectImage
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option cleanup.letToHave false
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
set_option backward.defeqAttrib.useBackward true

set_option linter.all false in
/-- The normalized coefficient lifts determine the vertex comparison of their
concrete roof. -/
theorem relativeMV_resolved_roof_vertex_normalization
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (r : schemeMVResolution X K ⟶
      schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    (s : ((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).obj (schemeMVResolution X' K') ⟶
      schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    (u₀ : schemeMayerVietorisComplex X U V (schemeMVResolution X K) ⟶
      schemeMayerVietorisComplex X U V
        (schemeMVResolution X ((schemeDerivedDirectImage g').obj K')))
    (hr : DerivedCategory.Q.map r = (schemeMVResolutionIso X K).hom ≫
      (relativeMVAdj g').homEquiv _ _ φ ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv)
    (hs : DerivedCategory.Q.map s =
      (schemeMVDirectImageLocalization g').app (schemeMVResolution X' K') ≫
      (schemeDerivedDirectImage g').map (schemeMVResolutionIso X' K').hom ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv)
    (hu₁ : u₀.τ₁ = r)
    (hu₂ : u₀.τ₂ = biprod.map
      (((schemeOpenModuleImage X U).mapHomologicalComplex (.up ℤ)).map r)
      (((schemeOpenModuleImage X V).mapHomologicalComplex (.up ℤ)).map r))
    (hu₃ : u₀.τ₃ =
      ((schemeOpenModuleImage X (U ⊓ V)).mapHomologicalComplex (.up ℤ)).map r) :
    let I := schemeMVResolution X K
    let J := schemeMVResolution X' K'
    let L := schemeMVResolution X ((schemeDerivedDirectImage g').obj K')
    let Ff := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
    let Ff' := (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
    let A := (schemeMayerVietorisComplex X U V I).map Ff
    let R := (schemeMayerVietorisComplex X U V L).map Ff
    let B := (schemeMayerVietorisComplex X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) J).map Ff'
    let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let F := G.mapHomologicalComplex (.up ℤ)
    let η := schemeMVDirectImageLocalization g
    let adj := relativeMVAdj g
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    let c := (Functor.mapHomologicalComplexCompIso
        (directImageSquareIso g' f f' g hpull.w) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom ⋙
          RingedSpace.moduleDirectImage g.toLRSHom.toShHom)) (.up ℤ)).symm).symm
    let D := schemeMayerVietorisComplex X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) J
    let u : A ⟶ R := Ff.mapShortComplex.map u₀
    let v : B.map F ⟶ R := (D.mapNatIso c).hom ≫
      Ff.mapShortComplex.map (schemeMVImageChainMap g' U V J L s)
    ∃ (e₁ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₁) ≅ a.left)
      (e₂ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₂) ≅
        (b U).left ⊞ (b V).left)
      (e₃ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₃) ≅ (b (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj B.X₁ ≅ a.right)
      (e₂' : DerivedCategory.Q.obj B.X₂ ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj B.X₃ ≅ (b (U ⊓ V)).right)
      (hv₁ : IsIso (DerivedCategory.Q.map v.τ₁))
      (hv₂ : IsIso (DerivedCategory.Q.map v.τ₂))
      (hv₃ : IsIso (DerivedCategory.Q.map v.τ₃)),
      letI := hv₁
      letI := hv₂
      letI := hv₃
      (DerivedCategory.Q.map u.τ₁ ≫ inv (DerivedCategory.Q.map v.τ₁) ≫ η.app B.X₁ =
        (adj.homEquiv _ _) (e₁.hom ≫ a.hom ≫ e₁'.inv)) ∧
      (DerivedCategory.Q.map u.τ₂ ≫ inv (DerivedCategory.Q.map v.τ₂) ≫ η.app B.X₂ =
        (adj.homEquiv _ _) (e₂.hom ≫ biprod.map (b U).hom (b V).hom ≫ e₂'.inv)) ∧
      (DerivedCategory.Q.map u.τ₃ ≫ inv (DerivedCategory.Q.map v.τ₃) ≫ η.app B.X₃ =
        (adj.homEquiv _ _) (e₃.hom ≫ (b (U ⊓ V)).hom ≫ e₃'.inv))  := by
  classical
  dsimp -proj only
  let J := schemeMVResolution X' K'
  let L := schemeMVResolution X ((schemeDerivedDirectImage g').obj K')
  let Ff := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
  let Ff' := (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
  let F := (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
  let c := (Functor.mapHomologicalComplexCompIso
      (directImageSquareIso g' f f' g hpull.w) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom ⋙
        RingedSpace.moduleDirectImage g.toLRSHom.toShHom)) (.up ℤ)).symm).symm
  let D := schemeMayerVietorisComplex X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) J
  let v₀ : D.map ((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
       (.up ℤ)) ⟶ schemeMayerVietorisComplex X U V L := schemeMVImageChainMap g' U V J L s
  obtain ⟨hi₁, hi₂, hi₃⟩ := image_row_vertex_isIso g' U V K' s hs
  have hp₁ := map_image_quasiIso g' f J L v₀.τ₁ hi₁
  have hp₂ := map_image_quasiIso g' f
    (schemeMayerVietorisB X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) J)
    (schemeMayerVietorisB X U V L) v₀.τ₂ hi₂
  have hp₃ := map_image_quasiIso g' f
    (schemeOpenModuleImageComplex X' ((g' ⁻¹ᵁ U) ⊓ (g' ⁻¹ᵁ V)) J)
    (schemeOpenModuleImageComplex X (U ⊓ V) L) v₀.τ₃ hi₃
  obtain ⟨hv₁, hv₂, hv₃⟩ := row_roof_vertices_isIso
    ((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ))
    Ff Ff' F c DerivedCategory.Q D _ v₀ hp₁ hp₂ hp₃
  exact combine_vertex_comparisons hv₁ hv₂ hv₃
    (relativeMV_resolved_roof_mate_comparisons f f' g g' hpull K K' φ U V
      r s u₀ hr hs hu₁ hu₂ hu₃ hv₁ hv₂ hv₃)

end AlgebraicGeometry
