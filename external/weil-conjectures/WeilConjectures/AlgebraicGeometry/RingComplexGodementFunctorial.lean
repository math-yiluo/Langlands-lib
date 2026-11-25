/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexGodementConstruction
import all WeilConjectures.AlgebraicGeometry.RingComplexGodementModelMaps

/-! # Functorial maps of the concrete Godement ring complex -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] ringComplexGodementModel ringComplexGodementUnit
  ringComplexGodementResolution resmap

private abbrev pt : (Discrete PUnit.{u + 1})ᵒᵖ := op ⟨PUnit.unit⟩

private abbrev scalarRestriction {A B : CommRingCat.{u}} (φ : A →+* B) :
    RingSiteModules B ⥤ RingSiteModules A :=
  SheafOfModules.restrictScalars
    ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).map (ringSiteMap.{u} φ))

private def semiHom {A B : CommRingCat.{u}} (φ : A →+* B)
    {M : RingSiteModules A} {N : RingSiteModules B}
    (f : M.val.obj pt →ₛₗ[φ] N.val.obj pt) :
    M ⟶ (scalarRestriction φ).obj N where
  val.app U := by
    obtain ⟨⟨⟨⟩⟩⟩ := U
    letI : Module A (N.val.obj pt) := Module.compHom _ φ
    exact ModuleCat.ofHom (R := A) (show M.val.obj pt →ₗ[A]
        ((scalarRestriction φ).obj N).val.obj pt from
      { toFun := fun x ↦ f x
        map_add' := f.map_add
        map_smul' := f.map_smul' })
  val.naturality := by
    rintro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩ i
    have hi : i = 𝟙 _ := Subsingleton.elim _ _
    subst hi
    ext x
    simp
    rfl

private def semiComplexHom {A B : CommRingCat.{u}} (φ : A →+* B)
    {K : CochainComplex (RingSiteModules A) ℤ}
    {L : CochainComplex (RingSiteModules B) ℤ}
    (f : ∀ n, (K.X n).val.obj pt →ₛₗ[φ] (L.X n).val.obj pt)
    (comm : ∀ n k x, f k ((K.d n k).val.app pt x) =
      (L.d n k).val.app pt (f n x)) :
    K ⟶ ((scalarRestriction φ).mapHomologicalComplex (.up ℤ)).obj L where
  f n := semiHom φ (f n)
  comm' n k _ := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    rintro ⟨⟨⟨⟩⟩⟩
    ext x
    exact (comm n k x).symm

private def semiConeHom {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (R : D ⥤ C) [R.Additive]
    {K L : CochainComplex C ℤ}
    {K' L' : CochainComplex D ℤ}
    (f : K ⟶ L) (f' : K' ⟶ L')
    (a : K ⟶ (R.mapHomologicalComplex (.up ℤ)).obj K')
    (b : L ⟶ (R.mapHomologicalComplex (.up ℤ)).obj L')
    (h : f ≫ b = a ≫ (R.mapHomologicalComplex (.up ℤ)).map f') :
    CochainComplex.mappingCone f ⟶
      (R.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mappingCone f') :=
  CochainComplex.mappingCone.map f _ a b h ≫
    (CochainComplex.mappingCone.mapHomologicalComplexIso f' R).inv

private theorem semiConeHom_fst {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (R : D ⥤ C) [R.Additive]
    {K L : CochainComplex C ℤ}
    {K' L' : CochainComplex D ℤ}
    (f : K ⟶ L) (f' : K' ⟶ L')
    (a : K ⟶ (R.mapHomologicalComplex (.up ℤ)).obj K')
    (b : L ⟶ (R.mapHomologicalComplex (.up ℤ)).obj L')
    (h : f ≫ b = a ≫ (R.mapHomologicalComplex (.up ℤ)).map f')
    (p q : ℤ) (hpq : p + 1 = q) :
    (semiConeHom R f f' a b h).f p ≫ R.map
        ((CochainComplex.mappingCone.fst f').1.v p q hpq) =
      (CochainComplex.mappingCone.fst f).1.v p q hpq ≫ a.f q := by
  let H := R.mapHomologicalComplex (.up ℤ)
  unfold semiConeHom
  rw [HomologicalComplex.comp_f, Category.assoc]
  change (CochainComplex.mappingCone.map f (H.map f') a b h).f p ≫
      (CochainComplex.mappingCone.mapHomologicalComplexXIso f' R p).inv ≫ _ = _
  rw [CochainComplex.mappingCone.mapHomologicalComplexXIso_eq f' R p q hpq]
  change (CochainComplex.mappingCone.map f (H.map f') a b h).f p ≫
      ((CochainComplex.mappingCone.fst (H.map f')).1.v p q hpq ≫
          R.map ((CochainComplex.mappingCone.inl f').v q p (by omega)) +
        (CochainComplex.mappingCone.snd (H.map f')).v p p (add_zero p) ≫
          R.map ((CochainComplex.mappingCone.inr f').f p)) ≫ _ = _
  simp only [Preadditive.add_comp, Category.assoc, ← R.map_comp,
    CochainComplex.mappingCone.inl_v_fst_v,
    CochainComplex.mappingCone.inr_f_fst_v, R.map_id, R.map_zero,
    comp_zero, add_zero]
  rw [CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc_f _ _ _ _ p q hpq]
  simp only [Preadditive.add_comp, Category.assoc,
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  simp only [HomologicalComplex.comp_f, Category.assoc,
    CochainComplex.mappingCone.inl_v_fst_v_assoc,
    CochainComplex.mappingCone.inr_f_fst_v_assoc,
    comp_zero, add_zero, zero_comp]
  dsimp only [H, Functor.mapHomologicalComplex_obj_X]
  simp only [Category.comp_id]

private theorem semiConeHom_snd {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (R : D ⥤ C) [R.Additive]
    {K L : CochainComplex C ℤ}
    {K' L' : CochainComplex D ℤ}
    (f : K ⟶ L) (f' : K' ⟶ L')
    (a : K ⟶ (R.mapHomologicalComplex (.up ℤ)).obj K')
    (b : L ⟶ (R.mapHomologicalComplex (.up ℤ)).obj L')
    (h : f ≫ b = a ≫ (R.mapHomologicalComplex (.up ℤ)).map f')
    (p q : ℤ) (hpq : p + 1 = q) :
    (semiConeHom R f f' a b h).f p ≫ R.map
        ((CochainComplex.mappingCone.snd f').v p p (add_zero p)) =
      (CochainComplex.mappingCone.snd f).v p p (add_zero p) ≫ b.f p := by
  let H := R.mapHomologicalComplex (.up ℤ)
  unfold semiConeHom
  rw [HomologicalComplex.comp_f, Category.assoc]
  change (CochainComplex.mappingCone.map f (H.map f') a b h).f p ≫
      (CochainComplex.mappingCone.mapHomologicalComplexXIso f' R p).inv ≫ _ = _
  rw [CochainComplex.mappingCone.mapHomologicalComplexXIso_eq f' R p q hpq]
  change (CochainComplex.mappingCone.map f (H.map f') a b h).f p ≫
      ((CochainComplex.mappingCone.fst (H.map f')).1.v p q hpq ≫
          R.map ((CochainComplex.mappingCone.inl f').v q p (by omega)) +
        (CochainComplex.mappingCone.snd (H.map f')).v p p (add_zero p) ≫
          R.map ((CochainComplex.mappingCone.inr f').f p)) ≫ _ = _
  simp only [Preadditive.add_comp, Category.assoc, ← R.map_comp,
    CochainComplex.mappingCone.inl_v_snd_v,
    CochainComplex.mappingCone.inr_f_snd_v, R.map_id, R.map_zero,
    comp_zero, zero_add]
  rw [CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc_f _ _ _ _ p q hpq]
  simp only [Preadditive.add_comp, Category.assoc,
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  simp only [HomologicalComplex.comp_f, Category.assoc,
    CochainComplex.mappingCone.inl_v_snd_v_assoc,
    CochainComplex.mappingCone.inr_f_snd_v_assoc,
    comp_zero, zero_add, zero_comp]
  dsimp only [H, Functor.mapHomologicalComplex_obj_X]
  simp only [Category.comp_id]

private def structureMap {X Y : Scheme.{u}} (f : Y ⟶ X) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

private theorem structureMap_id (X : Scheme.{u}) :
    structureMap (𝟙 X) = (Scheme.Modules.pushforwardId X).inv.app
      (SheafOfModules.unit X.ringCatSheaf) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext
  rfl

private theorem structureMap_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    structureMap (g ≫ f) = structureMap f ≫
      (Scheme.Modules.pushforward f).map (structureMap g) ≫
      (Scheme.Modules.pushforwardComp g f).hom.app
        (SheafOfModules.unit Z.ringCatSheaf) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext
  rfl

private def resolutionSectionsMap {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℤ) :
    ((ringComplexGodementResolution X).X n).val.obj (op ⊤) →ₛₗ[f.appTop.hom]
      ((ringComplexGodementResolution Y).X n).val.obj (op ⊤) where
  toFun := (resmap f (structureMap f)).f n |>.val.app (op ⊤)
  map_add' := map_add _
  map_smul' := ((resmap f (structureMap f)).f n |>.val.app (op ⊤)).hom.map_smul

private theorem resolutionSectionsMap_id (X : Scheme.{u}) (n : ℤ)
    (x : ((ringComplexGodementResolution X).X n).val.obj (op ⊤)) :
    resolutionSectionsMap (𝟙 X) n x = x := by
  change (((resmap (𝟙 X) (structureMap (𝟙 X))).f n).val.app (op ⊤)) x = x
  rw [structureMap_id, resmap_id]
  rfl

private theorem resolutionSectionsMap_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X)
    (g : Z ⟶ Y) (n : ℤ)
    (x : ((ringComplexGodementResolution X).X n).val.obj (op ⊤)) :
    resolutionSectionsMap (g ≫ f) n x =
      resolutionSectionsMap g n (resolutionSectionsMap f n x) := by
  change (((resmap (g ≫ f) (structureMap (g ≫ f))).f n).val.app (op ⊤)) x = _
  rw [structureMap_comp, resmap_comp]
  rfl

private theorem openMap_id (A : CommRingCat.{u}) (I : Ideal A)
    (h : I.map (RingHom.id A) = I) :
    ringComplexOpenMap (RingHom.id A) I I h = 𝟙 _ := by
  apply (cancel_mono (ringComplexOpen A I).ι).1
  simp only [ringComplexOpenMap, Scheme.Hom.resLE_comp_ι,
    show CommRingCat.ofHom (RingHom.id A) = 𝟙 A from rfl, Category.id_comp]
  rw [show Spec.map (𝟙 A) = 𝟙 (Spec A) from Scheme.Spec.map_id (op A)]
  exact Category.comp_id _

private theorem openMap_comp {A B D : CommRingCat.{u}} (φ : A →+* B) (ψ : B →+* D)
    (I : Ideal A) (J : Ideal B) (L : Ideal D) (h : I.map φ = J)
    (h' : J.map ψ = L) (h'' : I.map (ψ.comp φ) = L) :
    ringComplexOpenMap ψ J L h' ≫ ringComplexOpenMap φ I J h =
      ringComplexOpenMap (ψ.comp φ) I L h'' := by
  apply (cancel_mono (ringComplexOpen A I).ι).1
  simp only [ringComplexOpenMap, Category.assoc, Scheme.Hom.resLE_comp_ι,
    Scheme.Hom.resLE_comp_ι_assoc]
  rw [← Spec.map_comp]
  rfl

private theorem openRingMap_naturality {A B : CommRingCat.{u}} (φ : A →+* B)
    (I : Ideal A) (J : Ideal B) (h : I.map φ = J) :
    (ringComplexOpenMap φ I J h).appTop.hom.comp (ringComplexOpenRingMap A I) =
      (ringComplexOpenRingMap B J).comp φ := by
  change (((Scheme.ΓSpecIso A).inv ≫ (ringComplexOpen A I).ι.appTop) ≫
      (ringComplexOpenMap φ I J h).appTop).hom =
    ((CommRingCat.ofHom φ) ≫ (Scheme.ΓSpecIso B).inv ≫
      (ringComplexOpen B J).ι.appTop).hom
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, ringComplexOpenMap,
    Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rw [Category.assoc]
  rfl

private def sectionsMap {A B : CommRingCat.{u}} (φ : A →+* B)
    (I : Ideal A) (J : Ideal B) (h : I.map φ = J) (n : ℤ) :
    ((ringComplexGodementSections A I).X n).val.obj pt →ₛₗ[φ]
      ((ringComplexGodementSections B J).X n).val.obj pt where
  toFun := resolutionSectionsMap (ringComplexOpenMap φ I J h) n
  map_add' := map_add _
  map_smul' r x := by
    change resolutionSectionsMap (ringComplexOpenMap φ I J h) n
        (ringComplexOpenRingMap A I r •
          (show ((ringComplexGodementResolution (ringComplexOpen A I).toScheme).X n).val.obj
            (op ⊤) from x)) =
      ringComplexOpenRingMap B J (φ r) • _
    rw [LinearMap.map_smulₛₗ]
    exact congrArg (fun r ↦ r • resolutionSectionsMap (ringComplexOpenMap φ I J h) n x)
      (RingHom.congr_fun (openRingMap_naturality φ I J h) r)

private theorem sectionsMap_comm {A B : CommRingCat.{u}} (φ : A →+* B)
    (I : Ideal A) (J : Ideal B) (h : I.map φ = J) (n k : ℤ)
    (x : ((ringComplexGodementSections A I).X n).val.obj pt) :
    sectionsMap φ I J h k ((ringComplexGodementSections A I).d n k |>.val.app pt <| x) =
      ((ringComplexGodementSections B J).d n k).val.app pt (sectionsMap φ I J h n x) := by
  exact (congrArg (fun z ↦ z.val.app (op ⊤) x)
    ((resmap (ringComplexOpenMap φ I J h) (structureMap _)).comm n k)).symm

private theorem sectionsMap_id (A : CommRingCat.{u}) (I : Ideal A)
    (h : I.map (RingHom.id A) = I) (n : ℤ)
    (x : ((ringComplexGodementSections A I).X n).val.obj pt) :
    sectionsMap (RingHom.id A) I I h n x = x := by
  change resolutionSectionsMap (ringComplexOpenMap (RingHom.id A) I I h) n x = x
  rw [openMap_id]
  exact resolutionSectionsMap_id _ n x

private theorem sectionsMap_comp {A B D : CommRingCat.{u}} (φ : A →+* B) (ψ : B →+* D)
    (I : Ideal A) (J : Ideal B) (L : Ideal D) (h : I.map φ = J)
    (h' : J.map ψ = L) (h'' : I.map (ψ.comp φ) = L) (n : ℤ)
    (x : ((ringComplexGodementSections A I).X n).val.obj pt) :
    sectionsMap ψ J L h' n (sectionsMap φ I J h n x) =
      sectionsMap (ψ.comp φ) I L h'' n x := by
  change resolutionSectionsMap (ringComplexOpenMap ψ J L h') n
      (resolutionSectionsMap (ringComplexOpenMap φ I J h) n x) =
    resolutionSectionsMap (ringComplexOpenMap (ψ.comp φ) I L h'') n x
  rw [← resolutionSectionsMap_comp, openMap_comp]

private def singleMap {A B : CommRingCat.{u}} (φ : A →+* B) :
    ringComplexSingle A ⟶
      ((scalarRestriction φ).mapHomologicalComplex (.up ℤ)).obj (ringComplexSingle B) :=
  HomologicalComplex.mkHomFromSingle
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ringComplexUnit A)).hom ≫
      semiHom φ (M := ringComplexUnit A) (N := ringComplexUnit B)
        { toFun := φ
          map_add' := φ.map_add
          map_smul' := φ.map_mul } ≫
      (scalarRestriction φ).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ringComplexUnit B)).inv)
    (by intros; simp)

private theorem singleMap_zero {A B : CommRingCat.{u}} (φ : A →+* B)
    (x : ((ringComplexSingle A).X 0).val.obj pt) :
    ((singleMap φ).f 0).val.app pt x = φ x := by
  rw [singleMap, HomologicalComplex.mkHomFromSingle_f]
  rfl

private def sectionsComplexMap {A B : CommRingCat.{u}} (φ : A →+* B)
    (I : Ideal A) (J : Ideal B) (h : I.map φ = J) :
    ringComplexGodementSections A I ⟶
      ((scalarRestriction φ).mapHomologicalComplex (.up ℤ)).obj
        (ringComplexGodementSections B J) :=
  semiComplexHom φ (sectionsMap φ I J h) (sectionsMap_comm φ I J h)

private theorem restrictionValue (A : CommRingCat.{u}) (I : Ideal A)
    (x : ((ringComplexSingle A).X 0).val.obj pt) :
    ((ringComplexGodementRestriction A I).f 0).val.app pt x =
      ((ringComplexGodementUnit (ringComplexOpen A I).toScheme).f 0).val.app (op ⊤)
        (ringComplexOpenRingMap A I x) := by
  unfold ringComplexGodementRestriction
  rw [HomologicalComplex.mkHomFromSingle_f]
  rfl

private theorem restriction_square {A B : CommRingCat.{u}} (φ : A →+* B)
    (I : Ideal A) (J : Ideal B) (h : I.map φ = J) :
    ringComplexGodementRestriction A I ≫ sectionsComplexMap φ I J h =
      singleMap φ ≫ ((scalarRestriction φ).mapHomologicalComplex (.up ℤ)).map
        (ringComplexGodementRestriction B J) := by
  apply HomologicalComplex.from_single_hom_ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨⟨⟨⟩⟩⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change sectionsMap φ I J h 0 (((ringComplexGodementRestriction A I).f 0).val.app pt x) =
    ((ringComplexGodementRestriction B J).f 0).val.app pt
      (((singleMap φ).f 0).val.app pt x)
  rw [restrictionValue, singleMap_zero, restrictionValue]
  change (((resmap (ringComplexOpenMap φ I J h) (structureMap _)).f 0).val.app (op ⊤))
      (((ringComplexGodementUnit (ringComplexOpen A I).toScheme).f 0).val.app (op ⊤)
        (ringComplexOpenRingMap A I x)) = _
  have ha := congrArg (fun z ↦ z.val.app (op ⊤) (ringComplexOpenRingMap A I x))
    (resmap_aug (ringComplexOpenMap φ I J h) (structureMap _))
  change _ = ((ringComplexGodementUnit (ringComplexOpen B J).toScheme).f 0).val.app
    (op ⊤) ((ringComplexOpenMap φ I J h).appTop (ringComplexOpenRingMap A I x)) at ha
  rw [show (ringComplexOpenMap φ I J h).appTop (ringComplexOpenRingMap A I x) =
    ringComplexOpenRingMap B J (φ x) from
      RingHom.congr_fun (openRingMap_naturality φ I J h) x] at ha
  exact ha

private def fibreMap {A B : CommRingCat.{u}} (φ : A →+* B)
    (I : Ideal A) (J : Ideal B) (h : I.map φ = J) :
    ringComplexGodement A I ⟶
      ((scalarRestriction φ).mapHomologicalComplex (.up ℤ)).obj
        (ringComplexGodement B J) :=
  (semiConeHom (scalarRestriction φ)
    (ringComplexGodementRestriction A I) (ringComplexGodementRestriction B J)
    (singleMap φ) (sectionsComplexMap φ I J h) (restriction_square φ I J h))⟦-1⟧' ≫
    ((scalarRestriction φ).mapCochainComplexShiftIso (-1)).inv.app _

private def fibreMapSemi {A B : CommRingCat.{u}} (φ : A →+* B)
    (I : Ideal A) (J : Ideal B) (h : I.map φ = J) (n : ℤ) :
    ((ringComplexGodement A I).X n).val.obj pt →ₛₗ[φ]
      ((ringComplexGodement B J).X n).val.obj pt where
  toFun := ((fibreMap φ I J h).f n).val.app pt
  map_add' := map_add _
  map_smul' := (((fibreMap φ I J h).f n).val.app pt).hom.map_smul

private abbrev fibreFst (A : CommRingCat.{u}) (I : Ideal A) (n : ℤ) :=
  (CochainComplex.mappingCone.fst (ringComplexGodementRestriction A I)).1.v
    (n + -1) n (by omega)

private abbrev fibreSnd (A : CommRingCat.{u}) (I : Ideal A) (n : ℤ) :=
  (CochainComplex.mappingCone.snd (ringComplexGodementRestriction A I)).v
    (n + -1) (n + -1) (add_zero _)

private theorem fibreMap_fst {A B : CommRingCat.{u}} (φ : A →+* B)
    (I : Ideal A) (J : Ideal B) (h : I.map φ = J) (n : ℤ)
    (x : ((ringComplexGodement A I).X n).val.obj pt) :
    (fibreFst B J n).val.app pt (fibreMapSemi φ I J h n x) =
      ((singleMap φ).f n).val.app pt ((fibreFst A I n).val.app pt x) := by
  have hh := semiConeHom_fst (scalarRestriction φ)
    (ringComplexGodementRestriction A I) (ringComplexGodementRestriction B J)
    (singleMap φ) (sectionsComplexMap φ I J h) (restriction_square φ I J h)
    (n + -1) n (by omega)
  have he := congrArg (fun z ↦ z.val.app pt x) hh
  exact he

private theorem fibreMap_snd {A B : CommRingCat.{u}} (φ : A →+* B)
    (I : Ideal A) (J : Ideal B) (h : I.map φ = J) (n : ℤ)
    (x : ((ringComplexGodement A I).X n).val.obj pt) :
    (fibreSnd B J n).val.app pt (fibreMapSemi φ I J h n x) =
      sectionsMap φ I J h (n + -1) ((fibreSnd A I n).val.app pt x) := by
  have hh := semiConeHom_snd (scalarRestriction φ)
    (ringComplexGodementRestriction A I) (ringComplexGodementRestriction B J)
    (singleMap φ) (sectionsComplexMap φ I J h) (restriction_square φ I J h)
    (n + -1) n (by omega)
  have he := congrArg (fun z ↦ z.val.app pt x) hh
  exact he

private theorem fibre_ext (A : CommRingCat.{u}) (I : Ideal A) (n : ℤ)
    (x y : ((ringComplexGodement A I).X n).val.obj pt)
    (h₁ : (fibreFst A I n).val.app pt x = (fibreFst A I n).val.app pt y)
    (h₂ : (fibreSnd A I n).val.app pt x = (fibreSnd A I n).val.app pt y) : x = y := by
  have hh := CochainComplex.mappingCone.id_X (ringComplexGodementRestriction A I)
    (n + -1) n (by omega)
  have hx := congrArg (fun f ↦ f.val.app pt x) hh
  have hy := congrArg (fun f ↦ f.val.app pt y) hh
  let i₁ := (CochainComplex.mappingCone.inl (ringComplexGodementRestriction A I)).v
    n (n + -1) (by omega)
  let i₂ := (CochainComplex.mappingCone.inr (ringComplexGodementRestriction A I)).f (n + -1)
  change i₁.val.app pt ((fibreFst A I n).val.app pt x) +
    i₂.val.app pt ((fibreSnd A I n).val.app pt x) = x at hx
  change i₁.val.app pt ((fibreFst A I n).val.app pt y) +
    i₂.val.app pt ((fibreSnd A I n).val.app pt y) = y at hy
  rw [← hx, ← hy, h₁, h₂]

private theorem singleMap_id (A : CommRingCat.{u}) (n : ℤ)
    (x : ((ringComplexSingle A).X n).val.obj pt) :
    ((singleMap (RingHom.id A)).f n).val.app pt x = x := by
  by_cases hn : n = 0
  · subst n
    exact singleMap_zero _ x
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ringComplexUnit A) n hn
    have hz' := (SheafOfModules.evaluation _ pt).map_isZero hz
    have hs := ModuleCat.subsingleton_of_isZero hz'
    exact @Subsingleton.elim (((ringComplexSingle A).X n).val.obj pt) hs _ _

private theorem singleMap_comp {A B D : CommRingCat.{u}} (φ : A →+* B) (ψ : B →+* D)
    (n : ℤ) (x : ((ringComplexSingle A).X n).val.obj pt) :
    ((singleMap ψ).f n).val.app pt (((singleMap φ).f n).val.app pt x) =
      ((singleMap (ψ.comp φ)).f n).val.app pt x := by
  by_cases hn : n = 0
  · subst n
    rw [singleMap_zero, singleMap_zero, singleMap_zero]
    rfl
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ringComplexUnit D) n hn
    have hz' := (SheafOfModules.evaluation _ pt).map_isZero hz
    have hs := ModuleCat.subsingleton_of_isZero hz'
    exact @Subsingleton.elim (((ringComplexSingle D).X n).val.obj pt) hs _ _

private theorem coneAugmentation_zero {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (CochainComplex.mappingCone.triangle f).invRotate.mor₁.f 0 =
      (CochainComplex.mappingCone.fst f).1.v (-1) 0 (by omega) := by
  simp [CategoryTheory.Pretriangulated.Triangle.invRotate,
    CochainComplex.mappingCone.triangle,
    CochainComplex.HomComplex.Cochain.rightShift_v _ 1 0 (zero_add 1)
      (-1) (-1) (by omega) 0 (by omega),
    shiftFunctorCompIsoId, CochainComplex.shiftFunctorObjXIso,
    CochainComplex.shiftFunctorAdd'_inv_app_f', CochainComplex.shiftFunctorZero_hom_app_f]

private theorem augmentationValue (A : CommRingCat.{u}) (I : Ideal A)
    (x : ((ringComplexGodement A I).X 0).val.obj pt) :
    ringComplexAugmentationValue (ringComplexGodementAugmentation A I) x =
      (fibreFst A I 0).val.app pt x := by
  unfold ringComplexAugmentationValue ringComplexGodementAugmentation
  rw [coneAugmentation_zero]
  rfl

/-- The Godement mapping fibres form a strictly functorial augmented family.
Source: Stacks Project, Tag 099D(a),(b), via the concrete Godement construction,
Tag 0FKS. (auxiliary; not a blueprint node)

Proof: a ring map induces a map between the open complements, since a prime
contains the extended ideal precisely when its inverse image contains the original
ideal. Apply ringComplex_godement_model_maps to the structure-module coefficient map.
It gives extended cochain maps with strict identity and composition equations and
the actual germ-augmentation square. Take global sections; these operations
preserve those equations and the cochain equation.
Together with the coefficient homomorphism in degree zero this gives a square of
the restriction maps A[0] to Godement sections after restriction of scalars
from B to A. Restriction of scalars preserves finite biproducts and shifts, so
apply the mapping-cone map and inverse rotation, then identify its target with
the restriction of the B mapping fibre. On sections this is a semilinear map.
Its projection is the ring map, so the
augmentation square commutes. For an identity, the coordinate formula is the
identity; for a composite both formulas select the same point and apply the
composite stalk map. Thus identity and composition hold on the nose, including
all transports along equal ideals, by proof irrelevance. -/
theorem ringComplex_godement_functorial :
    ∃ m : RingComplexMaps (fun A I ↦ ringComplexGodement A I.val),
      RingComplexFunctorial (fun A I ↦ ringComplexGodement A I.val)
        (fun A I ↦ ringComplexGodementAugmentation A I.val) m := by
  refine ⟨fun _ _ φ I J h ↦ fibreMapSemi φ I.val J.val h, ?_, ?_, ?_, ?_⟩
  · intro A B φ I J h n k x
    exact (congrArg (fun z ↦ z.val.app pt x) ((fibreMap φ I.val J.val h).comm n k)).symm
  · intro A B φ I J h x
    rw [augmentationValue, augmentationValue, fibreMap_fst, singleMap_zero]
  · intro A I h n x
    apply fibre_ext A I.val n
    · rw [fibreMap_fst, singleMap_id]
    · rw [fibreMap_snd, sectionsMap_id]
  · intro A B D φ ψ I J L h h' h'' n x
    apply fibre_ext D L.val n
    · rw [fibreMap_fst, fibreMap_fst, fibreMap_fst, singleMap_comp]
    · rw [fibreMap_snd, fibreMap_snd, fibreMap_snd, sectionsMap_comp]

end
end AlgebraicGeometry
