/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelsExist
public import WeilConjectures.AlgebraicGeometry.RingComplexCechData
public import WeilConjectures.Topology.RingedSpaceModuleCohomology

/-! # The ring complex as a concrete Godement mapping fibre

Source: Stacks Project, Tags 099D and 0FKS.
The complex is constructed from global sections on the open complement of the ideal.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

namespace AlgebraicGeometry
noncomputable section

/-- The open complement of the vanishing locus of the ideal. -/
def ringComplexOpen (A : CommRingCat.{u}) (I : Ideal A) : (Spec A).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- The coefficient homomorphism from the ring into sections on the complement. -/
def ringComplexOpenRingMap (A : CommRingCat.{u}) (I : Ideal A) :
    A →+* Γ((ringComplexOpen A I).toScheme, ⊤) :=
  ((Scheme.ΓSpecIso A).inv ≫ (ringComplexOpen A I).ι.appTop).hom

/-- The inverse image of the ideal complement is the complement of the extended ideal. -/
theorem ringComplexOpen_preimage {A B : CommRingCat.{u}} (φ : A →+* B) (I : Ideal A) :
    (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ ringComplexOpen A I =
      ringComplexOpen B (I.map φ) := by
  ext p
  change (¬ I ≤ Ideal.comap φ p.asIdeal) ↔ ¬ I.map φ ≤ p.asIdeal
  rw [Ideal.map_le_iff_le_comap]

/-- The actual map of open complements associated to extension of an ideal. -/
def ringComplexOpenMap {A B : CommRingCat.{u}} (φ : A →+* B)
    (I : Ideal A) (J : Ideal B) (h : I.map φ = J) :
    (ringComplexOpen B J).toScheme ⟶ (ringComplexOpen A I).toScheme :=
  Scheme.Hom.resLE (Spec.map (CommRingCat.ofHom φ)) (ringComplexOpen A I)
    (ringComplexOpen B J) (by rw [ringComplexOpen_preimage, h])

/-- Constant modules on the one-object bottom-topology site. -/
def ringComplexConstant (A : CommRingCat.{u}) : ModuleCat.{u} A ⥤ RingSiteModules A where
  obj M :=
    { val :=
        { obj := fun _ ↦ M
          map := fun _ ↦ ModuleCat.ofHom LinearMap.id
          map_id := by intros; rfl
          map_comp := by intros; rfl }
      isSheaf := Presheaf.isSheaf_bot _ }
  map f :=
    { val :=
        { app := fun _ ↦ f
          naturality := by intros; ext x; rfl } }
  map_id := by intro M; rfl
  map_comp := by intro M N P f g; rfl

instance ringComplexConstant_additive (A : CommRingCat.{u}) :
    (ringComplexConstant A).Additive where
  map_add := by intros; rfl

/-- The actual Godement cosimplicial model, whose terms and cofaces are prescribed. -/
def ringComplexGodementModel (X : Scheme.{u}) : CosimplicialObject X.Modules :=
  (Scheme.Modules.moduleCup_godement_models_exist X
    (SheafOfModules.unit (moduleRings X.toRingedSpace))).choose

/-- The extended alternating coface complex of the prescribed Godement model. -/
def ringComplexGodementResolution (X : Scheme.{u}) : CochainComplex X.Modules ℤ :=
  (((alternatingCofaceMapComplex X.Modules).obj (ringComplexGodementModel X)).extend
    ComplexShape.embeddingUpNat)

/-- The germ augmentation of the prescribed Godement model. Its degree-zero formula
and its single-complex source determine every component uniquely. -/
def ringComplexGodementUnit (X : Scheme.{u}) :
    (CochainComplex.singleFunctor X.Modules 0).obj
      (SheafOfModules.unit (moduleRings X.toRingedSpace)) ⟶ ringComplexGodementResolution X :=
  (Scheme.Modules.moduleCup_godement_models_exist X
    (SheafOfModules.unit (moduleRings X.toRingedSpace))).choose_spec.choose

/-- Global sections with scalars restricted from A, placed on the one-object site. -/
def ringComplexOpenSections (A : CommRingCat.{u}) (I : Ideal A) :
    (ringComplexOpen A I).toScheme.Modules ⥤ RingSiteModules A :=
  RingedSpace.globalSectionsFunctor (ringComplexOpen A I).toScheme.toRingedSpace ⋙
    ModuleCat.restrictScalars (ringComplexOpenRingMap A I) ⋙ ringComplexConstant A

instance ringComplexOpenSections_additive (A : CommRingCat.{u}) (I : Ideal A) :
    (ringComplexOpenSections A I).Additive where
  map_add := by intros; rfl

/-- The complex of Godement sections on Spec A minus V(I). -/
def ringComplexGodementSections (A : CommRingCat.{u}) (I : Ideal A) :
    CochainComplex (RingSiteModules A) ℤ :=
  ((ringComplexOpenSections A I).mapHomologicalComplex (.up ℤ)).obj
    (ringComplexGodementResolution (ringComplexOpen A I).toScheme)

/-- Restriction of ring elements followed by the degree-zero germ augmentation. -/
def ringComplexGodementFirst (A : CommRingCat.{u}) (I : Ideal A) :
    ringComplexUnit A ⟶ (ringComplexGodementSections A I).X 0 := by
  let X := (ringComplexOpen A I).toScheme
  let F := SheafOfModules.unit (moduleRings X.toRingedSpace)
  let a := ringComplexGodementUnit X
  let b : F ⟶ (ringComplexGodementResolution X).X 0 :=
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).inv ≫ a.f 0
  let ρ := ringComplexOpenRingMap A I
  let v : A →ₗ[A] ((ModuleCat.restrictScalars ρ).obj
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj F)) :=
    { toFun := ρ
      map_add' := ρ.map_add
      map_smul' := by intro r x; exact ρ.map_mul r x }
  let r : ringComplexUnit A ⟶ (ringComplexOpenSections A I).obj F :=
    (ringComplexConstant A).map (ModuleCat.ofHom v)
  exact r ≫ (ringComplexOpenSections A I).map b

/-- The first differential is killed by the Godement differential. -/
theorem ringComplexGodementFirst_closed (A : CommRingCat.{u}) (I : Ideal A)
    (k : ℤ) (_hk : (ComplexShape.up ℤ).Rel 0 k) :
    ringComplexGodementFirst A I ≫ (ringComplexGodementSections A I).d 0 k = 0 := by
  let X := (ringComplexOpen A I).toScheme
  let F : X.Modules := SheafOfModules.unit (moduleRings X.toRingedSpace)
  let a := ringComplexGodementUnit X
  let S := ringComplexOpenSections A I
  have h : ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).inv ≫ a.f 0) ≫
      (ringComplexGodementResolution X).d 0 k = 0 := by
    erw [Category.assoc, a.comm 0 k, HomologicalComplex.single_obj_d,
      zero_comp]
  unfold ringComplexGodementFirst
  change _ ≫ S.map ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).inv ≫ a.f 0) ≫
    S.map ((ringComplexGodementResolution X).d 0 k) = 0
  erw [← S.map_comp, h, S.map_zero, comp_zero]

/-- The augmented map from A in degree zero into Godement sections. -/
def ringComplexGodementRestriction (A : CommRingCat.{u}) (I : Ideal A) :
    ringComplexSingle A ⟶ ringComplexGodementSections A I :=
  HomologicalComplex.mkHomFromSingle (ringComplexGodementFirst A I)
    (ringComplexGodementFirst_closed A I)

/-- The actual ring complex: the mapping fibre of restriction to Godement sections.
Source: Stacks Project, Tags 099D, 0FKS.
(auxiliary; not a blueprint node). -/
def ringComplexGodement (A : CommRingCat.{u}) (I : Ideal A) :
    CochainComplex (RingSiteModules A) ℤ :=
  (CochainComplex.mappingCone.triangle (ringComplexGodementRestriction A I)).invRotate.obj₁

/-- The projection of the mapping fibre onto A[0]. -/
def ringComplexGodementAugmentation (A : CommRingCat.{u}) (I : Ideal A) :
    ringComplexGodement A I ⟶ ringComplexSingle A :=
  (CochainComplex.mappingCone.triangle (ringComplexGodementRestriction A I)).invRotate.mor₁

end
end AlgebraicGeometry
