import Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctionsDirectImage
import Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctionsAlgebra
import Langlands.AlgebraicGeometry.Modules.TildePullback
import Langlands.AlgebraicGeometry.Modules.AffineVanishing.QuasicoherentCech
import Langlands.AlgebraicGeometry.FreeSectionPullback

/-! # The canonical arbitrary-base global-functions sheaf comparison -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open scoped ChangeOfRings TensorProduct

namespace Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctions

section General

variable {R S : CommRingCat.{u}} {X Y T : Scheme.{u}}
  (f : X ⟶ Spec R) (t : T ⟶ Spec R) (g : Y ⟶ X) (p : Y ⟶ T)
  (w : g ≫ f = p ≫ t)

/-- The actual pullback of global functions, with the base scalar action
in the commuting square. -/
def directImageGlobalSectionsMap :
    (relativeGlobalSections f).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      (relativeGlobalSections t).obj
        ((Scheme.Modules.pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf)) :=
  (relativeGlobalSections f).map (Langlands.Scheme.Modules.unitToPushforwardUnit g) ≫
    (relativeGlobalSectionsCompIso g f).hom.app _ ≫
    moduleSpecΓFunctor.map ((Scheme.Modules.pushforwardCongr w).hom.app _) ≫
    (relativeGlobalSectionsCompIso p t).inv.app _

lemma directImageGlobalSectionsMap_apply
    (x : (relativeGlobalSections f).obj (SheafOfModules.unit X.ringCatSheaf)) :
    directImageGlobalSectionsMap f t g p w x = g.appTop x := by
  change Y.presheaf.map (𝟙 (op ⊤)) (g.appTop x) = _
  simp

/-- The canonical morphism from pullback of the associated global-functions
module to the actual structure-module direct image. -/
def directImageSheafMap :
    (Scheme.Modules.pullback t).obj
        (tilde ((relativeGlobalSections f).obj (SheafOfModules.unit X.ringCatSheaf))) ⟶
      (Scheme.Modules.pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  ((tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction t)).homEquiv _ _).symm
    (directImageGlobalSectionsMap f t g p w)

/-- The defining global-sections adjunct of the canonical sheaf comparison. -/
lemma directImageSheafMap_homEquiv :
    (tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction t)).homEquiv _ _
      (directImageSheafMap f t g p w) = directImageGlobalSectionsMap f t g p w := by
  exact Equiv.apply_symm_apply _ _

end General

section AffineRestriction

variable {R S : CommRingCat.{u}} {T : Scheme.{u}} (t : T ⟶ Spec R)
  (j : Spec S ⟶ T) [IsOpenImmersion j] (φ : R ⟶ S)
  (w : j ≫ t = Spec.map φ)

/-- Over an affine open of an arbitrary base, actual global sections of
pushforward agree with restriction of scalars of the affine sections. -/
def affineRestrictionGlobalSectionsIso :
    Scheme.Modules.pushforward j ⋙ relativeGlobalSections t ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  relativeGlobalSectionsCompIso j t ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.pushforwardCongr w) moduleSpecΓFunctor ≪≫
      Langlands.Scheme.Modules.pushforwardΓIso φ

omit [IsOpenImmersion j] in
lemma affineRestrictionGlobalSectionsIso_hom_apply (N : (Spec S).Modules)
    (x : (relativeGlobalSections t).obj ((Scheme.Modules.pushforward j).obj N)) :
    (affineRestrictionGlobalSectionsIso t j φ w).hom.app N x = x := by
  change N.presheaf.map (𝟙 (op ⊤)) x = _
  simp

/-- Restricting the pulled-back associated module has this composite
adjunction with actual global sections. -/
def tildeRestrictionAdjunction :
    (tilde.functor R ⋙ Scheme.Modules.pullback t) ⋙ Scheme.Modules.restrictFunctor j ⊣
      Scheme.Modules.pushforward j ⋙ relativeGlobalSections t :=
  (tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction t)).comp
    (Scheme.Modules.restrictAdjunction j)

/-- The affine scalar-extension adjunction has the same right adjoint. -/
def scalarTildeRestrictionAdjunction :
    ModuleCat.extendScalars φ.hom ⋙ tilde.functor S ⊣
      Scheme.Modules.pushforward j ⋙ relativeGlobalSections t :=
  ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction).ofNatIsoRight
    (affineRestrictionGlobalSectionsIso t j φ w).symm

/-- The canonical local comparison with the associated scalar-extension
module, using uniqueness of left adjoints. -/
def tildeRestrictionIso (M : ModuleCat.{u} R) :
    ((Scheme.Modules.pullback t).obj (tilde M)).restrict j ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj M) :=
  ((tildeRestrictionAdjunction t j).leftAdjointUniq
    (scalarTildeRestrictionAdjunction t j φ w)).app M

/-- The local source comparison identifies the two adjuncts of every map. -/
lemma tildeRestrictionIso_inv_homEquiv (M : ModuleCat.{u} R) (N : (Spec S).Modules)
    (q : ((Scheme.Modules.pullback t).obj (tilde M)).restrict j ⟶ N) :
    (scalarTildeRestrictionAdjunction t j φ w).homEquiv _ _
        ((tildeRestrictionIso t j φ w M).inv ≫ q) =
      (tildeRestrictionAdjunction t j).homEquiv _ _ q := by
  rw [Adjunction.homEquiv_naturality_right]
  change (scalarTildeRestrictionAdjunction t j φ w).homEquiv _ _
      (((scalarTildeRestrictionAdjunction t j φ w).leftAdjointUniq
        (tildeRestrictionAdjunction t j)).hom.app M) ≫ _ = _
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

/-- Restriction of an adjoint map has the scalar-extension adjunct obtained
by restricting its actual global sections. -/
lemma tildeRestriction_homEquiv (M : ModuleCat.{u} R) (N : T.Modules)
    (q : (Scheme.Modules.pullback t).obj (tilde M) ⟶ N) :
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction).homEquiv _ _
        ((tildeRestrictionIso t j φ w M).inv ≫
          (Scheme.Modules.restrictFunctor j).map q) =
      (tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction t)).homEquiv _ _ q ≫
        (relativeGlobalSections t).map ((Scheme.Modules.restrictAdjunction j).unit.app N) ≫
          (affineRestrictionGlobalSectionsIso t j φ w).hom.app (N.restrict j) := by
  have h := tildeRestrictionIso_inv_homEquiv t j φ w M (N.restrict j)
    ((Scheme.Modules.restrictFunctor j).map q)
  rw [scalarTildeRestrictionAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply] at h
  erw [(Iso.comp_inv_eq ((affineRestrictionGlobalSectionsIso t j φ w).app
    (N.restrict j))).mp h]
  rw [← Category.assoc]
  congr 1
  rw [tildeRestrictionAdjunction, Adjunction.comp_homEquiv]
  change (tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction t)).homEquiv _ _
      ((Scheme.Modules.restrictAdjunction j).homEquiv _ _
        ((Scheme.Modules.restrictFunctor j).map q)) = _
  have hu : (Scheme.Modules.restrictAdjunction j).homEquiv _ _
      ((Scheme.Modules.restrictFunctor j).map q) =
        q ≫ (Scheme.Modules.restrictAdjunction j).unit.app N := by
    rw [Adjunction.homEquiv_unit]
    exact ((Scheme.Modules.restrictAdjunction j).unit.naturality q).symm
  erw [hu, Adjunction.homEquiv_naturality_right]
  rfl

/-- On generators, the local map is the restriction of the actual global
sections adjunct. -/
lemma tildeRestriction_one_tmul (M : ModuleCat.{u} R) (N : T.Modules)
    (q : (Scheme.Modules.pullback t).obj (tilde M) ⟶ N) (x : M) :
    (tilde.adjunction.homEquiv _ _
        ((tildeRestrictionIso t j φ w M).inv ≫
          (Scheme.Modules.restrictFunctor j).map q)) ((1 : S) ⊗ₜ[R,φ.hom] x) =
      ((Scheme.Modules.restrictAdjunction j).unit.app N).app ⊤
        ((tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction t)).homEquiv _ _
          q x) := by
  have h := tildeRestriction_homEquiv t j φ w M N q
  rw [Adjunction.comp_homEquiv] at h
  have hx := ConcreteCategory.congr_hom h x
  change (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _
      (tilde.adjunction.homEquiv _ _
        ((tildeRestrictionIso t j φ w M).inv ≫
          (Scheme.Modules.restrictFunctor j).map q)) x =
    (affineRestrictionGlobalSectionsIso t j φ w).hom.app (N.restrict j)
      (((Scheme.Modules.restrictAdjunction j).unit.app N).app ⊤
        ((tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction t)).homEquiv _ _
          q x)) at hx
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
    affineRestrictionGlobalSectionsIso_hom_apply] at hx
  exact hx

end AffineRestriction

section AffineChart

open Langlands.Cohomology AffineVanishing

variable {T : Scheme.{u}} (N : T.Modules) {U : T.Opens} (hU : IsAffineOpen U)

/-- Actual global sections after restriction to an affine chart are the
original module's sections over that affine open, with the same scalars. -/
def affineChartSectionsIso :
    moduleSpecΓFunctor.obj (N.restrict hU.fromSpec) ≅ N.val.obj (op U) := by
  let h := image_fromSpec_top hU
  let e := N.restrictAppIso hU.fromSpec ⊤ ≪≫
    N.presheaf.mapIso (eqToIso h.symm).op
  let l : moduleSpecΓFunctor.obj (N.restrict hU.fromSpec) →ₗ[Γ(T, U)] Γ(N, U) := {
    toFun := fun m => Cech.res h.ge ((N.restrictAppIso hU.fromSpec ⊤).hom m)
    map_add' := by intro a b; simp
    map_smul' := by
      intro r m
      rw [restrictAppIso_hom_smul, res_smul, rres_rres, rres_self]
      rfl
  }
  exact (LinearEquiv.ofBijective l (ConcreteCategory.bijective_of_isIso e.hom)).toModuleIso

/-- The chart comparison is the actual restriction along the equality of
the image open with `U`. -/
lemma affineChartSectionsIso_hom_apply (x : moduleSpecΓFunctor.obj (N.restrict hU.fromSpec)) :
    (affineChartSectionsIso N hU).hom x =
      N.presheaf.map (homOfLE (image_fromSpec_top hU).ge).op x := rfl

/-- The affine-chart comparison respects every actual sheaf morphism. -/
lemma affineChartSectionsIso_naturality {M N : T.Modules} (q : M ⟶ N) :
    moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor hU.fromSpec).map q) ≫
        (affineChartSectionsIso N hU).hom =
      (affineChartSectionsIso M hU).hom ≫ q.val.app (op U) := by
  ext x
  change N.presheaf.map _ (q.app (hU.fromSpec ''ᵁ ⊤) x) =
    q.app U (M.presheaf.map _ x)
  exact ConcreteCategory.congr_hom
    ((q.mapPresheaf.naturality (homOfLE (image_fromSpec_top hU).ge).op).symm) x

end AffineChart

section FieldBaseChange

variable {k : Type u} [Field k] {X Y T : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (t : T ⟶ Spec (CommRingCat.of k))
  (g : Y ⟶ X) (p : Y ⟶ T) (w : g ≫ f = p ≫ t)
  {U : T.Opens} (hU : IsAffineOpen U)

/-- The canonical sheaf comparison, restricted to the spectrum of an affine
open and expressed with its scalar-extension source. -/
def directImageAffineSheafMap :
    tilde ((ModuleCat.extendScalars (affineOpenFieldMap t hU).hom).obj (sections f)) ⟶
      ((Scheme.Modules.pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf)).restrict
        hU.fromSpec :=
  (tildeRestrictionIso t hU.fromSpec (affineOpenFieldMap t hU)
    (by simp [affineOpenFieldMap]) (sections f)).inv ≫
      (Scheme.Modules.restrictFunctor hU.fromSpec).map (directImageSheafMap f t g p w)

/-- The local scalar comparison on actual sections. -/
def directImageAffineModuleMap :
    (ModuleCat.extendScalars (affineOpenFieldMap t hU).hom).obj (sections f) ⟶
      directImageSections p U :=
  tilde.adjunction.homEquiv _ _ (directImageAffineSheafMap f t g p w hU) ≫
    (affineChartSectionsIso
      ((Scheme.Modules.pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf)) hU).hom

/-- The local canonical map pulls each global function back and restricts it
to the actual inverse image of the affine open. -/
lemma directImageAffineModuleMap_one_tmul (x : sections f) :
    directImageAffineModuleMap f t g p w hU
        ((1 : Γ(T, U)) ⊗ₜ[k,(affineOpenFieldMap t hU).hom] x) =
      Y.presheaf.map (homOfLE (show p ⁻¹ᵁ U ≤ ⊤ from le_top)).op (g.appTop x) := by
  change (affineChartSectionsIso _ hU).hom
    ((tilde.adjunction.homEquiv _ _ (directImageAffineSheafMap f t g p w hU))
      ((1 : Γ(T, U)) ⊗ₜ[k,(affineOpenFieldMap t hU).hom] x)) = _
  rw [directImageAffineSheafMap, tildeRestriction_one_tmul,
    directImageSheafMap_homEquiv]
  erw [directImageGlobalSectionsMap_apply f t g p w x,
    affineChartSectionsIso_hom_apply]
  change Y.presheaf.map _ (Y.presheaf.map _ (g.appTop x)) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable [IsProper f] (h : IsPullback g p f t)

/-- The existing affine section isomorphism has the same actual pullback
formula on scalar-extension generators. -/
lemma directImageAffineSectionsIso_hom_one_tmul (x : sections f) :
    (directImageAffineSectionsIso f t g p h hU).hom
        ((1 : Γ(T, U)) ⊗ₜ[k,(affineOpenFieldMap t hU).hom] x) =
      Y.presheaf.map (homOfLE (show p ⁻¹ᵁ U ≤ ⊤ from le_top)).op (g.appTop x) := by
  rw [directImageAffineSectionsIso_hom]
  change (affineRestrictSectionsIso p hU).hom
    ((baseChangeIso f (affineOpenFieldMap t hU) (affineRestrict p hU)
      ((p ⁻¹ᵁ U).ι ≫ g) (isPullback_affineOpen f t g p h hU)).hom
        ((1 : Γ(T, U)) ⊗ₜ[k,(affineOpenFieldMap t hU).hom] x)) = _
  rw [baseChangeIso_hom_one_tmul]
  change (p ⁻¹ᵁ U).topIso.hom (((p ⁻¹ᵁ U).ι ≫ g).appTop x) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Opens.ι_appTop]
  change Y.presheaf.map _ (Y.presheaf.map _ (g.appTop x)) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The canonical local section map is the previously constructed affine
base-change isomorphism. -/
lemma directImageAffineModuleMap_eq :
    directImageAffineModuleMap f t g p h.w hU =
      (directImageAffineSectionsIso f t g p h hU).hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  rw [directImageAffineModuleMap_one_tmul,
    directImageAffineSectionsIso_hom_one_tmul]

include hU in
/-- The canonical comparison is invertible on sections of each affine
open of the arbitrary base. -/
lemma isIso_directImageSheafMap_app_affine :
    IsIso ((directImageSheafMap f t g p h.w).app U) := by
  have ha : IsIso (directImageAffineModuleMap f t g p h.w hU) := by
    rw [directImageAffineModuleMap_eq f t g p hU h]
    infer_instance
  rw [directImageAffineModuleMap, isIso_comp_right_iff] at ha
  rw [Adjunction.homEquiv_unit, isIso_comp_left_iff] at ha
  have hb : IsIso ((directImageAffineSheafMap f t g p h.w hU).app ⊤) := by
    change IsIso ((forget₂ (ModuleCat Γ(T, U)) AddCommGrpCat).map
      (moduleSpecΓFunctor.map (directImageAffineSheafMap f t g p h.w hU)))
    infer_instance
  rw [directImageAffineSheafMap, Scheme.Modules.Hom.comp_app,
    isIso_comp_left_iff] at hb
  have hc : IsIso (moduleSpecΓFunctor.map
      ((Scheme.Modules.restrictFunctor hU.fromSpec).map
        (directImageSheafMap f t g p h.w))) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.restrictFunctor hU.fromSpec).map
        (directImageSheafMap f t g p h.w)).app ⊤)
  have hd := affineChartSectionsIso_naturality hU (directImageSheafMap f t g p h.w)
  have he : IsIso ((affineChartSectionsIso _ hU).hom ≫
      (directImageSheafMap f t g p h.w).val.app (op U)) := by
    rw [← hd]
    infer_instance
  rw [isIso_comp_left_iff] at he
  change IsIso ((forget₂ (ModuleCat Γ(T, U)) AddCommGrpCat).map
    ((directImageSheafMap f t g p h.w).val.app (op U)))
  infer_instance

/-- The canonical global-functions sheaf map is an isomorphism after
every base change of a proper scheme over an arbitrary field. -/
lemma isIso_directImageSheafMap : IsIso (directImageSheafMap f t g p h.w) := by
  have hs : IsIso ((SheafOfModules.toSheaf T.ringCatSheaf).map
      (directImageSheafMap f t g p h.w)) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis
      (B := fun U : T.affineOpens ↦ U.val)
      (by simpa only [Subtype.range_val] using T.isBasis_affineOpens)
    intro U
    exact isIso_directImageSheafMap_app_affine f t g p U.property h
  have hp : IsIso ((Scheme.Modules.toPresheaf T).map
      (directImageSheafMap f t g p h.w)) := by
    change IsIso ((TopCat.Sheaf.forget _ T).map
      ((SheafOfModules.toSheaf T.ringCatSheaf).map (directImageSheafMap f t g p h.w)))
    infer_instance
  exact isIso_of_reflects_iso (directImageSheafMap f t g p h.w)
    (Scheme.Modules.toPresheaf T)

/-- The actual structure-module direct image after arbitrary scheme base
change is the pullback of the associated module of actual global functions. -/
def directImageSheafIso :
    (Scheme.Modules.pullback t).obj (tilde (sections f)) ≅
      (Scheme.Modules.pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf) := by
  have := isIso_directImageSheafMap f t g p h
  exact asIso (directImageSheafMap f t g p h.w)

/-- The global isomorphism has the specified canonical map as its forward map. -/
lemma directImageSheafIso_hom :
    (directImageSheafIso f t g p h).hom = directImageSheafMap f t g p h.w := rfl

/-- Choosing a basis of actual global functions trivializes the actual
direct image globally, of rank `dim_k Gamma(X,O_X)`. -/
def directImageFreeIso :
    (Scheme.Modules.pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.free (R := T.ringCatSheaf)
        (ULift.{u} (Fin (Module.finrank k (sections f)))) := by
  let : Module.Finite k (sections f) := finite f
  let b : Module.Basis (ULift.{u} (Fin (Module.finrank k (sections f)))) k (sections f) :=
    (Module.finBasis k (sections f)).reindex Equiv.ulift.symm
  exact (directImageSheafIso f t g p h).symm ≪≫
    (Scheme.Modules.pullback t).mapIso
      ((tilde.functor (CommRingCat.of k)).mapIso b.repr.toModuleIso ≪≫ tildeFinsupp _) ≪≫
    Langlands.Scheme.Modules.freePullbackIso t _

/-- Every open's actual direct-image sections have a finite basis of the
same size, including opens of a non-quasi-compact base. -/
def directImageSectionBasis (V : T.Opens) :
    Module.Basis (ULift.{u} (Fin (Module.finrank k (sections f)))) Γ(T, V)
      (directImageSections p V) :=
  Langlands.Scheme.Modules.globalSectionBasis (directImageFreeIso f t g p h).symm V

end FieldBaseChange

end Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctions
