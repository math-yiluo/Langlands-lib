/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperations
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-!
# Compatible changes of ring sheaves and derived adjunctions

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0D6E and 07A6;
Modules on Sites, lemma-adjoint-push-pull-modules
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

private theorem isoOfAdjunct
    {A B : Type*} [Category A] [Category B] {L : A ⥤ B} {R : B ⥤ A}
    (adj : L ⊣ R) {X : A} {Y Z : B} (g : X ⟶ R.obj Y) (h : X ⟶ R.obj Z)
    (k : Y ⟶ Z) (hg : IsIso ((adj.homEquiv X Y).symm g))
    (hh : IsIso ((adj.homEquiv X Z).symm h)) (hk : g ≫ R.map k = h) : IsIso k := by
  let := hg
  let := hh
  have : IsIso ((adj.homEquiv X Y).symm g ≫ k) := by
    rw [← adj.homEquiv_naturality_right_symm, hk]
    exact hh
  exact IsIso.of_isIso_comp_left ((adj.homEquiv X Y).symm g) k

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ringUnitComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (adj : proEtaleRingModulePullback f R S c ⊣ proEtaleRingModuleDirectImage f R S c)
    (M : proEtaleRingModules Y R) :
    IsIso (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv
      ((SheafOfModules.toSheaf _).obj M)
      ((SheafOfModules.toSheaf _).obj ((proEtaleRingModulePullback f R S c).obj M))).symm
        ((SheafOfModules.toSheaf _).map (adj.unit.app M))) := by
  let A := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let B := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
  let C := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let P := SheafOfModules.toSheaf.{u + 1} A
  let Q := SheafOfModules.toSheaf.{u + 1} B
  let Q' := SheafOfModules.toSheaf.{u + 1} C
  let a := proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}
  obtain ⟨a₀, h₀⟩ := proEtaleModuleInverseImage_canonicalUnitComparison f R
  let rc := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
  let a₁ : proEtaleRingExtension f R S c ⊣
      SheafOfModules.restrictScalars.{u + 1} rc.hom :=
    proEtaleRingExtensionAdjunction f R S c
  have : (SheafOfModules.restrictScalars.{u + 1} rc.hom).IsEquivalence :=
    inferInstanceAs (proEtaleScalarEquivalence X rc).functor.IsEquivalence
  have : IsIso a₁.unit := by infer_instance
  have : IsIso (a₁.unit.app ((proEtaleModuleInverseImage f R).obj M)) := inferInstance
  let ac := a₀.comp a₁
  change proEtaleRingModulePullback f R S c ⊣ _ at ac
  let T := SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X) (S := A) (R := B)
      ⟨Functor.whiskerRight ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let er : SheafOfModules.restrictScalars rc.hom ⋙ T ≅
      proEtaleRingModuleDirectImage f R S c := by
    refine NatIso.ofComponents (fun N ↦ ?_) ?_
    · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
      exact PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by intros; rfl)
    · intro N N' h
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      rfl
  let ab := ac.ofNatIsoRight er
  let β₀ := (a.homEquiv (P.obj M)
    (Q.obj ((proEtaleModuleInverseImage f R).obj M))).symm
      (P.map (a₀.unit.app M))
  have : IsIso β₀ := h₀ M
  let k := Q.map (a₁.unit.app ((proEtaleModuleInverseImage f R).obj M))
  have : IsIso k := inferInstance
  have he : (a.homEquiv (P.obj M)
      (Q'.obj ((proEtaleRingModulePullback f R S c).obj M))).symm
        (P.map (ab.unit.app M)) = β₀ ≫ k := by
    rw [← a.homEquiv_naturality_right_symm]
    congr 1
  have hb : IsIso ((a.homEquiv (P.obj M)
      (Q'.obj ((proEtaleRingModulePullback f R S c).obj M))).symm
        (P.map (ab.unit.app M))) := by
    rw [he]
    infer_instance
  let e := ab.leftAdjointUniq adj
  have hu := Adjunction.unit_leftAdjointUniq_hom_app ab adj M
  have hh : (a.homEquiv (P.obj M)
      (Q'.obj ((proEtaleRingModulePullback f R S c).obj M))).symm
        (P.map (adj.unit.app M)) =
      (a.homEquiv (P.obj M)
        (Q'.obj ((proEtaleRingModulePullback f R S c).obj M))).symm
          (P.map (ab.unit.app M)) ≫ Q'.map (e.hom.app M) := by
    rw [← a.homEquiv_naturality_right_symm]
    congr 1
    rw [← hu, P.map_comp]
    rfl
  change IsIso ((a.homEquiv (P.obj M)
      (Q'.obj ((proEtaleRingModulePullback f R S c).obj M))).symm
        (P.map (adj.unit.app M)))
  rw [hh]
  infer_instance

/-- Restriction along a commutative ring-sheaf map on the original small site.
Source: Stacks, Modules on Sites (auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleRingRestrictScalars {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    proEtaleRingModules T S ⥤ proEtaleRingModules T R :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a)

/-- Restriction is exact and conservative before deriving.
Source: Stacks, Derived Categories, Tag 05RT
(auxiliary; not a blueprint node).
Proof: restriction leaves the underlying abelian sheaf and its kernels and sheafified
cokernels unchanged. A bijective linear sheaf map has a linear inverse: apply the map
to the proposed scalar-linearity equality for its inverse. Thus restriction reflects
isomorphisms and preserves finite limits and finite colimits. -/
theorem proEtaleRingRestrictScalars_properties {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteLimits (proEtaleRingRestrictScalars a) ∧
    PreservesFiniteColimits (proEtaleRingRestrictScalars a) ∧
    (proEtaleRingRestrictScalars a).ReflectsIsomorphisms := by
  let R₀ := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let S₀ := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let F := proEtaleRingRestrictScalars a
  have he : F ⋙ SheafOfModules.toSheaf.{u + 1} R₀ ≅ SheafOfModules.toSheaf.{u + 1} S₀ := Iso.refl _
  have : F.ReflectsIsomorphisms := by
    have : (F ⋙ SheafOfModules.toSheaf.{u + 1} R₀).ReflectsIsomorphisms :=
      reflectsIsomorphisms_of_iso he.symm
    exact reflectsIsomorphisms_of_comp F (SheafOfModules.toSheaf.{u + 1} R₀)
  have : PreservesFiniteLimits F := by
    have : PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf.{u + 1} R₀) :=
      preservesFiniteLimits_of_natIso he.symm
    exact preservesFiniteLimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{u + 1} R₀)
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u + 1} R₀) :=
    { reflects := fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  have : PreservesFiniteColimits F := by
    have : PreservesFiniteColimits (F ⋙ SheafOfModules.toSheaf.{u + 1} R₀) :=
      preservesFiniteColimits_of_natIso he.symm
    exact preservesFiniteColimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{u + 1} R₀)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Left exactness of restriction. Source: Stacks, Tag 05RT
(auxiliary; not a blueprint node). -/
theorem proEtaleRingRestrictScalars_preservesFiniteLimits {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteLimits (proEtaleRingRestrictScalars a) :=
  (proEtaleRingRestrictScalars_properties a).1

attribute [local instance] proEtaleRingRestrictScalars_preservesFiniteLimits

/-- Right exactness of restriction. Source: Stacks, Tag 05RT
(auxiliary; not a blueprint node). -/
theorem proEtaleRingRestrictScalars_preservesFiniteColimits {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteColimits (proEtaleRingRestrictScalars a) :=
  (proEtaleRingRestrictScalars_properties a).2.1

attribute [local instance] proEtaleRingRestrictScalars_preservesFiniteColimits

variable {U V : Scheme.{u}} (f : U ⟶ V)
  (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
  (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
  (aV : RV ⟶ SV) (aU : RU ⟶ SU)
  (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
  (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SV ≅ SU)
  (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aV ≫ cS.hom)

include comm in
private theorem restrictionDirectImageMap_square :
    aV ≫ proEtaleRingDirectImageMap f SV SU cS =
      proEtaleRingDirectImageMap f RV RU cR ≫
        (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map aU := by
  dsimp [proEtaleRingDirectImageMap]
  have hn := (proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.naturality aV
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  rw [Category.assoc, ← Functor.map_comp, ← comm, Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include comm in
private noncomputable def restrictionDirectImageHom (N : proEtaleRingModules U SU) :
    ((proEtaleRingModuleDirectImage f SV SU cS ⋙ proEtaleRingRestrictScalars aV).obj N) ⟶
      ((proEtaleRingRestrictScalars aU ⋙ proEtaleRingModuleDirectImage f RV RU cR).obj N) where
  val :=
    { app W := ModuleCat.ofHom
        (X := ((proEtaleRingModuleDirectImage f SV SU cS ⋙
          proEtaleRingRestrictScalars aV).obj N).val.obj W)
        (Y := ((proEtaleRingRestrictScalars aU ⋙
          proEtaleRingModuleDirectImage f RV RU cR).obj N).val.obj W)
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r n
            change (proEtaleRingDirectImageMap f SV SU cS).hom.app W
                (aV.hom.app W r) • (show N.val.obj ((proEtaleBaseChange f).op.obj W) from n) =
              aU.hom.app ((proEtaleBaseChange f).op.obj W)
                ((proEtaleRingDirectImageMap f RV RU cR).hom.app W r) •
                (show N.val.obj ((proEtaleBaseChange f).op.obj W) from n)
            congr 1
            exact congrArg (fun h ↦ h.hom.app W r)
              (restrictionDirectImageMap_square f RV SV RU SU aV aU cR cS comm) }
      naturality := by intros; ext n; rfl }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include comm in
private noncomputable def restrictionDirectImageInv (N : proEtaleRingModules U SU) :
    ((proEtaleRingRestrictScalars aU ⋙ proEtaleRingModuleDirectImage f RV RU cR).obj N) ⟶
      ((proEtaleRingModuleDirectImage f SV SU cS ⋙ proEtaleRingRestrictScalars aV).obj N) where
  val :=
    { app W := ModuleCat.ofHom
        (X := ((proEtaleRingRestrictScalars aU ⋙
          proEtaleRingModuleDirectImage f RV RU cR).obj N).val.obj W)
        (Y := ((proEtaleRingModuleDirectImage f SV SU cS ⋙
          proEtaleRingRestrictScalars aV).obj N).val.obj W)
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r n
            change aU.hom.app ((proEtaleBaseChange f).op.obj W)
                ((proEtaleRingDirectImageMap f RV RU cR).hom.app W r) •
                (show N.val.obj ((proEtaleBaseChange f).op.obj W) from n) =
              (proEtaleRingDirectImageMap f SV SU cS).hom.app W
                (aV.hom.app W r) • (show N.val.obj ((proEtaleBaseChange f).op.obj W) from n)
            congr 1
            exact congrArg (fun h ↦ h.hom.app W r)
              (restrictionDirectImageMap_square f RV SV RU SU aV aU cR cS comm).symm }
      naturality := by intros; ext n; rfl }

include comm in
/-- The underived comparison is uniquely specified by identity on every section.
Source: Stacks, Tag 0D6E (auxiliary; not a blueprint node).
Proof: both composites have sections `N(U ×_V W)`. Their actions coincide by taking
adjoints of the coefficient-square identity. Identity on those sections is linear,
commutes with restrictions and module maps, and is its own inverse. Sectionwise
faithfulness determines the natural isomorphism uniquely. -/
theorem proEtaleRingRestrictionDirectImage_existsUnique :
    ∃! e : proEtaleRingModuleDirectImage f SV SU cS ⋙ proEtaleRingRestrictScalars aV ≅
        proEtaleRingRestrictScalars aU ⋙ proEtaleRingModuleDirectImage f RV RU cR,
      ∀ (N : proEtaleRingModules U SU) (W : V.ProEtᵒᵖ)
        (n : N.val.obj ((proEtaleBaseChange f).op.obj W)),
        (e.hom.app N).val.app W n = n := by
  classical
  let e : proEtaleRingModuleDirectImage f SV SU cS ⋙ proEtaleRingRestrictScalars aV ≅
      proEtaleRingRestrictScalars aU ⋙ proEtaleRingModuleDirectImage f RV RU cR :=
    NatIso.ofComponents (fun N ↦
      { hom := restrictionDirectImageHom f RV SV RU SU aV aU cR cS comm N
        inv := restrictionDirectImageInv f RV SV RU SU aV aU cR cS comm N
        hom_inv_id := by
          apply SheafOfModules.hom_ext
          apply PresheafOfModules.hom_ext
          intro W
          ext n
          rfl
        inv_hom_id := by
          apply SheafOfModules.hom_ext
          apply PresheafOfModules.hom_ext
          intro W
          ext n
          rfl }) (by
        intros
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro W
        ext n
        rfl)
  refine ⟨e, fun _ _ _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext n
  exact he' N W n

/-- Canonical direct-image comparison, determined by the actual identity on sections.
Source: Stacks, Tag 0D6E (auxiliary; not a blueprint node). -/
noncomputable def proEtaleRingRestrictionDirectImage :
    proEtaleRingModuleDirectImage f SV SU cS ⋙ proEtaleRingRestrictScalars aV ≅
      proEtaleRingRestrictScalars aU ⋙ proEtaleRingModuleDirectImage f RV RU cR :=
  Classical.choose
    (proEtaleRingRestrictionDirectImage_existsUnique f RV SV RU SU aV aU cR cS comm)

/-- The inverse-image comparison before inversion is the mate of identity on sections.
Source: Stacks, lemma-adjoint-push-pull-modules
(auxiliary; not a blueprint node). -/
noncomputable def proEtaleRingRestrictionPullbackApp (M : proEtaleRingModules V SV) :
    (proEtaleRingModulePullback f RV RU cR).obj ((proEtaleRingRestrictScalars aV).obj M) ⟶
      (proEtaleRingRestrictScalars aU).obj ((proEtaleRingModulePullback f SV SU cS).obj M) :=
  (proEtaleRingModulePullback f RV RU cR).map
    ((proEtaleRingRestrictScalars aV).map
      ((proEtaleRingModuleAdjunction f SV SU cS).unit.app M)) ≫
  (proEtaleRingModulePullback f RV RU cR).map
    ((proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm).hom.app
      ((proEtaleRingModulePullback f SV SU cS).obj M)) ≫
  (proEtaleRingModuleAdjunction f RV RU cR).counit.app _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ringModuleMap_isIso
    (M : proEtaleRingModules V SV) (N : proEtaleRingModules U RU)
    (N' : proEtaleRingModules U SU)
    (g : (proEtaleRingRestrictScalars aV).obj M ⟶
      (proEtaleRingModuleDirectImage f RV RU cR).obj N)
    (h : M ⟶ (proEtaleRingModuleDirectImage f SV SU cS).obj N')
    (k : N ⟶ (proEtaleRingRestrictScalars aU).obj N')
    (hg : IsIso (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv
      ((SheafOfModules.toSheaf _).obj ((proEtaleRingRestrictScalars aV).obj M))
      ((SheafOfModules.toSheaf _).obj N)).symm ((SheafOfModules.toSheaf _).map g)))
    (hh : IsIso (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv
      ((SheafOfModules.toSheaf _).obj M)
      ((SheafOfModules.toSheaf _).obj N')).symm ((SheafOfModules.toSheaf _).map h)))
    (hk : g ≫ (proEtaleRingModuleDirectImage f RV RU cR).map k =
      (proEtaleRingRestrictScalars aV).map h ≫
        (proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm).hom.app N') :
    IsIso k := by
  let P := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology V)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)
  let P' := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology V)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj SV)
  let Q := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU)
  let Q' := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj SU)
  let a := proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}
  have he : P.map
      ((proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm).hom.app N') =
      𝟙 _ := by
    ext W n
    exact (Classical.choose_spec
      (proEtaleRingRestrictionDirectImage_existsUnique
        f RV SV RU SU aV aU cR cS comm)).1 _ W n
  have htP := congrArg P.map hk
  simp only [P.map_comp, he] at htP
  erw [Category.comp_id] at htP
  have htP' : P.map g ≫ (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map
      (Q.map k) = P'.map h := by
    ext W n
    exact ConcreteCategory.congr_hom (congrArg (fun z ↦ z.hom.app W) htP) n
  have : IsIso (Q.map k) := isoOfAdjunct a (X := P'.obj M) (Y := Q.obj N) (Z := Q'.obj N')
    (P.map g) (P'.map h) (Q.map k) hg hh htP'
  exact isIso_of_reflects_iso k Q

attribute [local irreducible] proEtaleRingRestrictionPullbackApp
  proEtaleRingModulePullback proEtaleRingModuleAdjunction

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The specified mate is natural and invertible.
Source: Stacks, Modules on Sites, lemma-adjoint-push-pull-modules
(auxiliary; not a blueprint node).
Proof: unit and counit naturality and naturality of the sectionwise identity give
naturality. Under the tensor-unit normalized adjunctions this mate is identity on
underlying inverse-image abelian sheaves. Its two scalar actions are equal because
`cS.inv aU = inverseImage(aV) cR.inv`, the coefficient-square equation. Hence it is
an isomorphism. No flatness of the coefficient-change maps is used. -/
theorem proEtaleRingRestrictionPullbackApp_properties :
    (∀ (M N : proEtaleRingModules V SV) (h : M ⟶ N),
      (proEtaleRingModulePullback f RV RU cR).map
          ((proEtaleRingRestrictScalars aV).map h) ≫
        proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm N =
      proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm M ≫
        (proEtaleRingRestrictScalars aU).map
          ((proEtaleRingModulePullback f SV SU cS).map h)) ∧
    ∀ M : proEtaleRingModules V SV,
      IsIso (proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm M) := by
  let adjS := proEtaleRingModuleAdjunction f SV SU cS
  let adjR := proEtaleRingModuleAdjunction f RV RU cR
  let d := proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm
  let s := (mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.hom)
  have hs (M : proEtaleRingModules V SV) :
      s.app M = proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm M := by
    simp only [s, mateEquiv_symm_apply, TwoSquare.mk, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
      Category.id_comp]
    dsimp only [Functor.comp_map]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    unfold proEtaleRingRestrictionPullbackApp
    rfl
  refine ⟨?_, ?_⟩
  · intro M N h
    simpa only [Functor.comp_map, hs] using s.naturality h
  · intro M
    have happ : proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm M =
        (adjR.homEquiv _ _).symm
          ((proEtaleRingRestrictScalars aV).map (adjS.unit.app M) ≫
            d.hom.app ((proEtaleRingModulePullback f SV SU cS).obj M)) := by
      simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
      unfold proEtaleRingRestrictionPullbackApp
      rfl
    have ht := (adjR.homEquiv _ _).apply_symm_apply
      ((proEtaleRingRestrictScalars aV).map (adjS.unit.app M) ≫
        d.hom.app ((proEtaleRingModulePullback f SV SU cS).obj M))
    rw [← happ, Adjunction.homEquiv_unit] at ht
    exact ringModuleMap_isIso f RV SV RU SU aV aU cR cS comm M
      ((proEtaleRingModulePullback f RV RU cR).obj ((proEtaleRingRestrictScalars aV).obj M))
      ((proEtaleRingModulePullback f SV SU cS).obj M)
      (adjR.unit.app ((proEtaleRingRestrictScalars aV).obj M)) (adjS.unit.app M)
      (proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm M)
      (ringUnitComparison f RV RU cR adjR ((proEtaleRingRestrictScalars aV).obj M))
      (ringUnitComparison f SV SU cS adjS M) ht

/-- The canonical ordinary inverse-image comparison, with its direction reversed.
Source: Stacks, lemma-adjoint-push-pull-modules
(auxiliary; not a blueprint node). -/
noncomputable def proEtaleRingRestrictionPullbackInv :
    proEtaleRingRestrictScalars aV ⋙ proEtaleRingModulePullback f RV RU cR ⟶
      proEtaleRingModulePullback f SV SU cS ⋙ proEtaleRingRestrictScalars aU where
  app := proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm
  naturality := (proEtaleRingRestrictionPullbackApp_properties
    f RV SV RU SU aV aU cR cS comm).1

/-- The ordinary comparison is invertible. Source: Stacks, Modules on Sites
(auxiliary; not a blueprint node).
Proof: each component is invertible by the identity-on-inverse-image calculation
in proEtaleRingRestrictionPullbackApp_properties; naturality gives the inverse. -/
theorem proEtaleRingRestrictionPullbackInv_isIso :
    IsIso (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm) := by
  have (M : proEtaleRingModules V SV) :
      IsIso ((proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm).app M) :=
    (proEtaleRingRestrictionPullbackApp_properties f RV SV RU SU aV aU cR cS comm).2 M
  exact NatIso.isIso_of_isIso_app _

attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso

end AlgebraicGeometry.Scheme
