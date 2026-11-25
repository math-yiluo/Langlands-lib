/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-! # Coherence of the derived unit and Leray comparison -/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

set_option backward.isDefEq.respectTransparency.types false in
private lemma identity_fac (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology A ⥤
      Sheaf X.smallEtaleTopology A)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 _) (K : HomotopyCategory
      (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _).hom.app
        (DerivedCategory.Qh.obj K) =
      F.mapDerivedCategoryFactorsh.hom.app K ≫ DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) := by
  have h := NatTrans.congr_app
    (congrArg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh
      (Sheaf X.smallEtaleTopology A))) K
  simp only [Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app,
    Functor.mapHomotopyCategoryIdIso_hom_app_eq_id] at h
  dsimp at h
  simp only [Category.comp_id] at h
  erw [DerivedCategory.Qh.map_id] at h
  simp only [Category.comp_id] at h
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  erw [h, Functor.mapDerivedCategoryNatIso_fach]

private noncomputable def lowerIdentity (X : Scheme.{u}) :
    (lowerStar A (𝟙 X)).rightDerivedFunctor ≅
      𝟭 (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  (lowerStar A (𝟙 X)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso (lowerStarId A X) ≪≫
      Functor.mapDerivedCategoryIdIso _

private lemma lowerIdentity_fac (X : Scheme.{u}) (K : HomotopyCategory
    (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    (lowerStar A (𝟙 X)).rightDerivedFunctorUnit.app K ≫
        (lowerIdentity (A := A) X).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory (lowerStarId A X).hom
          (.up ℤ)).app K) := by
  dsimp only [lowerIdentity, Iso.trans_hom, NatTrans.comp_app]
  rw [← Category.assoc]
  have h := NatTrans.congr_app
    (lowerStar A (𝟙 X)).rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  dsimp only [Functor.whiskerLeft_app, NatTrans.comp_app] at h
  rw [h]
  rw [← NatTrans.comp_app, ← Iso.trans_hom, identity_fac, Iso.inv_hom_id_app_assoc]

private lemma homotopy_unit (X : Scheme.{u}) (H : HomotopyCategory
    (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    ((upperStarLowerStarAdjunction A (𝟙 X)).mapHomotopyCategory
        (.up ℤ)).unit.app H ≫
      ((lowerStar A (𝟙 X)).mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (upperStarId A X).hom
          (.up ℤ)).app H) =
      (NatTrans.mapHomotopyCategory (lowerStarId A X).inv
        (.up ℤ)).app H := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  have hc : ((upperStarLowerStarAdjunction A (𝟙 X)
        ).mapHomologicalComplex (.up ℤ)).unit.app K ≫
      ((lowerStar A (𝟙 X)).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (upperStarId A X).hom
          (.up ℤ)).app K) =
      (NatTrans.mapHomologicalComplex (lowerStarId A X).inv
        (.up ℤ)).app K := by
    ext n : 1
    exact upperStarId_hom_app_unit_app A X (K.X n)
  have h := (HomotopyCategory.quotient _ (.up ℤ)).congr_map hc
  simp only [Functor.map_comp] at h
  exact h

private lemma derived_unit_identity (X : Scheme.{u}) :
    (mapDerivedUpperStarLowerStarAdjunction A (𝟙 X)).unit ≫
        Functor.whiskerRight
          (Functor.mapDerivedCategoryNatIso (upperStarId A X) ≪≫
            Functor.mapDerivedCategoryIdIso _).hom
          (lowerStar A (𝟙 X)).rightDerivedFunctor =
      (lowerIdentity (A := A) X).inv := by
  rw [← cancel_epi (lowerIdentity (A := A) X).hom, Iso.hom_inv_id]
  refine Functor.rightDerived_ext
    (lowerStar A (𝟙 X)).rightDerivedFunctor
    (lowerStar A (𝟙 X)).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _ ?_
  ext H : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app]
  have hunit := (upperStarLowerStarAdjunction A (𝟙 X)
    ).mapHomotopyCategory (.up ℤ) |>.derivedη_fac_app
      (HomotopyCategory.quasiIso _ (.up ℤ))
      (upperStar A (𝟙 X)).mapDerivedCategoryFactorsh.hom
      (lowerStar A (𝟙 X)).rightDerivedFunctorUnit H
  have hnat := (lowerStar A (𝟙 X)).rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory (upperStarId A X).hom
      (.up ℤ)).app H)
  dsimp only [Functor.comp_map] at hnat
  have hcomb : (NatTrans.mapHomotopyCategory (lowerStarId A X).hom
        (.up ℤ)).app H ≫
      ((upperStarLowerStarAdjunction A (𝟙 X)).mapHomotopyCategory
        (.up ℤ)).unit.app H ≫
      ((lowerStar A (𝟙 X)).mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (upperStarId A X).hom
          (.up ℤ)).app H) = 𝟙 _ := by
    rw [homotopy_unit, ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp,
      Iso.hom_inv_id, NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
  have hQ := congrArg DerivedCategory.Qh.map hcomb
  simp only [Functor.map_comp] at hQ
  erw [DerivedCategory.Qh.map_id] at hQ
  rw [← Category.assoc, lowerIdentity_fac, identity_fac, Functor.map_comp]
  erw [reassoc_of% hunit]
  erw [← hnat, reassoc_of% hQ]
  exact (Category.comp_id _).symm

private lemma lowerIdentity_inv_fac (X : Scheme.{u}) (H : HomotopyCategory
    (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    (lowerIdentity (A := A) X).inv.app (DerivedCategory.Qh.obj H) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (lowerStarId A X).inv
            (.up ℤ)).app H) ≫
        (lowerStar A (𝟙 X)).rightDerivedFunctorUnit.app H := by
  rw [← cancel_mono ((lowerIdentity (A := A) X).hom.app (DerivedCategory.Qh.obj H)),
    Iso.inv_hom_id_app, Category.assoc, lowerIdentity_fac, ← DerivedCategory.Qh.map_comp,
    ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
    NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
  exact ((DerivedCategory.Qh (C :=
    Sheaf X.smallEtaleTopology A)).map_id _).symm

private lemma underived_leray_identity (X : Scheme.{u}) :
    Functor.whiskerRight (lowerStarId A X).inv
        (Sheaf.Γ X.smallEtaleTopology A) ≫
      (lowerStarCompGlobalSectionsIso A (𝟙 X)).hom =
    𝟙 (Sheaf.Γ X.smallEtaleTopology A) := by
  ext F : 2
  dsimp only [lowerStarCompGlobalSectionsIso, Functor.isoWhiskerLeft_hom,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.id_app]
  rw [reassoc_of% (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
    A terminalIsTerminal).hom.naturality
      ((lowerStarId A X).inv.app F)]
  have ht : ((sheafSections X.smallEtaleTopology A).obj
        (Opposite.op (⊤_ X.Etale))).map
          ((lowerStarId A X).inv.app F) ≫
      (lowerStarCompSheafSectionsTerminalIso A (𝟙 X)).hom.app F =
        𝟙 _ := by
    dsimp [lowerStarId, GrothendieckTopology.lowerStarId,
      Functor.sheafPushforwardContinuousId', Functor.sheafPushforwardContinuousIso,
      Functor.sheafPushforwardContinuousNatTrans, Functor.sheafPushforwardContinuousId,
      lowerStarCompSheafSectionsTerminalIso]
    have hh : (PreservesTerminal.iso (Scheme.Hom.Etale (𝟙 X))).inv ≫
        (MorphismProperty.Over.pullbackId @Etale ⊤ X).hom.app (⊤_ X.Etale) = 𝟙 _ :=
      terminalIsTerminal.hom_ext _ _
    erw [Category.id_comp, ← F.obj.map_comp, ← op_comp, hh]
    exact F.obj.map_id _
  rw [reassoc_of% ht, Iso.hom_inv_id_app]

private lemma leray_fac (X : Scheme.{u}) :
    Functor.rightDerivedFunctorCompUnit
        (lowerStar A (𝟙 X))
        (Sheaf.Γ X.smallEtaleTopology A) ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          A (𝟙 X)).hom =
    Functor.whiskerRight
        (NatTrans.mapHomotopyCategory
          (lowerStarCompGlobalSectionsIso A (𝟙 X)).hom (.up ℤ))
        DerivedCategory.Qh ≫
      (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorUnit := by
  let F := lowerStar A (𝟙 X)
  let G := Sheaf.Γ X.smallEtaleTopology A
  have hcomp : (F ⋙ G).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso F G).hom =
      Functor.rightDerivedFunctorCompUnit F G := by
    simp [Functor.rightDerivedFunctorCompIso]
  rw [← hcomp, Category.assoc, ← Functor.whiskerLeft_comp]
  simp only [rightDerivedLowerStarCompRightDerivedGlobalSectionsIso,
    Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom]
  dsimp only [F, G]
  rw [Iso.hom_inv_id_assoc]
  exact Functor.rightDerivedNatTrans_fac _ _ _ _
    (HomotopyCategory.quasiIso
      (Sheaf X.smallEtaleTopology A) (.up ℤ)) _

private lemma derived_leray_identity (X : Scheme.{u}) :
    Functor.whiskerRight (lowerIdentity (A := A) X).inv
        (rightDerivedGlobalSections A X) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        A (𝟙 X)).hom =
    𝟙 (rightDerivedGlobalSections A X) := by
  let F := lowerStar A (𝟙 X)
  let G := Sheaf.Γ X.smallEtaleTopology A
  refine Functor.rightDerived_ext G.rightDerivedFunctor G.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _ ?_
  ext H : 2
  have hnat := G.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory (lowerStarId A X).inv
      (.up ℤ)).app H)
  have hfac := NatTrans.congr_app (leray_fac (A := A) X) H
  have hinv : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app H =
      𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) H
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app, Functor.comp_map] at hnat hfac ⊢
  dsimp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app] at hfac
  dsimp only [F, G] at hinv
  erw [hinv, DerivedCategory.Qh.map_id] at hfac
  dsimp at hfac
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hfac
  have hcomp : (G.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (lowerStarId A X).inv
          (.up ℤ)).app H) ≫
      (NatTrans.mapHomotopyCategory
        (lowerStarCompGlobalSectionsIso A (𝟙 X)).hom (.up ℤ)).app H =
      𝟙 ((G.mapHomotopyCategory (.up ℤ)).obj H) := by
    change (NatTrans.mapHomotopyCategory
      (Functor.whiskerRight (lowerStarId A X).inv G) (.up ℤ)).app H ≫
        (NatTrans.mapHomotopyCategory
          (lowerStarCompGlobalSectionsIso A (𝟙 X)).hom (.up ℤ)).app H = _
    rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp,
      underived_leray_identity]
    erw [NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
    rfl
  have hQ := congrArg DerivedCategory.Qh.map hcomp
  simp only [Functor.map_comp] at hQ
  erw [DerivedCategory.Qh.map_id] at hQ
  rw [lowerIdentity_inv_fac, Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hnat, hfac, reassoc_of% hQ]
  exact (Category.comp_id _).symm

/-- The derived unit followed by Leray and the derived inverse-image identity is
identity. Source: Stacks Project, Tags 015M and 03CB.
(blueprint: lem-weil-pbc-derived-unit-leray-id).

Proof: Write U for D((id_X)^*), R for R((id_X)_*), G for RGamma_X, and E:U≅id for
mapDerivedCategoryNatIso(upperStarId) followed by mapDerivedCategoryIdIso. The conjugate
identity isomorphism of R is obtained by right deriving lowerStarId. The unit equation is
eta_id,K followed by R(E_K) equal to the inverse direct-image identity comparison at K. This
follows by the underived unit equation, the derived adjunction unit characterization, and
uniqueness of transformations of right derived functors extending it.

The underived identification (id_X)_* followed by Gamma_X ≅ Gamma_X evaluates sheaves at the
terminal object and hence equals Gamma_X applied to lowerStarId. Consequently the Leray
comparison for id_X is G applied to the derived direct-image identity comparison: both
comparisons satisfy the same equation with the derived global-sections unit. Uniqueness of right
derived comparisons identifies them.

Naturality of the Leray comparison at E_K rewrites G(eta_id,K); lambda_id,U(K); G(E_K) as
G(eta_id,K); G(R(E_K)); lambda_id,K. Substitute the unit equation from step 1 and the
identification from step 2. The inverse and forward direct-image identity comparisons cancel,
and G preserves identity. The equation holds for every derived object, since all transformations
in this argument are on the unbounded derived category computed using K-injectives; no
boundedness of K is used. -/
theorem derivedUnitLeray_id (X : Scheme.{u})
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (rightDerivedGlobalSections A X).map
      ((mapDerivedUpperStarLowerStarAdjunction A (𝟙 X)).unit.app K) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A (𝟙 X)).hom.app
      ((upperStar A (𝟙 X)).mapDerivedCategory.obj K) ≫
    (rightDerivedGlobalSections A X).map
      ((Functor.mapDerivedCategoryNatIso (upperStarId A X) ≪≫
        Functor.mapDerivedCategoryIdIso
          (Sheaf X.smallEtaleTopology A)).hom.app K) = 𝟙 _ := by
  let E := Functor.mapDerivedCategoryNatIso (upperStarId A X) ≪≫
    Functor.mapDerivedCategoryIdIso
      (Sheaf X.smallEtaleTopology A)
  have hn := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
    A (𝟙 X)).hom.naturality (E.hom.app K)
  have hu := NatTrans.congr_app (derived_unit_identity (A := A) X) K
  have hl := NatTrans.congr_app (derived_leray_identity (A := A) X) K
  dsimp only [E, Functor.comp_map, Functor.id_map] at hn
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hu hl
  rw [← hn, ← Functor.map_comp_assoc, hu]
  exact hl

end AlgebraicGeometry.Etale
