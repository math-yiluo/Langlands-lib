/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Transport of the sections unit along the canonical affine isomorphism -/

@[expose] public section

set_option autoImplicit false
universe u w wA
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unit_iso_iff_resolution
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] {K I : CochainComplex A ℤ}
    (s : K ⟶ I) [QuasiIso s] [I.IsKInjective] :
    IsIso (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K)) ↔
      IsIso (DerivedCategory.Qh.map
        ((F.mapHomotopyCategory (.up ℤ)).map ((HomotopyCategory.quotient _ _).map s))) := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  have hs : IsIso (DerivedCategory.Qh.map (q.map s)) := by
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso A) s).mpr inferInstance
  have hi : IsIso (F.rightDerivedFunctorUnit.app (q.obj I)) := inferInstance
  have hn := F.rightDerivedFunctorUnit.naturality (q.map s)
  dsimp only [Functor.comp_map] at hn
  constructor
  · intro hk
    have : IsIso (DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map (q.map s)) ≫
        F.rightDerivedFunctorUnit.app (q.obj I)) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (F.rightDerivedFunctorUnit.app (q.obj I))
  · intro hm
    have : IsIso (F.rightDerivedFunctorUnit.app (q.obj K) ≫
        F.rightDerivedFunctor.map (DerivedCategory.Qh.map (q.map s))) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (F.rightDerivedFunctor.map (DerivedCategory.Qh.map (q.map s)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def affineRestrictionEquivalence (S : Scheme.{u}) [IsAffine S] :
    (Spec Γ(S, ⊤)).Modules ≌ S.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor S.toSpecΓ)
    (Scheme.Modules.restrictFunctor (inv S.toSpecΓ))
    ((Scheme.Modules.restrictFunctorComp (inv S.toSpecΓ) S.toSpecΓ).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (IsIso.inv_hom_id S.toSpecΓ) ≪≫
      Scheme.Modules.restrictFunctorId).symm
    ((Scheme.Modules.restrictFunctorComp S.toSpecΓ (inv S.toSpecΓ)).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (IsIso.hom_inv_id S.toSpecΓ) ≪≫
      Scheme.Modules.restrictFunctorId)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def affineSectionsIso (S : Scheme.{u}) [IsAffine S] :
    Scheme.Modules.restrictFunctor S.toSpecΓ ⋙
        RingedSpace.globalSectionsFunctor S.toRingedSpace ≅
      RingedSpace.globalSectionsFunctor (Spec Γ(S, ⊤)).toRingedSpace ⋙
        ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(S, ⊤)).inv.hom := by
  let e : S.Modules ≌ (Spec Γ(S, ⊤)).Modules :=
    CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward S.toSpecΓ)
      (Scheme.Modules.pushforward (inv S.toSpecΓ))
      (Scheme.Modules.pushforwardComp S.toSpecΓ (inv S.toSpecΓ) ≪≫
        Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id _) ≪≫
        Scheme.Modules.pushforwardId S).symm
      (Scheme.Modules.pushforwardComp (inv S.toSpecΓ) S.toSpecΓ ≪≫
        Scheme.Modules.pushforwardCongr (IsIso.inv_hom_id _) ≪≫
        Scheme.Modules.pushforwardId _)
  let t := (Scheme.Modules.restrictAdjunction S.toSpecΓ).leftAdjointUniq e.symm.toAdjunction
  refine Functor.isoWhiskerRight t _ ≪≫ ?_
  refine NatIso.ofComponents (fun M ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
  · intro r
    ext x
    change (Scheme.ΓSpecIso Γ(S, ⊤)).inv.hom r • (show Γ(M, ⊤) from x) =
      (inv S.toSpecΓ).appTop.hom r • (show Γ(M, ⊤) from x)
    simp [Scheme.toSpecΓ_appTop]
  · intro M N f
    ext x
    rfl

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport invertibility of the sections comparison across the canonical affine
isomorphism, for an arbitrary complex of module sheaves on its spectrum.
Source: Stacks Project, Tag 06Z0, identification of derived sections; the transport
argument is given below.
(blueprint: new-affine-sections-unit-transport)

Proof: Put X = Spec Γ(S, top), E = restriction along S.toSpecΓ, and
G = sections on X followed by scalar restriction along (ΓSpecIso Γ(S, top)).inv.
Since S is affine, S.toSpecΓ is an isomorphism. Restriction along its inverse is
inverse to E: restrictFunctorComp, restrictFunctorCongr and restrictFunctorId
give both composites. Hence E is an exact equivalence and preserves K-injective
complexes. Evaluation of restrictAppIso at the top open, whose image is top,
gives E followed by sections on S naturally isomorphic to G. The scalar relation
is S.toSpecΓ.appTop = (ΓSpecIso Γ(S, top)).hom, so its inverse is precisely the
scalar restriction in G, not the hom in the other direction.
Choose a K-injective resolution i : C -> I. Its image E(i) is a K-injective
resolution of E(C). In these resolution models the two right-derived units are
the localized maps G(i) and Γ_S(E(i)), respectively. The preceding natural
isomorphism identifies these maps up to invertible endpoint maps. Therefore
invertibility of the first implies invertibility of the second. Uniqueness of
right-derived functors, compatible with their units, transfers this conclusion
to the independently chosen derived categories in the statement. Neither
boundedness nor quasi-coherence is needed. For the zero ring, zero complex,
and identity affine isomorphism the same equivalence and resolution argument
applies without a nonzero-object assumption. -/
theorem affineSectionsUnit_transport (S : Scheme.{u}) [IsAffine S]
    [(Scheme.Modules.restrictFunctor S.toSpecΓ).Additive]
    (C : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec Γ(S, ⊤)).toRingedSpace)) ℤ)
    (h : IsIso ((RingedSpace.globalSectionsFunctor (Spec Γ(S, ⊤)).toRingedSpace ⋙
      ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(S, ⊤)).inv.hom).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj C))) :
    IsIso ((RingedSpace.globalSectionsFunctor S.toRingedSpace).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((Scheme.Modules.restrictFunctor S.toSpecΓ).mapHomologicalComplex (.up ℤ)).obj C))) :=
  by
    let E := Scheme.Modules.restrictFunctor S.toSpecΓ
    let F := RingedSpace.globalSectionsFunctor S.toRingedSpace
    let G := RingedSpace.globalSectionsFunctor (Spec Γ(S, ⊤)).toRingedSpace ⋙
      ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(S, ⊤)).inv.hom
    have : G.Additive := ⟨by intros; rfl⟩
    have : (RingedSpace.globalSectionsFunctor (Spec Γ(S, ⊤)).toRingedSpace ⋙
        ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(S, ⊤)).inv.hom).Additive :=
      inferInstanceAs G.Additive
    have : E.Additive := inferInstanceAs
      ((Scheme.Modules.restrictFunctor S.toSpecΓ).Additive)
    have : F.Additive := RingedSpace.globalSectionsFunctor_additive _
    have : (Scheme.Modules.restrictFunctor S.toSpecΓ ⋙
        RingedSpace.globalSectionsFunctor S.toRingedSpace).Additive := inferInstance
    have : E.IsEquivalence := (affineRestrictionEquivalence S).isEquivalence_functor
    obtain ⟨I, _, s, _, _⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
    have hg := (unit_iso_iff_resolution G s).mp h
    let q := HomotopyCategory.quotient (Spec Γ(S, ⊤)).Modules (.up ℤ)
    let t₀ : (E ⋙ F).mapHomotopyCategory (.up ℤ) ≅ G.mapHomotopyCategory (.up ℤ) :=
      { hom := (affineSectionsIso S).hom.mapHomotopyCategory (.up ℤ)
        inv := (affineSectionsIso S).inv.mapHomotopyCategory (.up ℤ)
        hom_inv_id := by
          rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
            NatTrans.mapHomotopyCategory_id]
        inv_hom_id := by
          rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
            NatTrans.mapHomotopyCategory_id] }
    let t := Functor.isoWhiskerRight t₀ DerivedCategory.Qh
    have hc : IsIso (DerivedCategory.Qh.map
        (((E ⋙ F).mapHomotopyCategory (.up ℤ)).map (q.map s))) :=
      (NatIso.isIso_map_iff t (q.map s)).mpr hg
    let a := Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ F)) (.up ℤ)) DerivedCategory.Qh
    have he : IsIso (DerivedCategory.Qh.map
        ((F.mapHomotopyCategory (.up ℤ)).map
          ((E.mapHomotopyCategory (.up ℤ)).map (q.map s)))) :=
      (NatIso.isIso_map_iff a (q.map s)).mpr hc
    exact (unit_iso_iff_resolution F
      ((E.mapHomologicalComplex (.up ℤ)).map s)).mpr he

end AlgebraicGeometry
