/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement

/-! # Finite normalized scalar restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A B : Type u) [CommRing A] [CommRing B]
  [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]

private theorem canonicalAbelianMap_scalar_natural
    (a : A →+* B) (ρ : coefficient A ⟶ coefficient B)
    (hρ : pointConstants A ≫ ρ.hom =
      (Functor.const Profinite.{u}ᵒᵖ).map
        (AddCommGrpCat.ofHom a.ulift.{u + 1, u + 1}.toAddMonoidHom) ≫ pointConstants B)
    (X : Scheme.{u}) :
    canonicalAbelianMap A X ≫ (upperStarFromPoint X).map ρ =
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom a.ulift.{u + 1, u + 1}.toAddMonoidHom) ≫ canonicalAbelianMap B X := by
  let J := coherentTopology Profinite.{u}
  let cA := ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ (coefficient A)).symm
    (pointConstants A)
  let cB := ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ (coefficient B)).symm
    (pointConstants B)
  let f := AddCommGrpCat.ofHom a.ulift.{u + 1, u + 1}.toAddMonoidHom
  have h : cA ≫ ρ = (constantSheaf J Ab.{u + 1}).map f ≫ cB := by
    apply ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ (coefficient B)).injective
    change toSheafify J _ ≫ (cA ≫ ρ).hom =
      toSheafify J _ ≫ ((constantSheaf J Ab.{u + 1}).map f ≫ cB).hom
    change toSheafify J _ ≫ (cA.hom ≫ ρ.hom) =
      toSheafify J _ ≫ (((constantSheaf J Ab.{u + 1}).map f).hom ≫ cB.hom)
    rw [← Category.assoc]
    have hA : toSheafify J _ ≫ cA.hom = pointConstants A :=
      ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ (coefficient A)).apply_symm_apply _
    rw [hA, hρ]
    have hB : toSheafify J _ ≫ cB.hom = pointConstants B :=
      ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ (coefficient B)).apply_symm_apply _
    rw [← hB, ← Category.assoc]
    simpa only [Category.assoc, constantSheaf, Functor.comp_map, sheafifyMap] using
      congrArg (fun k ↦ k ≫ cB.hom)
      (toSheafify_naturality J
        ((Functor.const Profinite.{u}ᵒᵖ).map f))
  change (constantSchemeIso X).hom.app _ ≫ (upperStarFromPoint X).map cA ≫
    (upperStarFromPoint X).map ρ = _
  rw [← Functor.map_comp, h, Functor.map_comp, ← Category.assoc]
  change _ = (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map f ≫
    ((constantSchemeIso X).hom.app _ ≫ (upperStarFromPoint X).map cB)
  simpa only [Category.assoc, Functor.comp_map] using
    congrArg (fun t ↦ t ≫ (upperStarFromPoint X).map cB)
      ((constantSchemeIso X).hom.naturality f).symm

private theorem normalized_scalar_square
    (a : A →+* B) (ρ : coefficient A ⟶ coefficient B) [IsMonHom ρ]
    (hρ : pointConstants A ≫ ρ.hom =
      (Functor.const Profinite.{u}ᵒᵖ).map
        (AddCommGrpCat.ofHom a.ulift.{u + 1, u + 1}.toAddMonoidHom) ≫ pointConstants B)
    (X : Scheme.{u}) (eA : Encoding A X) (eB : Encoding B X) :
    eA.ringIso.hom ≫ CondensedRing.sectionRingMap X ((upperStarFromPoint X).map ρ) =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom a.ulift.{u + 1, u + 1}) ≫ eB.ringIso.hom := by
  let J := Scheme.ProEt.topology X
  apply ((sheafificationAdjunction J CommRingCat.{u + 1}).homEquiv _ _).injective
  change toSheafify J _ ≫
      (eA.ringIso.hom ≫ CondensedRing.sectionRingMap X ((upperStarFromPoint X).map ρ)).hom =
    toSheafify J _ ≫
      ((constantSheaf J CommRingCat.{u + 1}).map
        (CommRingCat.ofHom a.ulift.{u + 1, u + 1}) ≫ eB.ringIso.hom).hom
  ext U r
  change ((upperStarFromPoint X).map ρ).hom.app U
      (eA.ringIso.hom.hom.app U ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} A)))).app U r)) = _
  rw [eA.normalization]
  have hn := ConcreteCategory.congr_hom
    (congr_app (congrArg (fun k ↦ k.hom)
      (canonicalAbelianMap_scalar_natural A B a ρ hρ X).symm) U)
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)))).app U r)
  have hu := ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality J
      ((Functor.const X.ProEtᵒᵖ).map
        (AddCommGrpCat.ofHom a.ulift.{u + 1, u + 1}.toAddMonoidHom))) U) r
  have hr := ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality J
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))) U) r
  simp only [NatTrans.comp_app, CategoryTheory.comp_apply,
    ObjectProperty.FullSubcategory.comp_hom] at hn hu hr
  change (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} B)))).app U
      (a.ulift.{u + 1, u + 1} r) =
    (((constantSheaf J CommRingCat.{u + 1}).map
      (CommRingCat.ofHom a.ulift.{u + 1, u + 1})).hom.app U)
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} A)))).app U r) at hr
  change _ = eB.ringIso.hom.hom.app U
    (((constantSheaf J CommRingCat.{u + 1}).map
      (CommRingCat.ofHom a.ulift.{u + 1, u + 1})).hom.app U
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} A)))).app U r))
  rw [← hr, eB.normalization]
  exact hn.symm.trans (congrArg ((canonicalAbelianMap B X).hom.app U) hu.symm)

private def scalarRestrictionSquare
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S T U : Sheaf J RingCat.{u + 1}}
    (q : R ⟶ S) (t : T ⟶ R) (c : U ⟶ S) (π : T ⟶ U)
    (h : t ≫ q = π ≫ c) :
    SheafOfModules.restrictScalars q ⋙ SheafOfModules.restrictScalars t ≅
      SheafOfModules.restrictScalars c ⋙ SheafOfModules.restrictScalars π := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
    · refine ModuleCat.isoMk (Iso.refl _) ?_
      intro r
      ext m
      have hh := congrArg (fun f : T ⟶ S ↦ f.hom.app V r) h
      let L := M.val.obj V
      change (c.hom.app V (π.hom.app V r)) • (show L from m) =
        (q.hom.app V (t.hom.app V r)) • (show L from m)
      exact congrArg (fun z : S.obj.obj V ↦ z • (show L from m)) hh.symm
    · intro V W f
      ext x
      rfl
  · intro M N f
    ext V x
    rfl

/-- Normalized finite coefficient encodings carry scalar restriction to ordinary
restriction along the same constant-ring map.
Source: the finite coefficient filtration in integral-finite-levels, first paragraph.
(blueprint: lem-pe-finite-normalized-scalar-restriction).

Proof: the sheafification adjunction transports the specified equality on constant
sections to the scheme inverse image. Test the coefficient square after the constant
presheaf unit and use both encoding normalizations. Reconstruct the internal scalar
restriction as sectionwise restriction; the square identifies the two composite
scalar actions. The identity on sections supplies a natural linear isomorphism. -/
theorem finite_normalized_scalar_restriction
    (a : A →+* B) (ρ : coefficient A ⟶ coefficient B) [IsMonHom ρ]
    (hρ : pointConstants A ≫ ρ.hom =
      (Functor.const Profinite.{u}ᵒᵖ).map
        (AddCommGrpCat.ofHom a.ulift.{u + 1, u + 1}.toAddMonoidHom) ≫ pointConstants B)
    (X : Scheme.{u}) (eA : Encoding A X) (eB : Encoding B X) :
    Nonempty (Mod.comap ((upperStarFromPoint X).map ρ) ⋙ eA.ordinary.functor ≅
      eB.ordinary.functor ⋙ Scheme.proEtaleRingRestrictScalars
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))) := by
  rw [eA.ordinary_functor, eB.ordinary_functor]
  let J := Scheme.ProEt.topology X
  let F := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let φ := (upperStarFromPoint X).map ρ
  let q := F.map (CondensedRing.sectionRingMap X φ)
  let t := F.map eA.ringIso.hom
  let c := F.map eB.ringIso.hom
  let π := F.map ((constantSheaf J CommRingCat.{u + 1}).map
    (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))
  have hs : t ≫ q = π ≫ c := by
    exact (F.map_comp _ _).symm.trans
      ((congrArg F.map (normalized_scalar_square A B a ρ hρ X eA eB)).trans
        (F.map_comp _ _))
  let α := CondensedRing.sectionModuleComapIso X φ
  let V := (InternalAbelianSheafModule.sectionModuleEquivalence J
    (condensedRingObj (coefficient B) X)).functor
  exact ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight α (SheafOfModules.restrictScalars t) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft V (scalarRestrictionSquare q t c π hs) ≪≫
      (Functor.associator _ _ _).symm⟩

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
