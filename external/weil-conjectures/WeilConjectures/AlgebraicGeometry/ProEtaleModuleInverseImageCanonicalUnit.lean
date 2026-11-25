/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
/-!
# Unit comparison for the canonical pro-etale module adjunction

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3.
(auxiliary; not a blueprint node)
-/

@[expose] public section
universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- A normalized isomorphism identifies the mate with its inverse.
private theorem isIso_unitMate {C : Type w₁} {D : Type w₂}
    [Category.{v₁} C] [Category.{v₂} D] {L : C ⥤ D} {G : D ⥤ C}
    (adj : L ⊣ G) {M : C} {N : D} (e : N ≅ L.obj M)
    (g : M ⟶ G.obj N) (h : g ≫ G.map e.hom = adj.unit.app M) :
    IsIso ((adj.homEquiv M N).symm g) := by
  have he : (adj.homEquiv M N).symm g = e.inv := by
    apply (adj.homEquiv M N).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, ← h,
      Category.assoc, ← G.map_comp, e.hom_inv_id, G.map_id, Category.comp_id]
  rw [he]
  infer_instance

-- Both transports act on sections by the strict up/down functors.
private noncomputable def fromModelHomEquiv {X : Scheme.{u}}
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (P : SheafOfModules.{u + 1}
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj A))
    (N : SheafOfModules.{u + 1} A) :
    ((proEtaleModuleFromModel A).obj P ⟶ N) ≃
      (P ⟶ (proEtaleModuleToModel A).obj N) where
  toFun h :=
    { val :=
      { app W := h.val.app (AsSmall.down.op.obj W)
        naturality := by
          intro U V i
          ext m
          exact PresheafOfModules.naturality_apply h.val (AsSmall.down.op.map i) m } }
  invFun g :=
    { val :=
      { app W := g.val.app (AsSmall.up.op.obj W)
        naturality := by
          intro U V i
          ext m
          exact PresheafOfModules.naturality_apply g.val (AsSmall.up.op.map i) m } }
  left_inv h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl
  right_inv g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl

-- Restrict the original abelian adjunction to the model sites, retaining its unit.
private noncomputable def modelSheafEquivalence (X : Scheme.{u}) :
    Sheaf (proEtaleModelTopology X) AddCommGrpCat.{u + 1} ≌
      Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (ProEt.topology X) (proEtaleModelTopology X))
    ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X))
    (Iso.refl _) (Iso.refl _)
@[irreducible] private noncomputable def modelAbelianAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (modelSheafEquivalence Y).functor ⋙ proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} ⋙
      (modelSheafEquivalence X).inverse ⊣
        (proEtaleModelBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (proEtaleModelTopology Y) (proEtaleModelTopology X) :=
  (proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).restrictFullyFaithful
    (modelSheafEquivalence Y).fullyFaithfulFunctor
    (modelSheafEquivalence X).fullyFaithfulFunctor
    (Iso.refl _) (Iso.refl _)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
private abbrev A := (sheafCompose (ProEt.topology Y)
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
private noncomputable abbrev B := (sheafCompose (ProEt.topology X)
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
private noncomputable abbrev T := SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
  (J := ProEt.topology Y) (K := ProEt.topology X) (S := A R) (R := B f R)
  ⟨Functor.whiskerRight ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
private noncomputable def directEquiv
    (M : SheafOfModules.{u + 1} (A R)) (N : SheafOfModules.{u + 1} (B f R)) :
    ((proEtaleModuleToModel (A R)).obj M ⟶
      (SheafOfModules.pushforward (proEtaleModelRingUnit f R)).obj
        ((proEtaleModuleToModel (B f R)).obj N)) ≃ (M ⟶ (T f R).obj N) where
  toFun h :=
    { val :=
      { app W := h.val.app (AsSmall.up.op.obj W)
        naturality := by
          intro U V i
          ext m
          exact PresheafOfModules.naturality_apply h.val (AsSmall.up.op.map i) m } }
  invFun g :=
    { val :=
      { app W := g.val.app (AsSmall.down.op.obj W)
        naturality := by
          intro U V i
          ext m
          exact PresheafOfModules.naturality_apply g.val (AsSmall.down.op.map i) m } }
  left_inv h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl
  right_inv g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl
private noncomputable def homEquiv
    (M : SheafOfModules.{u + 1} (A R)) (N : SheafOfModules.{u + 1} (B f R)) :
    ((proEtaleModuleInverseImage f R).obj M ⟶ N) ≃ (M ⟶ (T f R).obj N) :=
  (fromModelHomEquiv _ _ _).trans
    (((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).homEquiv
      _ _).trans (directEquiv f R M N))
private theorem homEquiv_left
    (M M' : SheafOfModules.{u + 1} (A R)) (N : SheafOfModules.{u + 1} (B f R))
    (k : M ⟶ M') (h : (proEtaleModuleInverseImage f R).obj M' ⟶ N) :
    homEquiv f R M N ((proEtaleModuleInverseImage f R).map k ≫ h) =
      k ≫ homEquiv f R M' N h := by
  have hn := (SheafOfModules.pullbackPushforwardAdjunction
    (proEtaleModelRingUnit f R)).homEquiv_naturality_left
    ((proEtaleModuleToModel (A R)).map k) (fromModelHomEquiv _ _ _ h)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact congrArg (fun z ↦ z.val.app (AsSmall.up.op.obj U) m) hn
private theorem homEquiv_right
    (M : SheafOfModules.{u + 1} (A R)) (N N' : SheafOfModules.{u + 1} (B f R))
    (k : N ⟶ N') (h : (proEtaleModuleInverseImage f R).obj M ⟶ N) :
    homEquiv f R M N' (h ≫ k) =
      homEquiv f R M N h ≫ (T f R).map k := by
  have hn := (SheafOfModules.pullbackPushforwardAdjunction
    (proEtaleModelRingUnit f R)).homEquiv_naturality_right
    (fromModelHomEquiv _ _ _ h) ((proEtaleModuleToModel (B f R)).map k)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact congrArg (fun z ↦ z.val.app (AsSmall.up.op.obj U) m) hn
@[irreducible] private noncomputable def canonicalAdjunction :
    proEtaleModuleInverseImage f R ⊣ T f R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv f R
      homEquiv_naturality_left_symm := by
        intro M M' N k h
        apply (homEquiv f R M N).injective
        rw [Equiv.apply_symm_apply, homEquiv_left, Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun h k ↦ homEquiv_right f R _ _ _ k h }
private theorem canonicalAdjunction_homEquiv :
    (canonicalAdjunction f R).homEquiv = homEquiv f R := by
  rw [canonicalAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
-- The Hom equivalence makes the module unit literally the model unit on sections.
private theorem canonicalUnit_sections
    (M : SheafOfModules.{u + 1} (A R)) (U : Y.ProEtᵒᵖ) (m : M.val.obj U) :
    ((canonicalAdjunction f R).unit.app M).val.app U m =
      ((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).unit.app
        ((proEtaleModuleToModel _).obj M)).val.app (AsSmall.up.op.obj U) m := by
  rw [← (canonicalAdjunction f R).homEquiv_id M, canonicalAdjunction_homEquiv]
  change ((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).homEquiv
    ((proEtaleModuleToModel (A R)).obj M) _
    (fromModelHomEquiv _ _ _ (𝟙 ((proEtaleModuleInverseImage f R).obj M)))).val.app
      (AsSmall.up.op.obj U) m = _
  rw [Adjunction.homEquiv_unit]
  rfl

-- Compose the normalized model module comparison with uniqueness of abelian left adjoints.
private theorem canonicalComparisonProof :
    ∃ adj : proEtaleModuleInverseImage f R ⊣ T f R,
      ∀ M, IsIso (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv
        ((SheafOfModules.toSheaf (A R)).obj M)
        ((SheafOfModules.toSheaf (B f R)).obj ((proEtaleModuleInverseImage f R).obj M))).symm
          ((SheafOfModules.toSheaf (A R)).map (adj.unit.app M))) := by
  let : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits (proEtaleModelBaseChange f) := by
    change PreservesFiniteLimits
      ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt) ⋙ proEtaleBaseChange f ⋙ AsSmall.up)
    infer_instance
  let : RepresentablyFlat (proEtaleModelBaseChange f) := flat_of_preservesFiniteLimits _
  obtain ⟨p, hp⟩ := proEtaleModelRingPresentation f R
  obtain ⟨em, hem⟩ := SheafOfModules.inverseImage_underlying_of_ring_presentation
    (proEtaleModelRingUnit f R) p (by ext U r; exact hp U r)
  let a := modelAbelianAdjunction f
  let b := sheafAdjunctionContinuous (proEtaleModelBaseChange f) AddCommGrpCat.{u + 1}
    (proEtaleModelTopology Y) (proEtaleModelTopology X)
  let q := b.leftAdjointUniq a
  let P := SheafOfModules.toSheaf.{u + 1} (A R)
  let Q := SheafOfModules.toSheaf.{u + 1} (B f R)
  let G := proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}
  let adj := proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}
  refine ⟨canonicalAdjunction f R, ?_⟩
  intro M
  let Mm := (proEtaleModuleToModel (A R)).obj M
  let N := ((SheafOfModules.toSheaf _).obj Mm)
  let e : Q.obj ((proEtaleModuleInverseImage f R).obj M) ≅
      (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj (P.obj M) :=
    (modelSheafEquivalence X).functor.mapIso (em.app Mm ≪≫ q.app N)
  have hunit : P.map ((canonicalAdjunction f R).unit.app M) ≫ G.map e.hom =
      adj.unit.app (P.obj M) := by
    have h₁ := hem Mm
    have h₂ := congrArg (modelSheafEquivalence Y).functor.map
      (Adjunction.unit_leftAdjointUniq_hom_app b a N)
    change _ = (modelSheafEquivalence Y).functor.map
      ((modelAbelianAdjunction f).unit.app N) at h₂
    rw [modelAbelianAdjunction, Adjunction.map_restrictFullyFaithful_unit_app] at h₂
    simp only [Iso.refl_hom, NatTrans.id_app] at h₂
    ext U m
    have h₁' := congrArg (fun z ↦ z.hom.app (AsSmall.up.op.obj U) m) h₁
    have h₂' := congrArg (fun z ↦ z.hom.app U m) h₂
    change e.hom.hom.app ((proEtaleBaseChange f).op.obj U)
      (((canonicalAdjunction f R).unit.app M).val.app U m) = _
    rw [canonicalUnit_sections]
    change (q.hom.app N).hom.app ((proEtaleModelBaseChange f).op.obj
      (AsSmall.up.op.obj U))
      ((em.hom.app Mm).hom.app ((proEtaleModelBaseChange f).op.obj (AsSmall.up.op.obj U))
        (((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).unit.app
          Mm).val.app (AsSmall.up.op.obj U) m)) = _
    change (em.hom.app Mm).hom.app ((proEtaleModelBaseChange f).op.obj
      (AsSmall.up.op.obj U))
      (((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).unit.app
        Mm).val.app (AsSmall.up.op.obj U) m) = _ at h₁'
    rw [h₁']
    exact h₂'
  exact isIso_unitMate adj e (P.map ((canonicalAdjunction f R).unit.app M)) hunit
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
/-- A canonical adjunction for module inverse image has an invertible underlying unit mate.

This isolates the strict `AsSmall` transport and the module-action comparison from the
uniqueness argument for arbitrary adjunctions.  Its proof follows Tags 03D2 and 03D3:
transport the module pullback adjunction through the two site equivalences and use the
unit-compatible underlying comparison supplied by the model presentation.
(auxiliary; not a blueprint node) -/
theorem proEtaleModuleInverseImage_canonicalUnitComparison {X Z : Scheme.{u}} (i : Z ⟶ X)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ∃ (adj₀ : (proEtaleModuleInverseImage i A ⊣
      (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange i)
      (J := ProEt.topology X) (K := ProEt.topology Z)
      (S := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (R := ((sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)))
      ⟨Functor.whiskerRight
        ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app A).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩))),
      let S := (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A
      let R := (sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)
      ∀ M, IsIso (((proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).homEquiv
        ((SheafOfModules.toSheaf S).obj M)
        ((SheafOfModules.toSheaf R).obj ((proEtaleModuleInverseImage i A).obj M))).symm
          ((SheafOfModules.toSheaf S).map (adj₀.unit.app M))) := by
  exact canonicalComparisonProof i A
end AlgebraicGeometry.Scheme
