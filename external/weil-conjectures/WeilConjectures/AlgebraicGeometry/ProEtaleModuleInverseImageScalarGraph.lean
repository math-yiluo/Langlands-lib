/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace SheafOfModules
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}}
  (φ : A ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj B)
open MonoidalCategory
private noncomputable def scalarAction (M : SheafOfModules.{u} B) :
    (sheafCompose K (CategoryTheory.forget RingCat.{u})).obj B ⊗
      (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj ((toSheaf B).obj M) ⟶
      (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj ((toSheaf B).obj M) :=
  ⟨{ app := fun U ↦ ↾fun x ↦
       @SMul.smul (B.obj.obj U) (M.val.obj U) inferInstance x.1 x.2
     naturality := by
       intro U V i
       ext x
       exact (M.val.map_smul i x.1 x.2).symm }⟩
private theorem module_scalar_comparison
    [RepresentablyFlat F] [PreservesFiniteLimits (sheafPullback F (Type u) J K)]
    (pr : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (CategoryTheory.forget RingCat.{u})).obj A)
      ((sheafCompose K (CategoryTheory.forget RingCat.{u})).obj B))
    (hr : pr.unit = (sheafCompose J (CategoryTheory.forget RingCat.{u})).map φ) :
    ∃ eM : pullback.{u} φ ⋙ toSheaf B ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u}) ≅
      (toSheaf A ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})) ⋙
        sheafPullback F (Type u) J K,
      ∀ M : SheafOfModules.{u} A,
        ∃ p : SheafPullbackUnitPresentation (F := F)
          ((toSheaf A ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M)
          ((toSheaf B ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
            ((pullback φ).obj M)),
          p.iso = eM.app M ∧
          (∀ U (r : A.obj.obj U) (m : M.val.obj U),
            p.unit.hom.app U (r • m) =
              @SMul.smul (B.obj.obj (F.op.obj U))
                (((pullback φ).obj M).val.obj (F.op.obj U)) inferInstance
                  (φ.hom.app U r) (p.unit.hom.app U m)) := by
  obtain ⟨ea, hea⟩ := inverseImage_underlying_of_ring_presentation φ pr hr
  let c := sheafPullbackForgetIso J K F (CategoryTheory.forget AddCommGrpCat.{u})
  let eM := Functor.isoWhiskerRight ea
    (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})) ≪≫
      Functor.isoWhiskerLeft (toSheaf A) c
  refine ⟨eM, ?_⟩
  intro M
  let p : SheafPullbackUnitPresentation (F := F)
      ((toSheaf A ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M)
      ((toSheaf B ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
        ((pullback φ).obj M)) :=
    { unit := (toSheaf A ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).map
        ((pullbackPushforwardAdjunction φ).unit.app M)
      iso := eM.app M
      equation := by
        intro U m
        have h := congrArg (fun z ↦ z.hom.app U) (hea M)
        have hm := ConcreteCategory.congr_hom h m
        have hc := sheafPullbackForgetIso_unit J K F
          (CategoryTheory.forget AddCommGrpCat.{u}) ((toSheaf A).obj M)
        have hcm := congrArg (fun z ↦ z.hom.app U m) hc
        change (c.hom.app ((toSheaf A).obj M)).hom.app (F.op.obj U)
          ((ea.hom.app M).hom.app (F.op.obj U)
            (((pullbackPushforwardAdjunction φ).unit.app M).val.app U m)) = _
        change (ea.hom.app M).hom.app (F.op.obj U)
          (((pullbackPushforwardAdjunction φ).unit.app M).val.app U m) =
            ((sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
              ((toSheaf A).obj M)).hom.app U m at hm
        change (c.hom.app ((toSheaf A).obj M)).hom.app (F.op.obj U)
          (((sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
            ((toSheaf A).obj M)).hom.app U m) = _ at hcm
        exact (congrArg (fun z ↦ (c.hom.app ((toSheaf A).obj M)).hom.app
          (F.op.obj U) z) hm).trans hcm }
  refine ⟨p, rfl, ?_⟩
  intro U r m
  exact (((pullbackPushforwardAdjunction φ).unit.app M).val.app U).hom.map_smul r m
private theorem transport_scalar_graph
    (M : SheafOfModules.{u} A) (N : SheafOfModules.{u} B)
    (pr : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (CategoryTheory.forget RingCat.{u})).obj A)
      ((sheafCompose K (CategoryTheory.forget RingCat.{u})).obj B))
    (pm : SheafPullbackUnitPresentation (F := F)
      ((toSheaf A ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M)
      ((toSheaf B ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj N))
    (hs : ∀ U (r : A.obj.obj U) (m : M.val.obj U),
      pm.unit.hom.app U (r • m) =
        @SMul.smul (B.obj.obj (F.op.obj U)) (N.val.obj (F.op.obj U)) inferInstance
          (pr.unit.hom.app U r) (pm.unit.hom.app U m))
    (T : Sheaf J (Type u))
    (a : T ⟶ (sheafCompose J (CategoryTheory.forget RingCat.{u})).obj A)
    (b t : T ⟶ (toSheaf A ⋙
      sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M)
    (ht : ∀ U (x : T.obj.obj U),
      @id (M.val.obj U) (t.hom.app U x) =
        @id (A.obj.obj U) (a.hom.app U x) • @id (M.val.obj U) (b.hom.app U x)) :
    ∀ V (x : ((sheafPullback F (Type u) J K).obj T).obj.obj V),
      @id (N.val.obj V)
        (pm.iso.inv.hom.app V (((sheafPullback F (Type u) J K).map t).hom.app V x)) =
        @id (B.obj.obj V)
          (pr.iso.inv.hom.app V (((sheafPullback F (Type u) J K).map a).hom.app V x)) •
        @id (N.val.obj V)
          (pm.iso.inv.hom.app V (((sheafPullback F (Type u) J K).map b).hom.app V x)) := by
  let L := sheafPullback F (Type u) J K
  let pt : SheafPullbackUnitPresentation (F := F) T (L.obj T) :=
    { unit := (sheafAdjunctionContinuous F (Type u) J K).unit.app T
      iso := Iso.refl _
      equation := fun _ _ ↦ rfl }
  let a' := L.map a ≫ pr.iso.inv
  let b' := L.map b ≫ pm.iso.inv
  let t' := L.map t ≫ pm.iso.inv
  let pair : L.obj T ⟶
      (sheafCompose K (CategoryTheory.forget RingCat.{u})).obj B ⊗
        (toSheaf B ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj N :=
    ⟨{ app := fun V ↦ ↾fun x ↦ (a'.hom.app V x, b'.hom.app V x)
       naturality := by
         intro V W i
         ext x
         apply Prod.ext
         · exact congrArg (fun z ↦ z x) (a'.hom.naturality i)
         · exact congrArg (fun z ↦ z x) (b'.hom.naturality i) }⟩
  have hmaps : t' = pair ≫ scalarAction N := by
    apply pt.hom_ext
    intro U x
    have ha := pt.map_unit pr a U x
    have hb := pt.map_unit pm b U x
    have htm := pt.map_unit pm t U x
    change a'.hom.app (F.op.obj U) (pt.unit.hom.app U x) =
      pr.unit.hom.app U (a.hom.app U x) at ha
    change b'.hom.app (F.op.obj U) (pt.unit.hom.app U x) =
      pm.unit.hom.app U (b.hom.app U x) at hb
    change t'.hom.app (F.op.obj U) (pt.unit.hom.app U x) =
      pm.unit.hom.app U (t.hom.app U x) at htm
    change t'.hom.app (F.op.obj U) (pt.unit.hom.app U x) =
      @SMul.smul (B.obj.obj (F.op.obj U)) (N.val.obj (F.op.obj U)) inferInstance
        (a'.hom.app (F.op.obj U) (pt.unit.hom.app U x))
        (b'.hom.app (F.op.obj U) (pt.unit.hom.app U x))
    rw [htm, ha, hb]
    exact (congrArg (fun z : M.val.obj U ↦ pm.unit.hom.app U z) (ht U x)).trans
      (hs U (a.hom.app U x) (b.hom.app U x))
  intro V x
  exact congrArg (fun z ↦ z.hom.app V x) hmaps
end SheafOfModules

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] proEtaleModelRingUnit SheafOfModules.pullback
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
private noncomputable def modelSetEquivalence (X : Scheme.{u}) :
    Sheaf (proEtaleModelTopology X) (Type (u + 1)) ≌
      Sheaf (ProEt.topology X) (Type (u + 1)) :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).sheafPushforwardContinuous
      (Type (u + 1)) (ProEt.topology X) (proEtaleModelTopology X))
    ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      (Type (u + 1)) (proEtaleModelTopology X) (ProEt.topology X))
    (Iso.refl _) (Iso.refl _)

set_option backward.defeqAttrib.useBackward false in
private noncomputable def toModelForgetSetIso (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    proEtaleModuleToModel A ⋙
      SheafOfModules.toSheaf
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
          (proEtaleModelTopology X) (ProEt.topology X)).obj A) ⋙
      sheafCompose (proEtaleModelTopology X) (CategoryTheory.forget AddCommGrpCat.{u + 1}) ≅
    (SheafOfModules.toSheaf A ⋙
      sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})) ⋙
        (modelSetEquivalence X).inverse :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N g
    apply Sheaf.hom_ext
    ext U m
    rfl)

set_option backward.defeqAttrib.useBackward false in
private noncomputable def fromModelForgetSetIso (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    proEtaleModuleFromModel A ⋙ SheafOfModules.toSheaf A ⋙
      sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1}) ≅
    (SheafOfModules.toSheaf
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
        (proEtaleModelTopology X) (ProEt.topology X)).obj A) ⋙
      sheafCompose (proEtaleModelTopology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})) ⋙
      (modelSetEquivalence X).functor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N g
    apply Sheaf.hom_ext
    ext U m
    rfl)

@[irreducible] private noncomputable def modelSetAdjunction {X Y : Scheme.{u}}
    (f : Y ⟶ X) :
    (modelSetEquivalence X).functor ⋙ proEtaleSheafInverseImage f (Type (u + 1)) ⋙
      (modelSetEquivalence Y).inverse ⊣
    (proEtaleModelBaseChange f).sheafPushforwardContinuous (Type (u + 1))
      (proEtaleModelTopology X) (proEtaleModelTopology Y) :=
  (proEtaleSheafAdjunction f (Type (u + 1))).restrictFullyFaithful
    (modelSetEquivalence X).fullyFaithfulFunctor
    (modelSetEquivalence Y).fullyFaithfulFunctor (Iso.refl _) (Iso.refl _)

@[irreducible] private noncomputable def modelSetPullbackIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (modelSetEquivalence X).inverse ⋙
      Functor.sheafPullbackConstruction.sheafPullback (proEtaleModelBaseChange f)
        (Type (u + 1)) (proEtaleModelTopology X) (proEtaleModelTopology Y) ⋙
      (modelSetEquivalence Y).functor ≅ proEtaleSheafInverseImage f (Type (u + 1)) := by
  let a := modelSetAdjunction f
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proEtaleModelBaseChange f) (Type (u + 1))
      (proEtaleModelTopology X) (proEtaleModelTopology Y)
  let q := b.leftAdjointUniq a
  exact Functor.isoWhiskerLeft (modelSetEquivalence X).inverse
    (Functor.isoWhiskerRight q (modelSetEquivalence Y).functor)

/-- Transport an underlying-set comparison from the small models, together with its
inverse-component formula, while keeping the module functor abstract. -/
private theorem scalarGraph_modelComparison {X Y : Scheme.{u}}
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (B : Sheaf (ProEt.topology Y) RingCat.{u + 1})
    (L : SheafOfModules.{u + 1}
        (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
          RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj A) ⥤
      SheafOfModules.{u + 1}
        (((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
          RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj B))
    (Ls : Sheaf (proEtaleModelTopology X) (Type (u + 1)) ⥤
      Sheaf (proEtaleModelTopology Y) (Type (u + 1)))
    (L' : Sheaf (ProEt.topology X) (Type (u + 1)) ⥤
      Sheaf (ProEt.topology Y) (Type (u + 1)))
    (em : L ⋙ SheafOfModules.toSheaf _ ⋙
        sheafCompose (proEtaleModelTopology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1}) ≅
      (SheafOfModules.toSheaf _ ⋙
        sheafCompose (proEtaleModelTopology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})) ⋙ Ls)
    (q : (modelSetEquivalence X).inverse ⋙ Ls ⋙ (modelSetEquivalence Y).functor ≅ L') :
    ∃ eM : (proEtaleModuleToModel A ⋙ L ⋙ proEtaleModuleFromModel B) ⋙
        SheafOfModules.toSheaf B ⋙
        sheafCompose (ProEt.topology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1}) ≅
      (SheafOfModules.toSheaf A ⋙
        sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})) ⋙ L',
      ∀ M, eM.inv.app M =
        q.inv.app ((SheafOfModules.toSheaf A ⋙
          sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj M) ≫
        (modelSetEquivalence Y).functor.map
          (em.inv.app ((proEtaleModuleToModel A).obj M)) := by
  let d := (modelSetEquivalence X).inverse
  let v := (modelSetEquivalence Y).functor
  let p := Functor.isoWhiskerLeft (proEtaleModuleToModel A ⋙ L) (fromModelForgetSetIso Y B)
  let e₀ := Functor.isoWhiskerLeft (proEtaleModuleToModel A)
    (Functor.isoWhiskerRight em v)
  let t₀ := Functor.isoWhiskerRight (toModelForgetSetIso X A) (Ls ⋙ v)
  refine ⟨p ≪≫ e₀ ≪≫ t₀ ≪≫ Functor.isoWhiskerLeft
    (SheafOfModules.toSheaf A ⋙
      sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})) q, ?_⟩
  intro M
  have hid := (Ls ⋙ v).map_id
    (((SheafOfModules.toSheaf A ⋙ sheafCompose (ProEt.topology X)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})) ⋙ d).obj M)
  have hz := congrArg (fun z ↦ ((q.inv.app _ ≫ z) ≫
    v.map (em.inv.app ((proEtaleModuleToModel A).obj M))) ≫ 𝟙 _) hid
  exact hz.trans ((Category.comp_id _).trans
    (congrArg (fun k ↦ k ≫ v.map (em.inv.app ((proEtaleModuleToModel A).obj M)))
      (Category.comp_id _)))

private theorem scalarGraph_naturality
    {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L L' : Sheaf J (Type u) ⥤ Sheaf K (Type u)} (q : L ≅ L')
    {T S : Sheaf J (Type u)} (g : T ⟶ S) (V : Dᵒᵖ)
    (x : (L'.obj T).obj.obj V) :
    (q.inv.app S).hom.app V ((L'.map g).hom.app V x) =
      (L.map g).hom.app V ((q.inv.app T).hom.app V x) :=
  congrArg (fun z ↦ z.hom.app V x) (q.inv.naturality g)

-- The comparison is normalized by simp, then identity maps with transported endpoints
-- are rewritten explicitly. This intentionally uses the simplified goal in the next step.
set_option linter.flexible false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural set comparisons for inverse image respect scalar multiplication on
arbitrary generalized sections.

Source: Stacks Project, Tags 03D2, 03D3 and 04JC.
(auxiliary; not a blueprint node)

Proof: use the small model sites. The actual ring adjunction unit presents the underlying
inverse-image ring as set inverse image. Apply finite-product-preserving set inverse image
to the original module action, and obtain the module action on abelian inverse image.
An abelian map out of this action module is linear exactly when its adjunct is linear
for the ring unit. Restrict the abelian hom equivalence to linear maps; faithfulness
makes the lifts unique and proves naturality. This gives a module adjunction with the
same right adjoint as actual module pullback. Its underlying unit is the abelian unit.
Uniqueness of left adjoints, with its unit equation, gives a natural abelian comparison
normalized on the actual module unit. Compose with the unit-normalized forgetful
comparison to obtain set comparisons and unit presentations pr for the ring and pm for
each module. They satisfy pm.unit(r*m)=pr.unit(r)*pm.unit(m).
For a graph t=a*b on a test sheaf T, compare inverse image of t followed by pm.iso.inv
with the pair of inverse images of a and b followed by pr.iso.inv, pm.iso.inv and the
target scalar action. Maps out of set inverse image are equal when equal on source unit
sections. On these sections the graph hypothesis and the displayed unit-linearity
identity prove equality. Thus the equality holds on every generalized target section.
Transport these comparisons through AsSmall up and down. Naturality of the model/actual
inverse-image comparison on a, b and t gives the required displayed equation. Empty
schemes and the zero coefficient ring require no separate nonemptiness hypothesis.
-/
theorem proEtale_moduleInverseImage_scalarGraph {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (∃ (eR : (proEtaleSheafInverseImage f (Type (u + 1))).obj
            ((sheafCompose (ProEt.topology X) (CategoryTheory.forget CommRingCat.{u + 1})).obj R) ≅
            (sheafCompose (ProEt.topology Y) (CategoryTheory.forget CommRingCat.{u + 1})).obj
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
          (eM : proEtaleModuleInverseImage f R ⋙ SheafOfModules.toSheaf _ ⋙
              sheafCompose (ProEt.topology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1}) ≅
            (SheafOfModules.toSheaf _ ⋙
              sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})) ⋙
                proEtaleSheafInverseImage f (Type (u + 1))),
          ∀ (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
            (T : Sheaf (ProEt.topology X) (Type (u + 1)))
            (a : T ⟶ (sheafCompose (ProEt.topology X)
              (CategoryTheory.forget CommRingCat.{u + 1})).obj R)
            (b t : T ⟶ (SheafOfModules.toSheaf _ ⋙
              sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj M),
            (∀ (U : X.ProEtᵒᵖ) (x : T.obj.obj U),
              @id (M.val.obj U) (t.hom.app U x) =
                @id (R.obj.obj U) (a.hom.app U x) •
                  @id (M.val.obj U) (b.hom.app U x)) →
            ∀ (V : Y.ProEtᵒᵖ)
              (x : ((proEtaleSheafInverseImage f (Type (u + 1))).obj T).obj.obj V),
              @id (((proEtaleModuleInverseImage f R).obj M).val.obj V)
                ((eM.inv.app M).hom.app V
                  (((proEtaleSheafInverseImage f (Type (u + 1))).map t).hom.app V x)) =
                @id (((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R).obj.obj V)
                  (eR.hom.hom.app V
                    (((proEtaleSheafInverseImage f (Type (u + 1))).map a).hom.app V x)) •
                @id (((proEtaleModuleInverseImage f R).obj M).val.obj V)
                  ((eM.inv.app M).hom.app V
                    (((proEtaleSheafInverseImage f (Type (u + 1))).map b).hom.app V x))) := by
  let A := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let B := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
  let φ := proEtaleModelRingUnit f R
  let : (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits (proEtaleModelBaseChange f) := by
    change PreservesFiniteLimits
      ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt) ⋙ proEtaleBaseChange f ⋙ AsSmall.up)
    infer_instance
  let : RepresentablyFlat (proEtaleModelBaseChange f) := flat_of_preservesFiniteLimits _
  obtain ⟨pr, hpr⟩ := proEtaleModelRingPresentation f R
  have hr : pr.unit =
      (sheafCompose (proEtaleModelTopology X) (CategoryTheory.forget RingCat.{u + 1})).map φ := by
    ext U r
    exact hpr U r
  obtain ⟨em, hpm⟩ := SheafOfModules.module_scalar_comparison φ pr hr
  let q := modelSetPullbackIso f
  let d := (modelSetEquivalence X).inverse
  let v := (modelSetEquivalence Y).functor
  obtain ⟨eM, heM⟩ := scalarGraph_modelComparison A B (SheafOfModules.pullback φ)
    (sheafPullback (proEtaleModelBaseChange f) (Type (u + 1))
      (proEtaleModelTopology X) (proEtaleModelTopology Y))
    (proEtaleSheafInverseImage f (Type (u + 1))) em q
  let r₀ := v.mapIso pr.iso
  let eR : (proEtaleSheafInverseImage f (Type (u + 1))).obj
      ((sheafCompose (ProEt.topology X) (CategoryTheory.forget CommRingCat.{u + 1})).obj R) ≅
    ((sheafCompose (ProEt.topology Y) (CategoryTheory.forget CommRingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)) :=
    (r₀ ≪≫ q.app
    ((sheafCompose (ProEt.topology X) (CategoryTheory.forget CommRingCat.{u + 1})).obj R)).symm
  refine ⟨eR, eM, ?_⟩
  intro M T a b t ht V x
  obtain ⟨pm, hme, hs⟩ := hpm ((proEtaleModuleToModel A).obj M)
  let Tm := d.obj T
  let am := d.map a
  let bm := d.map b
  let tm := d.map t
  have htm : ∀ U (z : Tm.obj.obj U),
      @id (((proEtaleModuleToModel A).obj M).val.obj U) (tm.hom.app U z) =
        @id (R.obj.obj (AsSmall.down.op.obj U))
            (am.hom.app U z) •
        @id (((proEtaleModuleToModel A).obj M).val.obj U) (bm.hom.app U z) := by
    intro U z
    exact ht _ z
  let Mm := (proEtaleModuleToModel A).obj M
  let Nm := (SheafOfModules.pullback φ).obj Mm
  let Am := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj A
  let Bm := ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj B
  have hs' : ∀ U (r : Am.obj.obj U) (m : Mm.val.obj U),
      @id (Nm.val.obj ((proEtaleModelBaseChange f).op.obj U))
        (pm.unit.hom.app U (r • m)) =
      @SMul.smul (Bm.obj.obj ((proEtaleModelBaseChange f).op.obj U))
        (Nm.val.obj ((proEtaleModelBaseChange f).op.obj U)) inferInstance
          (pr.unit.hom.app U r) (pm.unit.hom.app U m) := by
    rw [hr]
    exact hs
  have hg := SheafOfModules.transport_scalar_graph ((proEtaleModuleToModel A).obj M)
    ((SheafOfModules.pullback φ).obj ((proEtaleModuleToModel A).obj M))
      pr pm hs' Tm am bm tm htm (AsSmall.up.op.obj V)
        ((q.inv.app T).hom.app V x)
  have hqa := scalarGraph_naturality q a V x
  have hqb := scalarGraph_naturality q b V x
  have hqt := scalarGraph_naturality q t V x
  rw [hme] at hg
  have h₁ := congrArg (fun z ↦
    (em.inv.app ((proEtaleModuleToModel A).obj M)).hom.app (AsSmall.up.op.obj V) z) hqt
  have h₂ := congrArg (fun z ↦ pr.iso.inv.hom.app (AsSmall.up.op.obj V) z) hqa
  have h₃ := congrArg (fun z ↦
    (em.inv.app ((proEtaleModuleToModel A).obj M)).hom.app (AsSmall.up.op.obj V) z) hqb
  rw [heM M]
  exact h₁.trans (hg.trans (congrArg₂ (fun (r : Bm.obj.obj (AsSmall.up.op.obj V))
      (m : Nm.val.obj (AsSmall.up.op.obj V)) ↦ r • m) h₂.symm h₃.symm))

end AlgebraicGeometry.Scheme
