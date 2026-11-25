/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData

/-!
# The integral comparison on profinite test objects

(auxiliary; not a blueprint node).
-/

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace CategoryTheory
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K]
    [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
    [(J.W (A := AddCommGrpCat.{w})).IsMonoidal]
    [(K.W (A := AddCommGrpCat.{w})).IsMonoidal]
    [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [K.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

private lemma pushforwardRingMonObj (R : Sheaf K RingCat.{w}) :
    (Sheaf.monObj_sheafCompose_obj J
      ((F.sheafPushforwardContinuous RingCat.{w} J K).obj R)) =
    (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).monObjObj
      ((sheafCompose K (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj R) := by
  apply MonObj.ext
  apply Sheaf.tensor_hom_ext
  change Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{w}) _ _ ≫ _ = _
  rw [Sheaf.μ_comp_map_mul]
  change _ = Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{w}) _ _ ≫
    (sheafToPresheaf J AddCommGrpCat.{w}).map
      (Functor.LaxMonoidal.μ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K) _ _ ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
          (MonObj.mul (X := (sheafCompose K
            (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj R)))
  rw [Functor.map_comp, ← Category.assoc,
    Functor.μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous]
  apply NatTrans.ext
  funext U
  let : MonObj ((sheafCompose K (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj R).obj :=
    R.obj.monObjCompForget₂
  have h := congr_app (Sheaf.μ_comp_map_mul
    ((sheafCompose K (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj R)) (F.op.obj U)
  simp only [NatTrans.comp_app] at h ⊢
  change _ = 𝟙 _ ≫
    (Functor.LaxMonoidal.μ (sheafToPresheaf K AddCommGrpCat.{w}) _ _).app (F.op.obj U) ≫
      (MonObj.mul (X := (sheafCompose K
        (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj R)).hom.app (F.op.obj U)
  rw [Category.id_comp]
  erw [← h]
  rfl
end CategoryTheory

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma pointRingMonObj (X : Scheme.{u})
    (B : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) :
    Sheaf.monObj_sheafCompose_obj (coherentTopology Profinite.{u})
      ((profiniteToProEt.sheafPushforwardContinuous RingCat.{u + 1}
        (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).obj
          (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).sheafPushforwardContinuous
            RingCat.{u + 1}
              (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X)).obj B)) =
    (sfbPullbackFromPointRightAdjoint X).monObjObj
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj B) := by
  rw [CategoryTheory.pushforwardRingMonObj]
  have h := CategoryTheory.pushforwardRingMonObj
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X))
      (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X) B
  dsimp only [sfbPullbackFromPointRightAdjoint, ProEtale.lowerStar, pointLowerStar]
  rw [h]
  apply MonObj.ext
  dsimp only [Functor.monObjObj]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem constantRing_unit {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{u + 1}] [HasWeakSheafify J (Type (u + 1))]
    [J.HasSheafCompose (forget CommRingCat.{u + 1})]
    [J.PreservesSheafification (forget CommRingCat.{u + 1})] (R : Type (u + 1)) [CommRing R]
    (V : Cᵒᵖ) (r : R) :
    ((constantCommuteCompose J (forget CommRingCat.{u + 1})).app
      (CommRingCat.of R)).hom.hom.app V
        ((toSheafify J
          ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app V r) =
      (toSheafify J
        ((Functor.const Cᵒᵖ).obj R)).app V r := by
  have h := sheafComposeIso_inv_fac J
    (forget CommRingCat.{u + 1}) ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))
  have h' : Functor.whiskerRight (toSheafify J
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))) (forget CommRingCat.{u + 1}) ≫
      ((constantCommuteCompose J
        (forget CommRingCat.{u + 1})).hom.app (CommRingCat.of R)).hom =
      toSheafify J ((Functor.const Cᵒᵖ).obj R) := by
    rw [constantCommuteCompose_hom_app_hom]
    set_option backward.isDefEq.respectTransparency false in
      rw [← Category.assoc, h, ← toSheafify_naturality]
    rfl
  exact congrArg (fun t ↦ t.app V r) h'

private theorem constantRing_binary {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{u + 1}] [HasWeakSheafify J (Type (u + 1))]
    [J.HasSheafCompose (forget CommRingCat.{u + 1})]
    [J.PreservesSheafification (forget CommRingCat.{u + 1})] (R : Type (u + 1)) [CommRing R]
    (V : Cᵒᵖ) (B₀ : Type (u + 1)) (p q : B₀ → R)
    (b : ((constantSheaf J
      (Type (u + 1))).obj B₀).obj.obj V)
    (opR : R → R → R)
    (opS : ∀ W : Cᵒᵖ,
      ((constantSheaf J CommRingCat.{u + 1}).obj
        (CommRingCat.of R)).obj.obj W →
      ((constantSheaf J CommRingCat.{u + 1}).obj
        (CommRingCat.of R)).obj.obj W →
      ((constantSheaf J CommRingCat.{u + 1}).obj
        (CommRingCat.of R)).obj.obj W)
    (hnat : ∀ {W Z : Cᵒᵖ} (f : W ⟶ Z) x y,
      ((constantSheaf J CommRingCat.{u + 1}).obj
        (CommRingCat.of R)).obj.map f (opS W x y) =
      opS Z (((constantSheaf J CommRingCat.{u + 1}).obj
        (CommRingCat.of R)).obj.map f x)
        (((constantSheaf J CommRingCat.{u + 1}).obj
        (CommRingCat.of R)).obj.map f y))
    (hu : ∀ W x y, (toSheafify J
        ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app W (opR x y) =
      opS W ((toSheafify J
        ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app W x)
        ((toSheafify J
        ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app W y)) :
    let F := constantSheaf J (Type (u + 1))
    let k := (constantCommuteCompose J
      (forget CommRingCat.{u + 1})).app (CommRingCat.of R)
    k.inv.hom.app V ((F.map (TypeCat.ofHom (fun b : B₀ ↦ opR (p b) (q b)))).hom.app V b) =
      opS V (k.inv.hom.app V ((F.map (TypeCat.ofHom p)).hom.app V b))
        (k.inv.hom.app V ((F.map (TypeCat.ofHom q)).hom.app V b)) := by
  intro F k
  let P := (Functor.const Cᵒᵖ).obj B₀
  let B := (constantSheaf J CommRingCat.{u + 1}).obj
    (CommRingCat.of R)
  have hunit (W : Cᵒᵖ) (r : R) :
      k.inv.hom.app W ((toSheafify J
        ((Functor.const Cᵒᵖ).obj R)).app W r) =
        (toSheafify J
          ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app W r := by
    have h := congrArg (fun z ↦ k.inv.hom.app W z) (constantRing_unit.{u} J R W r)
    exact h.symm.trans
      (((sheafToPresheaf J (Type (u + 1))).mapIso k
        ).hom_inv_id_app_apply W _)
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp
    ((sheafCompose _ (forget CommRingCat.{u + 1})).obj B).property).isSeparated _
      (Presheaf.imageSieve_mem J (toSheafify _ P) b)).ext
  rintro W f ⟨r, hr⟩
  change (toSheafify J P).app (op W) r =
    (F.obj B₀).obj.map f.op b at hr
  change B.obj.map f.op _ = B.obj.map f.op _
  set_option backward.isDefEq.respectTransparency false in
    rw [hnat]
  have hres (g : B₀ → R) :
      B.obj.map f.op (k.inv.hom.app V ((F.map (TypeCat.ofHom g)).hom.app V b)) =
        (toSheafify J
          ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app (op W) (g r) := by
    have h₁ := NatTrans.naturality_apply k.inv.hom f.op
      ((F.map (TypeCat.ofHom g)).hom.app V b)
    have h₂ := NatTrans.naturality_apply (F.map (TypeCat.ofHom g)).hom f.op b
    change k.inv.hom.app (op W)
        ((F.obj R).obj.map f.op ((F.map (TypeCat.ofHom g)).hom.app V b)) =
      B.obj.map f.op (k.inv.hom.app V ((F.map (TypeCat.ofHom g)).hom.app V b)) at h₁
    change (F.map (TypeCat.ofHom g)).hom.app (op W)
        ((F.obj B₀).obj.map f.op b) =
      (F.obj R).obj.map f.op ((F.map (TypeCat.ofHom g)).hom.app V b) at h₂
    rw [← h₁, ← h₂, ← hr]
    have h₃ := congrArg (fun t ↦ t.app (op W) r)
      (toSheafify_naturality J
        ((Functor.const Cᵒᵖ).map (TypeCat.ofHom g)))
    change (toSheafify J
        ((Functor.const Cᵒᵖ).obj R)).app (op W) (g r) =
      (F.map (TypeCat.ofHom g)).hom.app _ ((toSheafify _ P).app _ r) at h₃
    rw [← h₃, hunit]
  rw [hres, hres, hres]
  exact hu _ _ _

private theorem constantRing_const {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{u + 1}] [HasWeakSheafify J (Type (u + 1))]
    [J.HasSheafCompose (forget CommRingCat.{u + 1})]
    [J.PreservesSheafification (forget CommRingCat.{u + 1})] (R : Type (u + 1))
    [CommRing R] (V : Cᵒᵖ) (B₀ : Type (u + 1)) (r : R)
    (b : ((constantSheaf J
      (Type (u + 1))).obj B₀).obj.obj V) :
    let F := constantSheaf J (Type (u + 1))
    let k := (constantCommuteCompose J
      (forget CommRingCat.{u + 1})).app (CommRingCat.of R)
    k.inv.hom.app V ((F.map (TypeCat.ofHom (fun _ : B₀ ↦ r))).hom.app V b) =
      (toSheafify J
        ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app V r := by
  exact constantRing_binary.{u} J R V B₀ (fun _ ↦ r) (fun _ ↦ r) b
    (fun _ _ ↦ r)
    (fun W _ _ ↦ (toSheafify J
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app W r)
    (by
      intro W Z f x y
      change (sheafify J
        ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).map f _ = _
      exact (NatTrans.naturality_apply
        (toSheafify J
          ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))) f r).symm)
    (by intro W x y; rfl)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def finiteLabelSection (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (R : FintypeCat.{u}) (V : X.ProEtᵒᵖ)
    (f : V.unop ⟶ (profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj R)) :
    ((sfbFiniteConstantSets X).obj R).obj V :=
  (a.inv.app R).app V (ULift.up f)

private theorem finiteLabelSection_map (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    {R T : FintypeCat.{u}} (b : R ⟶ T) (V : X.ProEtᵒᵖ)
    (f : V.unop ⟶ (profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj R)) :
    ((sfbFiniteConstantSets X).map b).app V (finiteLabelSection X a R V f) =
      finiteLabelSection X a T V
        (f ≫ (profiniteToProEtOf X).map (FintypeCat.toProfinite.map b)) := by
  exact (congrArg (fun t ↦ t.app V (ULift.up f)) (a.inv.naturality b)).symm

private theorem finiteRing_binary (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (R : Type u) [CommRing R] [Finite R]
    (V : X.ProEtᵒᵖ)
    (f : V.unop ⟶ (profiniteToProEtOf X).obj
      (FintypeCat.toProfinite.obj (FintypeCat.of (R × R))))
    (opR : R → R → R)
    (opS : ∀ W : X.ProEtᵒᵖ,
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.obj W →
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.obj W →
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.obj W)
    (hnat : ∀ {W Z : X.ProEtᵒᵖ} (g : W ⟶ Z) x y,
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.map g (opS W x y) =
      opS Z (((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.map g x)
        (((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.map g y))
    (hu : ∀ W x y, (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app W
          (ULift.up (opR x.down y.down)) =
      opS W ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app W x)
        ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app W y)) :
    let k := (constantCommuteCompose (Scheme.ProEt.topology X)
      (forget CommRingCat.{u + 1})).app (CommRingCat.of (ULift.{u + 1} R))
    k.inv.hom.app V (finiteLabelSection X a (FintypeCat.of R) V
      (f ≫ (profiniteToProEtOf X).map (FintypeCat.toProfinite.map
        (FintypeCat.homMk (fun p : R × R ↦ opR p.1 p.2))))) =
      opS V (k.inv.hom.app V (finiteLabelSection X a (FintypeCat.of R) V
        (f ≫ (profiniteToProEtOf X).map (FintypeCat.toProfinite.map
          (FintypeCat.homMk Prod.fst)))))
        (k.inv.hom.app V (finiteLabelSection X a (FintypeCat.of R) V
          (f ≫ (profiniteToProEtOf X).map (FintypeCat.toProfinite.map
            (FintypeCat.homMk Prod.snd))))) := by
  intro k
  rw [← finiteLabelSection_map, ← finiteLabelSection_map, ← finiteLabelSection_map]
  exact constantRing_binary.{u} (Scheme.ProEt.topology X) (ULift.{u + 1} R) V
    (ULift.{u + 1} (R × R))
    (fun p ↦ ULift.up p.down.1) (fun p ↦ ULift.up p.down.2)
    (finiteLabelSection X a (FintypeCat.of (R × R)) V f)
    (fun x y ↦ ULift.up (opR x.down y.down)) opS hnat hu

private noncomputable def finitePair (S : Profinite.{u}) (R : FintypeCat.{u})
    (f g : S ⟶ FintypeCat.toProfinite.obj R) :
    S ⟶ FintypeCat.toProfinite.obj (FintypeCat.of (R × R)) := by
  letI := FintypeCat.botTopology R
  letI := FintypeCat.discreteTopology R
  let h : C(S, R × R) :=
    ⟨fun s ↦ (f s, g s), f.hom.hom.continuous.prodMk g.hom.hom.continuous⟩
  have htop : (inferInstance : TopologicalSpace (R × R)) = ⊥ := DiscreteTopology.eq_bot
  exact ConcreteCategory.ofHom
    (show C(S, FintypeCat.toProfinite.obj (FintypeCat.of (R × R))) from
      ⟨fun s ↦ (f s, g s), by
        change @Continuous _ (R × R) _ ⊥ (fun s ↦ (f s, g s))
        rw [← htop]
        exact h.continuous⟩)

private noncomputable def finiteRingSection (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (R : Type u) [CommRing R] [Finite R] (S : Profinite.{u})
    (f : S ⟶ FintypeCat.toProfinite.obj (FintypeCat.of R)) :
    ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} R))).obj.obj
        (op ((profiniteToProEtOf X).obj S)) :=
  (((constantCommuteCompose (Scheme.ProEt.topology X)
    (forget CommRingCat.{u + 1})).app (CommRingCat.of (ULift.{u + 1} R))).inv.hom.app
      (op ((profiniteToProEtOf X).obj S)))
    (finiteLabelSection X a (FintypeCat.of R) (op ((profiniteToProEtOf X).obj S))
      ((profiniteToProEtOf X).map f))

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] finiteRingSection profiniteToProEtOf

private theorem finiteRingSection_binary (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (R : Type u) [CommRing R] [Finite R] (S : Profinite.{u})
    (f g h : S ⟶ FintypeCat.toProfinite.obj (FintypeCat.of R))
    (opR : R → R → R) (hh : ∀ s, h s = opR (f s) (g s))
    (opS : ∀ W : X.ProEtᵒᵖ,
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.obj W →
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.obj W →
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.obj W)
    (hnat : ∀ {W Z : X.ProEtᵒᵖ} (q : W ⟶ Z) x y,
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.map q (opS W x y) =
      opS Z (((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.map q x)
        (((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} R))).obj.map q y))
    (hu : ∀ W x y, (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app W
          (ULift.up (opR x.down y.down)) =
      opS W ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app W x)
        ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app W y)) :
    finiteRingSection X a R S h =
      opS (op ((profiniteToProEtOf X).obj S))
        (finiteRingSection X a R S f) (finiteRingSection X a R S g) := by
  let U := profiniteToProEtOf X
  let pair := finitePair S (FintypeCat.of R) f g
  have hfst : pair ≫ FintypeCat.toProfinite.map (FintypeCat.homMk Prod.fst) = f := by
    ext s
    rfl
  have hsnd : pair ≫ FintypeCat.toProfinite.map (FintypeCat.homMk Prod.snd) = g := by
    ext s
    rfl
  have hop : pair ≫ FintypeCat.toProfinite.map
      (FintypeCat.homMk (fun p : R × R ↦ opR p.1 p.2)) = h := by
    ext s
    exact (hh s).symm
  have ht := finiteRing_binary X a R (op (U.obj S)) (U.map pair) opR opS hnat hu
  have hf' : U.map pair ≫ U.map
      (FintypeCat.toProfinite.map (FintypeCat.homMk Prod.fst)) = U.map f :=
    (U.map_comp _ _).symm.trans (congrArg U.map hfst)
  have hg' : U.map pair ≫ U.map
      (FintypeCat.toProfinite.map (FintypeCat.homMk Prod.snd)) = U.map g :=
    (U.map_comp _ _).symm.trans (congrArg U.map hsnd)
  have hh' : U.map pair ≫ U.map
      (FintypeCat.toProfinite.map (FintypeCat.homMk
        (fun p : R × R ↦ opR p.1 p.2))) = U.map h :=
    (U.map_comp _ _).symm.trans (congrArg U.map hop)
  dsimp only [U] at hf' hg' hh' ht
  simp only [hf', hg', hh'] at ht
  unfold finiteRingSection
  exact ht

private theorem finiteRingSection_const (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (R : Type u) [CommRing R] [Finite R] (S : Profinite.{u})
    (f : S ⟶ FintypeCat.toProfinite.obj (FintypeCat.of R)) (r : R)
    (hf : ∀ s, f s = r) :
    finiteRingSection X a R S f =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))).app
          (op ((profiniteToProEtOf X).obj S)) (ULift.up r) := by
  let b : FintypeCat.of R ⟶ FintypeCat.of R := FintypeCat.homMk (fun _ ↦ r)
  have hcomp : f ≫ FintypeCat.toProfinite.map b = f := by
    ext s
    exact (hf s).symm
  have hm := finiteLabelSection_map X a b (op ((profiniteToProEtOf X).obj S))
    ((profiniteToProEtOf X).map f)
  rw [← Functor.map_comp, hcomp] at hm
  unfold finiteRingSection
  rw [← hm]
  exact constantRing_const.{u} (Scheme.ProEt.topology X) (ULift.{u + 1} R) _
    (ULift.{u + 1} R) (ULift.up r) _

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local semireducible] profiniteToProEtOf finiteRingSection

/-- The completed representation on continuous functions defines a morphism of the
actual ring objects on the profinite point.

proof.md`, Step 4
(auxiliary; not a blueprint node).

Proof: send a continuous function f:S→O_E to d.inv(X[f]). Naturality follows from
naturality of d.inv and functoriality of X[-]. After the nth finite projection, hd
identifies its value with the section of the finite constant ring labelled by the
locally constant reduction q_n∘f; hq identifies q_n with the actual quotient ring map.
For two functions refine their labelled clopen partitions by their intersections.
On a piece labelled (x,y), addition, multiplication and negation have labels x+y, xy
and -x, and the constant functions have labels 0 and 1. The natural finite-label
comparison a preserves these labels: its product comparison is determined by the two
projections, and naturality for the addition, multiplication, negation and singleton
label maps gives the identities. Thus the proposed map preserves every operation
after each finite projection. The projections of the ring-sheaf limit jointly
distinguish sections, so the map is additive and preserves multiplication and one.
Bundle its additive section maps as an abelian-sheaf morphism. The ring objects of
continuous functions and of the completion use the sheafification of sectionwise
multiplication. The tensor-comparison formula for continuous pushforward identifies
their restricted multiplication with sectionwise multiplication; the corresponding
formula for the unit identifies one. Tensor and unit hom extensionality therefore
make this abelian-sheaf morphism a monoid-object morphism. This gives t, and its
section formula is its definition. This step takes place on the profinite point;
no inverse-image or uniqueness assertion is used.
-/
theorem sfb_integral_point_ring_map_exists (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (c : Cone (sfbIntegralFiniteTower l E ⋙ FintypeCat.toProfinite))
    (j : sfbIntegralProfinite l E ≅ c.pt)
    (hq : ∀ (n : ℕ) (x : Padic.coefficientExtensionIntegers l E),
      (j.hom ≫ c.π.app (op n)) x =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x)
    (_hc : IsLimit c)
    (d : (completedIntegralCoefficientSheafUnrestricted l E X).obj ⋙
      forget RingCat.{u + 1} ≅
        uliftYoneda.{u + 1}.obj ((profiniteToProEtOf X).obj (sfbIntegralProfinite l E)))
    (hd : ∀ (V : X.ProEtᵒᵖ)
        (f : V.unop ⟶ (profiniteToProEtOf X).obj (sfbIntegralProfinite l E)) (n : ℕ),
      (sfbIntegralFiniteRepresentation l E X a n).hom.app V
        ((limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app V
          (d.inv.app V (ULift.up f))) =
        ULift.up (f ≫ (profiniteToProEtOf X).map (j.hom ≫ c.π.app (op n)))) :
    ∃ t : sfbCondensedIntegers l E ⟶
        (sfbPullbackFromPointRightAdjoint X).mapMon.obj
          (Mon.mk (sfbCompletedIntegersAb l E X)),
      ∀ (S : Profinite.{u}) (f : S ⟶ sfbIntegralProfinite l E),
        t.hom.hom.app (op S) (ULift.up f.hom.hom) =
          d.inv.app (op ((profiniteToProEtOf X).obj S))
            (ULift.up ((profiniteToProEtOf X).map f)) := by
  let U := profiniteToProEtOf X
  let O := sfbIntegralProfinite l E
  let B := completedIntegralCoefficientSheafUnrestricted l E X
  let val (S : Profinite.{u}) (f : S ⟶ O) :=
    d.inv.app (op (U.obj S)) (ULift.up (U.map f))
  have hproj (S : Profinite.{u}) (f : S ⟶ O) (n : ℕ) :
      (limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app (op (U.obj S))
        (val S f) =
      (((constantCommuteCompose (Scheme.ProEt.topology X)
        (forget CommRingCat.{u + 1})).app
          (CommRingCat.of (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1))))).inv.hom.app (op (U.obj S)))
        (finiteLabelSection X a (sfbIntegralFiniteLevel l E n) (op (U.obj S))
          (U.map (f ≫ j.hom ≫ c.π.app (op n)))) := by
    have h := congrArg ((sfbIntegralFiniteRepresentation l E X a n).inv.app
      (op (U.obj S))) (hd (op (U.obj S)) (U.map f) n)
    rw [(sfbIntegralFiniteRepresentation l E X a n).hom_inv_id_app_apply] at h
    dsimp only [sfbIntegralFiniteRepresentation, Iso.trans_inv, NatTrans.comp_app,
      Functor.mapIso_inv] at h
    simp only [CategoryTheory.comp_apply] at h
    change (limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app
        (op (U.obj S)) (val S f) =
      (((constantCommuteCompose (Scheme.ProEt.topology X)
        (forget CommRingCat.{u + 1})).app
          (CommRingCat.of (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1))))).inv.hom.app (op (U.obj S)))
        (finiteLabelSection X a (sfbIntegralFiniteLevel l E n) (op (U.obj S))
          (U.map f ≫ U.map (j.hom ≫ c.π.app (op n)))) at h
    simpa only [Functor.map_comp] using h
  let := spectralNorm.normedField (Padic l) E
  let : ∀ n : ℕ, Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    fun n ↦ Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  let q (n : ℕ) : Padic.coefficientExtensionIntegers l E →
      Padic.coefficientExtensionRing l E (n + 1) :=
    fun x ↦ (j.hom ≫ c.π.app (op n)) x
  let red (S : Profinite.{u}) (f : C(S, Padic.coefficientExtensionIntegers l E)) (n : ℕ) :=
    (ConcreteCategory.ofHom f : S ⟶ O) ≫ (j.hom ≫ c.π.app (op n))
  let v (S : Profinite.{u}) (x : ULift.{u + 1} C(S, Padic.coefficientExtensionIntegers l E)) :=
    val S (ConcreteCategory.ofHom x.down)
  have hprojection (S : Profinite.{u}) (f : C(S, Padic.coefficientExtensionIntegers l E)) (n : ℕ) :
      (limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app (op (U.obj S))
        (v S (ULift.up f)) =
      finiteRingSection X a (Padic.coefficientExtensionRing l E (n + 1)) S
        (red S f n) := by
    simpa only [finiteRingSection, v, red, sfbIntegralFiniteLevel] using
      hproj S (ConcreteCategory.ofHom f) n
  have hext (S : Profinite.{u}) (x y : B.obj.obj (op (U.obj S)))
      (h : ∀ n, (limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app
        (op (U.obj S)) x =
      (limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app
        (op (U.obj S)) y) : x = y := by
    let ev := sheafToPresheaf (Scheme.ProEt.topology X) RingCat.{u + 1} ⋙
      (evaluation X.ProEtᵒᵖ RingCat.{u + 1}).obj (op (U.obj S))
    apply Concrete.isLimit_ext _ (isLimitOfPreserves ev
      (limit.isLimit (integralCoefficientSheafSystem l E X)))
    intro n
    exact h n.unop
  have hadd (S : Profinite.{u}) (x y : ULift.{u + 1} C(S, Padic.coefficientExtensionIntegers l E)) :
      v S (x + y) = v S x + v S y := by
    apply hext S
    intro n
    rw [map_add]
    rw [hprojection S (x + y).down, hprojection S x.down, hprojection S y.down]
    exact finiteRingSection_binary X a (Padic.coefficientExtensionRing l E (n + 1)) S
      (red S x.down n) (red S y.down n) (red S (x + y).down n) (· + ·)
      (by
        intro s
        change q n (x.down s + y.down s) = q n (x.down s) + q n (y.down s)
        dsimp only [q]
        rw [hq, hq, hq]
        exact map_add _ _ _)
      (fun _ x y ↦ x + y)
      (by intro W Z f x y; exact map_add _ _ _)
      (by intro W x y; exact map_add _ _ _)
  have hmul (S : Profinite.{u}) (x y : ULift.{u + 1} C(S, Padic.coefficientExtensionIntegers l E)) :
      v S (x * y) = v S x * v S y := by
    apply hext S
    intro n
    rw [map_mul]
    rw [hprojection S (x * y).down, hprojection S x.down, hprojection S y.down]
    exact finiteRingSection_binary X a (Padic.coefficientExtensionRing l E (n + 1)) S
      (red S x.down n) (red S y.down n) (red S (x * y).down n) (· * ·)
      (by
        intro s
        change q n (x.down s * y.down s) = q n (x.down s) * q n (y.down s)
        dsimp only [q]
        rw [hq, hq, hq]
        exact map_mul _ _ _)
      (fun _ x y ↦ x * y)
      (by intro W Z f x y; exact map_mul _ _ _)
      (by intro W x y; exact map_mul _ _ _)
  have hzero (S : Profinite.{u}) : v S 0 = 0 := by
    apply hext S
    intro n
    rw [map_zero, hprojection S
      (0 : ULift.{u + 1} C(S, Padic.coefficientExtensionIntegers l E)).down]
    rw [finiteRingSection_const X a _ S _ 0 (by
      intro s
      change q n (0 : Padic.coefficientExtensionIntegers l E) = 0
      dsimp only [q]
      rw [hq]
      exact map_zero _)]
    exact map_zero _
  have hone (S : Profinite.{u}) : v S 1 = 1 := by
    apply hext S
    intro n
    rw [map_one, hprojection S
      (1 : ULift.{u + 1} C(S, Padic.coefficientExtensionIntegers l E)).down]
    rw [finiteRingSection_const X a _ S _ 1 (by
      intro s
      change q n (1 : Padic.coefficientExtensionIntegers l E) = 1
      dsimp only [q]
      rw [hq]
      exact map_one _)]
    exact map_one _
  let R := (profiniteToProEt.sheafPushforwardContinuous RingCat.{u + 1}
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).obj
      (((MorphismProperty.Over.pullback @WeaklyEtale ⊤
        (toSpecZ X)).sheafPushforwardContinuous RingCat.{u + 1}
          (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X)).obj B)
  let r : Profinite.continuousMapRingSheafOfUniverse
      (Padic.coefficientExtensionIntegers l E) ⟶ R := ⟨{
    app := fun S ↦ by
      change RingCat.of (ULift.{u + 1}
        C(S.unop, Padic.coefficientExtensionIntegers l E)) ⟶ B.obj.obj (op (U.obj S.unop))
      exact RingCat.ofHom {
        toFun := v S.unop
        map_one' := hone S.unop
        map_mul' := hmul S.unop
        map_zero' := hzero S.unop
        map_add' := hadd S.unop }
    naturality := by
      intro S T f
      ext x
      have h := congrArg (fun k ↦ k
        (ULift.up (U.map (ConcreteCategory.ofHom x.down : S.unop ⟶ O))))
          (d.inv.naturality (U.map f.unop).op)
      change d.inv.app (op (U.obj T.unop))
          (ULift.up (U.map (f.unop ≫ ConcreteCategory.ofHom x.down))) =
        B.obj.map (U.map f.unop).op
          (d.inv.app (op (U.obj S.unop))
            (ULift.up (U.map (ConcreteCategory.ofHom x.down : S.unop ⟶ O))))
      change d.inv.app (op (U.obj T.unop))
          (ULift.up (U.map f.unop ≫ U.map (ConcreteCategory.ofHom x.down))) = _ at h
      rw [U.map_comp]
      exact h }⟩
  let g := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map r
  have hg : IsMonHom g := by
    exact Sheaf.isMonHom_sheafCompose_map _ r
  have hmon := pointRingMonObj X B
  dsimp only [R] at g hg
  rw [hmon] at hg
  let t : sfbCondensedIntegers l E ⟶
      (sfbPullbackFromPointRightAdjoint X).mapMon.obj
        (Mon.mk (sfbCompletedIntegersAb l E X)) :=
    { hom := g
      isMonHom_hom := hg }
  refine ⟨t, ?_⟩
  intro S f
  rfl

end AlgebraicGeometry.ProEtale
