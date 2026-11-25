/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteRingTorsorAssociatedModule
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RepresentationTheory.Rep.Basic
import WeilConjectures.ConstructibleSheaf.TorsorSectionRepresentation
import WeilConjectures.ConstructibleSheaf.ConstantModuleLocallyConstant
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import WeilConjectures.Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Associated module sheaves for a finite torsor with finite ring coefficients

## References

* Stacks Project, Tags 0DV5 (3), 0DV6, 04TR and 04TS
* Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R
* Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS
* Stacks Project, Tag 0DV5 (3), Tag 0DV6, and Tags 04TR and 04TS
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
open Etale
namespace Scheme.GaloisCover

private noncomputable def sectionRepresentationOver
    {V : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]
    {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Rep.{u + 1} Λ P :=
  Rep.of (X := F.obj.obj (op c.sectionObject))
    { toFun g := (F.obj.map (c.sectionDeck g⁻¹).op).hom
      map_one' := by
        have hd : c.sectionDeck (1 : P) = 𝟙 _ := by
          apply Scheme.EtaleTorsor.etaleHom_ext
          exact c.one_smul
        simp [hd]
        rfl
      map_mul' g h := by
        have hd (a b : P) : c.sectionDeck (a * b) =
            c.sectionDeck b ≫ c.sectionDeck a := by
          apply Scheme.EtaleTorsor.etaleHom_ext
          exact c.mul_smul ⟨a⟩ ⟨b⟩
        simp only [mul_inv_rev, hd, op_comp, Functor.map_comp]
        rfl }

private noncomputable abbrev sectionRepresentationPresheafOver
    {V : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]
    {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  c.equivariantModulePresheafOver Λ (sectionRepresentationOver Λ c F)

private def SectionEvaluationNormalizedOver
    {V : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]
    {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (α : F.obj ⟶ sectionRepresentationPresheafOver Λ c F) : Prop :=
  ∀ (s : F.obj.obj (op c.sectionObject)) (y : c.P),
    (α.app (op c.sectionObject) s).val
      (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp) y) = s

end Scheme.GaloisCover

/-- Ordinary evaluation exists without imposing deck equivariance.
Fixed-cover adaptation to arbitrary modules. -/
private theorem Scheme.GaloisCover.exists_ordinarySectionEvaluationOver
    {V : Scheme.{u}} [ConnectedSpace V] (Λ : Type (u + 1)) [CommRing Λ]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (Λ)))
    (A : ModuleCat.{u + 1} (Λ))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (Λ)].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (Λ))).obj A)) :
    ∃ β : ∀ W : V.Etaleᵒᵖ, F.obj.obj W →ₗ[Λ]
      LocallyConstant (c.sectionSpace W.unop) (F.obj.obj (op c.sectionObject)),
      (∀ (W W' : V.Etaleᵒᵖ) (f : W ⟶ W') (s : F.obj.obj W)
        (x : c.sectionSpace W'.unop),
      β W' (F.obj.map f s) x = β W s (c.sectionRestriction f.unop x)) ∧
      (∀ (s : F.obj.obj (op c.sectionObject)) (y : c.P),
      β (op c.sectionObject) s
        (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp) y) = s) := by
  classical
  let R := Λ
  let C := ModuleCat.{u + 1} R
  let D := MorphismProperty.Over.map ⊤ c.etale
  let Q := c.π.Etale
  let adj := MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤
    c.π c.etale trivial
  let T : c.P.Etale := Scheme.Etale.mk (𝟙 c.P)
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  obtain ⟨e⟩ := h
  obtain ⟨eLC⟩ := Scheme.Etale.locallyConstantModulePresheafFunctor_iso_constantSheaf c.P Λ
  let k : (sheafToPresheaf _ _).obj
      ((localizationRestriction C c.π c.etale).obj F) ≅
      (Scheme.Etale.locallyConstantModulePresheafFunctor c.P Λ).obj A :=
    (sheafToPresheaf _ _).mapIso
      ((upperStarIsoLocalizationRestriction C c.π c.etale).app F).symm ≪≫
    (sheafToPresheaf _ _).mapIso e ≪≫ (eLC.app A).symm
  let t : D.obj T ≅ c.sectionObject :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change (𝟙 c.P) ≫ c.π = (𝟙 c.P) ≫ c.π
      rfl)
  obtain ⟨y₀⟩ := ‹ConnectedSpace c.P›.toNonempty
  let ev : LocallyConstant c.P A ≃ₗ[Λ] A :=
    { toFun := fun f ↦ f y₀
      invFun := LocallyConstant.const _
      left_inv := by
        intro f
        ext y
        exact f.isLocallyConstant.apply_eq_of_preconnectedSpace y₀ y
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let b : F.obj.obj (op c.sectionObject) ≃ₗ[Λ] A :=
    (F.obj.mapIso t.op).toLinearEquiv.trans
      ((k.app (op T)).toLinearEquiv.trans ev)
  let a₀ (W : V.Etaleᵒᵖ) : F.obj.obj W →ₗ[Λ]
      LocallyConstant (c.sectionSpace W.unop) A :=
    (k.hom.app (op (Q.obj W.unop))).hom.comp
      (F.obj.map (adj.counit.app W.unop).op).hom
  let β (W : V.Etaleᵒᵖ) : F.obj.obj W →ₗ[Λ]
      LocallyConstant (c.sectionSpace W.unop) (F.obj.obj (op c.sectionObject)) :=
    (LocallyConstant.mapₗ Λ b.symm.toLinearMap).comp (a₀ W)
  refine ⟨β, ?_, ?_⟩
  · intro W W' f s x
    change b.symm (a₀ W' (F.obj.map f s) x) =
      b.symm (a₀ W s (c.sectionRestriction f.unop x))
    congr 1
    have hn := ConcreteCategory.congr_hom
      (k.hom.naturality (Q.map f.unop).op)
      (F.obj.map (adj.counit.app W.unop).op s)
    have hc : (adj.counit.app W'.unop) ≫ f.unop =
        D.map (Q.map f.unop) ≫ (adj.counit.app W.unop) :=
      (adj.counit.naturality f.unop).symm
    have hF : F.obj.map (adj.counit.app W'.unop).op (F.obj.map f s) =
        F.obj.map (D.map (Q.map f.unop)).op
          (F.obj.map (adj.counit.app W.unop).op s) := by
      have hm := congrArg
        (fun g : D.obj (Q.obj W'.unop) ⟶ W.unop ↦ F.obj.map g.op) hc
      simp only [op_comp, Functor.map_comp] at hm
      exact ConcreteCategory.congr_hom hm s
    have hval : a₀ W' (F.obj.map f s) =
        (a₀ W s).comap (Q.map f.unop).left.base.hom := by
      change (k.hom.app (op (Q.obj W'.unop))).hom
        ((F.obj.map (adj.counit.app W'.unop).op).hom ((F.obj.map f).hom s)) = _
      rw [hF]
      exact hn
    exact congrArg (fun g : LocallyConstant (c.sectionSpace W'.unop) A ↦ g x) hval
  · intro s y
    let δ : T ⟶ Q.obj c.sectionObject :=
      MorphismProperty.Over.homMk
        (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp))
        (by
          change pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) _ ≫
            pullback.snd c.π c.π = 𝟙 c.P
          exact pullback.lift_snd _ _ _)
    have hd : D.map δ ≫ adj.counit.app c.sectionObject = t.hom := by
      apply MorphismProperty.Over.Hom.ext
      change pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) _ ≫
        pullback.fst c.π c.π = 𝟙 c.P
      simp
    have hn := ConcreteCategory.congr_hom (k.hom.naturality δ.op)
      (F.obj.map (adj.counit.app c.sectionObject).op s)
    have hF : F.obj.map (D.map δ).op
        (F.obj.map (adj.counit.app c.sectionObject).op s) =
        F.obj.map t.hom.op s := by
      have hm := congrArg (fun g : D.obj T ⟶ c.sectionObject ↦ F.obj.map g.op) hd
      simp only [op_comp, Functor.map_comp] at hm
      exact ConcreteCategory.congr_hom hm s
    have hv : (show LocallyConstant c.P A from k.hom.app (op T)
        (F.obj.map t.hom.op s)) =
        (a₀ (op c.sectionObject) s).comap δ.left.base.hom := by
      rw [← hF]
      exact hn
    change b.symm (a₀ (op c.sectionObject) s
      (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) _ y)) = s
    apply b.injective
    rw [b.apply_symm_apply]
    have hy := congrArg (fun g : LocallyConstant c.P A ↦ g y) hv
    change (show LocallyConstant c.P A from k.hom.app (op T)
      (F.obj.map t.hom.op s)) y = a₀ (op c.sectionObject) s (δ.left y) at hy
    refine hy.symm.trans ?_
    let g : LocallyConstant c.P A := k.hom.app (op T) (F.obj.map t.hom.op s)
    exact g.isLocallyConstant.apply_eq_of_preconnectedSpace
      y y₀

/-- Constant coordinates for a sheaf trivialized by a connected torsor, with a
pointwise local description by restrictions of global sections upstairs. -/
private theorem Scheme.GaloisCover.constantCoordinates_localRestrictionOver
    {V : Scheme.{u}} [ConnectedSpace V] (Λ : Type (u + 1)) [CommRing Λ]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (Λ)))
    (A : ModuleCat.{u + 1} (Λ))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (Λ)].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (Λ))).obj A))
    (W : V.Etaleᵒᵖ) (f : W.unop ⟶ c.sectionObject) :
    ∃ γ : F.obj.obj W ≃ LocallyConstant W.unop.left
        (F.obj.obj (Opposite.op c.sectionObject)),
      ∀ (s : F.obj.obj W) (w : W.unop.left),
        ∃ (U : V.Etale) (i : U ⟶ W.unop) (z : U.left)
          (x : F.obj.obj (Opposite.op c.sectionObject)),
          i.left z = w ∧ F.obj.map i.op s = F.obj.map (i ≫ f).op x ∧ γ s w = x := by
  classical
  let R := Λ
  let C := ModuleCat.{u + 1} R
  let U := CategoryTheory.forget₂ C AddCommGrpCat.{u + 1}
  have : PreservesColimitsOfSize.{u + 1, u + 1} U :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} R
  have : c.P.smallEtaleTopology.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification c.P.smallEtaleTopology U
  let D := MorphismProperty.Over.map ⊤ c.etale
  let T : c.P.Etale := Scheme.Etale.mk (𝟙 c.P)
  let Z : c.P.Etale := Scheme.Etale.mk f.left
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  obtain ⟨e⟩ := h
  let k : (sheafCompose c.P.smallEtaleTopology U).obj
      ((localizationRestriction C c.π c.etale).obj F) ≅
      Scheme.Etale.continuousMapSheaf c.P A :=
    (sheafCompose c.P.smallEtaleTopology U).mapIso
      ((upperStarIsoLocalizationRestriction C c.π c.etale).app F).symm ≪≫
    (sheafCompose c.P.smallEtaleTopology U).mapIso e ≪≫
    (constantCommuteCompose c.P.smallEtaleTopology U).app A ≪≫
    Scheme.Etale.constantSheafIsoContinuousMapSheaf c.P A
  let t : D.obj T ≅ c.sectionObject :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change (𝟙 c.P) ≫ c.π = (𝟙 c.P) ≫ c.π
      rfl)
  let tW : D.obj Z ≅ W.unop :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change (𝟙 W.unop.left) ≫ W.unop.hom =
        (𝟙 W.unop.left) ≫ f.left ≫ c.π
      simpa using (MorphismProperty.Over.w f).symm)
  obtain ⟨y₀⟩ := ‹ConnectedSpace c.P›.toNonempty
  let ev : C(c.P, A) ≃+ A :=
    { toFun := fun g ↦ g y₀
      invFun := ContinuousMap.const _
      left_inv := by
        intro g
        ext y
        exact ((IsLocallyConstant.iff_continuous g).2 g.continuous).apply_eq_of_preconnectedSpace
          y₀ y
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  let b : F.obj.obj (Opposite.op c.sectionObject) ≃+ A :=
    ((F.obj.mapIso t.op).toLinearEquiv.toAddEquiv).trans
      (((((sheafToPresheaf _ _).mapIso k).app (Opposite.op T)).addCommGroupIsoToAddEquiv).trans
        ev)
  let r : F.obj.obj W ≃ C(W.unop.left, A) :=
    (F.obj.mapIso tW.op).toLinearEquiv.toEquiv.trans
      (((((sheafToPresheaf _ _).mapIso k).app (Opposite.op Z)).addCommGroupIsoToAddEquiv).toEquiv)
  let lc : C(W.unop.left, A) ≃ LocallyConstant W.unop.left A :=
    { toFun := fun g ↦ ⟨g, (IsLocallyConstant.iff_continuous g).2 g.continuous⟩
      invFun := fun g ↦ g.toContinuousMap
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let γ : F.obj.obj W ≃ LocallyConstant W.unop.left
      (F.obj.obj (Opposite.op c.sectionObject)) :=
    r.trans (lc.trans (LocallyConstant.congrRight b.symm.toEquiv))
  refine ⟨γ, ?_⟩
  intro s w
  let O := W.unop.left.fiberOpens (r s) (r s w)
  let B : c.P.Etale := Scheme.Etale.mk (O.ι ≫ f.left)
  let j : B ⟶ Z := MorphismProperty.Over.homMk O.ι rfl
  let q : B ⟶ T := MorphismProperty.Over.homMk B.hom (by
    change B.hom ≫ 𝟙 c.P = B.hom
    exact Category.comp_id _)
  let i : D.obj B ⟶ W.unop := D.map j ≫ tW.hom
  let z : O := ⟨w, rfl⟩
  let x := b.symm (r s w)
  refine ⟨D.obj B, i, z, x, ?_, ?_, ?_⟩
  · change (O.ι ≫ 𝟙 _) z = w
    simp [z]
  · have hi : D.map j ≫ tW.hom = i := rfl
    have hq : D.map q ≫ t.hom = i ≫ f := by
      apply MorphismProperty.Over.Hom.ext
      change (O.ι ≫ f.left) ≫ 𝟙 _ = (O.ι ≫ 𝟙 _) ≫ f.left
      simp
    have hj := ConcreteCategory.congr_hom (k.hom.hom.naturality j.op)
      (F.obj.map tW.hom.op s)
    have hqnat := ConcreteCategory.congr_hom (k.hom.hom.naturality q.op)
      (F.obj.map t.hom.op x)
    have hFis : F.obj.map (D.map j).op (F.obj.map tW.hom.op s) =
        F.obj.map i.op s := by
      rw [← ModuleCat.comp_apply, ← F.obj.map_comp, ← CategoryTheory.op_comp, hi]
    have hFix : F.obj.map (D.map q).op (F.obj.map t.hom.op x) =
        F.obj.map (i ≫ f).op x := by
      rw [← ModuleCat.comp_apply, ← F.obj.map_comp, ← CategoryTheory.op_comp, hq]
    have hb : (show C(c.P, A) from k.hom.hom.app (Opposite.op T)
        (F.obj.map t.hom.op x)) = ContinuousMap.const _ (r s w) := by
      ext y
      let v : C(c.P, A) := k.hom.hom.app (Opposite.op T) (F.obj.map t.hom.op x)
      change v y = r s w
      calc
        v y = v y₀ :=
          ((IsLocallyConstant.iff_continuous v).2 v.continuous).apply_eq_of_preconnectedSpace
            y y₀
        _ = b x := rfl
        _ = r s w := b.apply_symm_apply _
    apply (ConcreteCategory.bijective_of_isIso (k.hom.hom.app (Opposite.op B))).1
    change k.hom.hom.app (Opposite.op B) (F.obj.map i.op s) =
      k.hom.hom.app (Opposite.op B) (F.obj.map (i ≫ f).op x)
    rw [← hFis, ← hFix]
    change (show C(B.left, A) from k.hom.hom.app (Opposite.op B)
      (F.obj.map (D.map j).op (F.obj.map tW.hom.op s))) =
      (show C(B.left, A) from k.hom.hom.app (Opposite.op B)
        (F.obj.map (D.map q).op (F.obj.map t.hom.op x)))
    change (show C(B.left, A) from k.hom.hom.app (Opposite.op B)
      (F.obj.map (D.map j).op (F.obj.map tW.hom.op s))) =
      (r s).comp j.left.base.hom at hj
    change (show C(B.left, A) from k.hom.hom.app (Opposite.op B)
      (F.obj.map (D.map q).op (F.obj.map t.hom.op x))) =
      (show C(c.P, A) from k.hom.hom.app (Opposite.op T)
        (F.obj.map t.hom.op x)).comp q.left.base.hom at hqnat
    rw [hj, hqnat, hb]
    ext y
    exact y.property
  · rfl

/-- The value of an ordinary normalized evaluation on the graph of f gives the
constant-sheaf coordinates on W. No equivariance of the evaluation is assumed. -/
private theorem Scheme.GaloisCover.ordinaryGraphEvaluation_bijectiveOver
    {V : Scheme.{u}} [ConnectedSpace V] (Λ : Type (u + 1)) [CommRing Λ]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (Λ)))
    (A : ModuleCat.{u + 1} (Λ))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (Λ)].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (Λ))).obj A))
    (β : ∀ T : V.Etaleᵒᵖ, F.obj.obj T →ₗ[Λ]
      LocallyConstant (c.sectionSpace T.unop) (F.obj.obj (Opposite.op c.sectionObject)))
    (hβ : ∀ (T T' : V.Etaleᵒᵖ) (g : T ⟶ T') (s : F.obj.obj T)
        (x : c.sectionSpace T'.unop),
      β T' (F.obj.map g s) x = β T s (c.sectionRestriction g.unop x))
    (hΔ : ∀ (s : F.obj.obj (Opposite.op c.sectionObject)) (y : c.P),
      β (Opposite.op c.sectionObject) s
        (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp) y) = s) (W : V.Etaleᵒᵖ)
    (f : W.unop ⟶ c.sectionObject) :
    Function.Bijective (fun s : F.obj.obj W ↦
      LocallyConstant.comap
        (pullback.lift (f := W.unop.hom) (g := c.π) (𝟙 W.unop.left) f.left
          (by simpa using (MorphismProperty.Over.w f).symm)).base.hom
        (β W s)) := by
  obtain ⟨γ, hγ⟩ := c.constantCoordinates_localRestrictionOver Λ P F A h W f
  let graph (T : V.Etale) (g : T ⟶ c.sectionObject) : T.left ⟶ c.sectionSpace T :=
    pullback.lift (𝟙 T.left) g.left
      (by simpa using (MorphismProperty.Over.w g).symm)
  have heq (s : F.obj.obj W) :
      LocallyConstant.comap (graph W.unop f).base.hom (β W s) = γ s := by
    apply LocallyConstant.ext
    intro w
    obtain ⟨U, i, z, x, hiz, hs, hx⟩ := hγ s w
    have hi : graph U (i ≫ f) ≫ c.sectionRestriction i =
        i.left ≫ graph W.unop f := by
      apply pullback.hom_ext <;> simp [graph, Scheme.GaloisCover.sectionRestriction]
      rfl
    have hf : graph U (i ≫ f) ≫ c.sectionRestriction (i ≫ f) =
        (i ≫ f).left ≫ graph c.sectionObject (𝟙 _) := by
      apply pullback.hom_ext <;> simp [graph, Scheme.GaloisCover.sectionRestriction]
      rfl
    change β W s (graph W.unop f w) = γ s w
    rw [hx, ← hiz]
    rw [← Scheme.Hom.comp_apply, ← hi, Scheme.Hom.comp_apply]
    have hb := hβ W (Opposite.op U) i.op s (graph U (i ≫ f) z)
    change β (Opposite.op U) (F.obj.map i.op s) (graph U (i ≫ f) z) =
      β W s (c.sectionRestriction i (graph U (i ≫ f) z)) at hb
    rw [← hb, hs]
    rw [hβ (Opposite.op c.sectionObject) (Opposite.op U) (i ≫ f).op x
      (graph U (i ≫ f) z)]
    change β (Opposite.op c.sectionObject) x
      (c.sectionRestriction (i ≫ f) (graph U (i ≫ f) z)) = x
    rw [← Scheme.Hom.comp_apply, hf, Scheme.Hom.comp_apply]
    exact hΔ x ((i ≫ f).left z)
  change Function.Bijective (fun s ↦
    LocallyConstant.comap (graph W.unop f).base.hom (β W s))
  have he : (fun s ↦ LocallyConstant.comap (graph W.unop f).base.hom (β W s)) =
      (fun s ↦ γ s) := funext heq
  rw [he]
  exact γ.bijective

set_option backward.isDefEq.respectTransparency false in
/-- Naturality evaluates a locally presented section at its constant label. -/
private theorem evaluation_of_local_presentation
    {V : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (Λ)))
    (β : ∀ W : V.Etaleᵒᵖ, F.obj.obj W →ₗ[Λ]
      LocallyConstant (c.sectionSpace W.unop) (F.obj.obj (op c.sectionObject)))
    (hβ : ∀ (W W' : V.Etaleᵒᵖ) (f : W ⟶ W') (s : F.obj.obj W)
        (x : c.sectionSpace W'.unop),
      β W' (F.obj.map f s) x = β W s (c.sectionRestriction f.unop x))
    (hΔ : ∀ (s : F.obj.obj (op c.sectionObject)) (y : c.P),
      β (op c.sectionObject) s
        (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp) y) = s)
    (W : V.Etaleᵒᵖ) (s : F.obj.obj W)
    (T : V.Etale) (p : T ⟶ W.unop) (q : T ⟶ c.sectionObject) (y : T.left)
    (a : F.obj.obj (op c.sectionObject))
    (hs : F.obj.map p.op s = F.obj.map q.op a) :
    β W s (pullback.lift p.left q.left
      ((MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q).symm) y) = a := by
  let d : T.left ⟶ c.sectionSpace T :=
    pullback.lift (𝟙 _) q.left (by simpa using (MorphismProperty.Over.w q).symm)
  have hp : d ≫ c.sectionRestriction p =
      pullback.lift p.left q.left
        ((MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q).symm) := by
    apply pullback.hom_ext <;>
      simp only [d, Scheme.GaloisCover.sectionRestriction, Scheme.GaloisCover.sectionObject,
        Scheme.Etale.mk, MorphismProperty.Over.mk, pullback.map,
        pullback.lift_fst_assoc, pullback.lift_fst,
        pullback.lift_snd, Category.id_comp, Category.comp_id, Category.assoc]
  have hq : d ≫ c.sectionRestriction q =
      q.left ≫ pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp) := by
    apply pullback.hom_ext <;>
      simp only [d, Scheme.GaloisCover.sectionRestriction, Scheme.GaloisCover.sectionObject,
        Scheme.Etale.mk, MorphismProperty.Over.mk, pullback.map,
        pullback.lift_fst_assoc, pullback.lift_fst,
        pullback.lift_snd, Category.id_comp, Category.comp_id, Category.assoc]
  calc
    _ = β (op T) (F.obj.map p.op s) (d y) := by
      rw [hβ]
      change β W s _ = β W s ((d ≫ c.sectionRestriction p) y)
      rw [hp]
      rfl
    _ = β (op T) (F.obj.map q.op a) (d y) := by rw [hs]
    _ = a := by
      rw [hβ]
      change β (op c.sectionObject) a ((d ≫ c.sectionRestriction q) y) = a
      rw [hq, Scheme.Hom.comp_apply]
      exact hΔ a (q.left y)

set_option backward.isDefEq.respectTransparency false in
/-- A natural ordinary evaluation normalized on the diagonal is deck-equivariant.
Fixed-cover adaptation to arbitrary modules. -/
private theorem Scheme.GaloisCover.ordinarySectionEvaluation_equivariantOver
    {V : Scheme.{u}} [ConnectedSpace V] (Λ : Type (u + 1)) [CommRing Λ]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (Λ)))
    (A : ModuleCat.{u + 1} (Λ))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (Λ)].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (Λ))).obj A))
    (β : ∀ W : V.Etaleᵒᵖ, F.obj.obj W →ₗ[Λ]
      LocallyConstant (c.sectionSpace W.unop) (F.obj.obj (op c.sectionObject)))
    (hβ : ∀ (W W' : V.Etaleᵒᵖ) (f : W ⟶ W') (s : F.obj.obj W)
        (x : c.sectionSpace W'.unop),
      β W' (F.obj.map f s) x = β W s (c.sectionRestriction f.unop x))
    (hΔ : ∀ (s : F.obj.obj (op c.sectionObject)) (y : c.P),
      β (op c.sectionObject) s
        (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp) y) = s) :
    ∀ (W : V.Etaleᵒᵖ) (s : F.obj.obj W) (g : P) (x : c.sectionSpace W.unop),
      β W s (c.sectionAction W.unop g x) =
        (Scheme.GaloisCover.sectionRepresentationOver Λ c F).ρ g (β W s x) := by
  intro W s g x
  have := c.etale
  let U : V.Etale := Etale.mk (pullback.fst W.unop.hom c.π ≫ W.unop.hom)
  let pU : U ⟶ W.unop :=
    MorphismProperty.Over.homMk (pullback.fst W.unop.hom c.π) rfl
  let qU : U ⟶ c.sectionObject :=
    MorphismProperty.Over.homMk (pullback.snd W.unop.hom c.π) pullback.condition.symm
  let t := F.obj.map pU.op s
  let dU : U.left ⟶ c.sectionSpace U :=
    pullback.lift (𝟙 _) qU.left (by simpa using (MorphismProperty.Over.w qU).symm)
  let f : LocallyConstant U.left (F.obj.obj (op c.sectionObject)) :=
    LocallyConstant.comap dU.base.hom (β (op U) t)
  let O : U.left.Opens := ⟨{z | f z = f x}, f.isLocallyConstant.isOpen_fiber _⟩
  let T : V.Etale := Etale.mk (O.ι ≫ U.hom)
  let i : T ⟶ U := MorphismProperty.Over.homMk O.ι rfl
  let p : T ⟶ W.unop := i ≫ pU
  let q : T ⟶ c.sectionObject := i ≫ qU
  let y : T.left := ⟨x, rfl⟩
  let a : F.obj.obj (op c.sectionObject) := f x
  have hx : pullback.lift p.left q.left
      ((MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q).symm) y = x := by
    have hm : pullback.lift p.left q.left
        ((MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q).symm) = O.ι := by
      apply pullback.hom_ext <;>
        simp only [Scheme.GaloisCover.sectionObject, Scheme.Etale.mk,
          MorphismProperty.Over.mk, pullback.lift_fst, pullback.lift_snd]
      all_goals rfl
    rw [hm]
    rfl
  have hs : F.obj.map p.op s = F.obj.map q.op a := by
    apply (c.ordinaryGraphEvaluation_bijectiveOver Λ P F A h β hβ hΔ (op T) q).1
    apply LocallyConstant.ext
    intro z
    let d : T.left ⟶ c.sectionSpace T :=
      pullback.lift (𝟙 _) q.left (by simpa using (MorphismProperty.Over.w q).symm)
    change β (op T) (F.obj.map p.op s) (d z) =
      β (op T) (F.obj.map q.op a) (d z)
    have hm : d ≫ c.sectionRestriction i = O.ι ≫ dU := by
      apply pullback.hom_ext <;>
        simp only [d, Scheme.GaloisCover.sectionRestriction, dU, q, i,
          pullback.map, pullback.lift_fst_assoc, pullback.lift_fst,
          pullback.lift_snd, Category.assoc, Category.id_comp, Category.comp_id]
      all_goals rfl
    have hleft : β (op T) (F.obj.map p.op s) (d z) = a := by
      change β (op T) (F.obj.map (pU.op ≫ i.op) s) (d z) = a
      rw [CategoryTheory.Functor.map_comp, ModuleCat.comp_apply, hβ]
      change β (op U) t ((d ≫ c.sectionRestriction i) z) = a
      rw [hm, Scheme.Hom.comp_apply]
      exact z.property
    have hright : β (op T) (F.obj.map q.op a) (d z) = a := by
      exact evaluation_of_local_presentation Λ c F β hβ hΔ (op T)
        (F.obj.map q.op a) T (𝟙 T) q z a (by simp)
    exact hleft.trans hright.symm
  have ha : β W s x = a := by
    rw [← hx]
    exact evaluation_of_local_presentation Λ c F β hβ hΔ W s T p q y a hs
  let q' : T ⟶ c.sectionObject := q ≫ c.sectionDeck g
  let b : F.obj.obj (op c.sectionObject) := F.obj.map (c.sectionDeck g⁻¹).op a
  have hd : c.sectionDeck g ≫ c.sectionDeck g⁻¹ = 𝟙 _ := by
    apply Scheme.EtaleTorsor.etaleHom_ext
    change c.smul ⟨g⟩ ≫ c.smul ⟨g⁻¹⟩ = 𝟙 _
    rw [← c.mul_smul]
    change c.smul ((⟨g⟩ : ULift.{u + 1} P)⁻¹ * ⟨g⟩) = 𝟙 _
    rw [inv_mul_cancel, c.one_smul]
  have hs' : F.obj.map p.op s = F.obj.map q'.op b := by
    rw [hs]
    dsimp [q', b]
    rw [Functor.map_comp]
    change F.obj.map q.op a =
      F.obj.map q.op (F.obj.map (c.sectionDeck g).op
        (F.obj.map (c.sectionDeck g⁻¹).op a))
    have hm : (c.sectionDeck g⁻¹).op ≫ (c.sectionDeck g).op = 𝟙 _ := by
      rw [← op_comp, hd, op_id]
    have he : F.obj.map (c.sectionDeck g).op
        (F.obj.map (c.sectionDeck g⁻¹).op a) = a := by
      rw [← ModuleCat.comp_apply, ← Functor.map_comp, hm, CategoryTheory.Functor.map_id]
      rfl
    rw [he]
  have hx' : pullback.lift p.left q'.left
      ((MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q').symm) y =
      c.sectionAction W.unop g x := by
    have hm : pullback.lift p.left q'.left
        ((MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q').symm) =
        pullback.lift p.left q.left
          ((MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q).symm) ≫
          c.sectionAction W.unop g := by
      apply pullback.hom_ext <;>
        simp [Scheme.GaloisCover.sectionAction, q', Scheme.GaloisCover.sectionDeck,
          Scheme.GaloisCover.sectionObject, Scheme.Etale.mk, MorphismProperty.Over.mk]
      rfl
    rw [hm, Scheme.Hom.comp_apply, hx]
    rfl
  rw [← hx']
  rw [evaluation_of_local_presentation Λ c F β hβ hΔ W s T p q' y b hs', ha]
  rfl

/-- Evaluation on the chosen graph determines an equivariant locally constant function. -/
private theorem Scheme.GaloisCover.graphEvaluation_injectiveOver
    {V : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (N : Rep.{u + 1} Λ P) (W : V.Etale)
    (f : W ⟶ c.sectionObject) :
    Function.Injective (fun s : c.equivariantSectionsOver Λ N W ↦
      LocallyConstant.comap
        (pullback.lift (f := W.hom) (g := c.π) (𝟙 W.left) f.left
          (by simpa using (MorphismProperty.Over.w f).symm)).base.hom s.val) := by
  let D := Sigma.desc fun g : ULift.{u + 1} P ↦
    pullback.lift (f := c.π) (g := c.π) (c.smul g) (𝟙 c.P) (by simp [c.smul_π])
  have : IsIso D := c.isIso_sigmaDesc
  let E := Sigma.desc fun g : ULift.{u + 1} P ↦
    pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (c.smul g) (by simp [c.smul_π])
  have hE : E = D ≫ (pullbackSymmetry c.π c.π).hom := by
    apply Sigma.hom_ext
    intro g
    apply pullback.hom_ext <;> simp [E, D]
  have : IsIso E := by rw [hE]; infer_instance
  have hw : f.left ≫ c.π = W.hom := MorphismProperty.Over.w f
  let T := Sigma.desc fun g : ULift.{u + 1} P ↦
    pullback.lift (f := f.left ≫ c.π) (g := c.π) (𝟙 W.left)
      (f.left ≫ c.smul g) (by simp [c.smul_π])
  have : IsIso T := FinitaryPreExtensive.isIso_sigmaDesc_lift_comp
    c.π c.smul c.smul_π f.left
  let graph : W.left ⟶ c.sectionSpace W :=
    pullback.lift (𝟙 W.left) f.left hw.symm
  let S : (∐ fun _ : ULift.{u + 1} P ↦ W.left) ⟶ c.sectionSpace W :=
    Sigma.desc fun g ↦ graph ≫ c.sectionAction W g.down
  have hS : IsIso S := by
    have hST : S = T ≫ (pullback.congrHom hw rfl).hom := by
      apply Sigma.hom_ext
      intro g
      apply pullback.hom_ext <;>
        simp [S, T, graph, Scheme.GaloisCover.sectionAction, pullback.congrHom]
    rw [hST]
    infer_instance
  have hs : Function.Surjective S := by
    have := hS
    exact Surjective.surj (f := S)
  intro a b hab
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  obtain ⟨z, hz⟩ := hs x
  obtain ⟨g, w, hwz⟩ := (sigmaOpenCover fun _ : ULift.{u + 1} P ↦ W.left).exists_eq z
  have hpoint : c.sectionAction W g.down (graph w) = x := by
    have ht := congrArg (fun k ↦ S k) hwz
    have hi : Sigma.ι (fun _ : ULift.{u + 1} P ↦ W.left) g ≫ S =
        graph ≫ c.sectionAction W g.down := by simp [S]
    rw [← Scheme.Hom.comp_apply, ← hi, Scheme.Hom.comp_apply]
    exact ht.trans hz
  rw [← hpoint, a.property, b.property]
  congr 1
  exact congrArg (fun t : LocallyConstant W.left N.V ↦ t w) hab

/-- Normalized evaluation is bijective on an etale object with a map to the torsor. -/
private theorem Scheme.GaloisCover.sectionEvaluation_bijective_of_sectionOver
    {V : Scheme.{u}} [ConnectedSpace V] (Λ : Type (u + 1)) [CommRing Λ]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (Λ)))
    (A : ModuleCat.{u + 1} (Λ))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (Λ)].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (Λ))).obj A))
    (α : F.obj ⟶ Scheme.GaloisCover.sectionRepresentationPresheafOver Λ c F)
    (hα : Scheme.GaloisCover.SectionEvaluationNormalizedOver Λ c F α) (W : V.Etaleᵒᵖ)
    (f : W.unop ⟶ c.sectionObject) :
    Function.Bijective (α.app W) := by
  have hgraph := c.graphEvaluation_injectiveOver Λ
    (Scheme.GaloisCover.sectionRepresentationOver Λ c F) W.unop f
  let β (T : V.Etaleᵒᵖ) : F.obj.obj T →ₗ[Λ]
      LocallyConstant (c.sectionSpace T.unop) (F.obj.obj (Opposite.op c.sectionObject)) :=
    { toFun s := (α.app T s).val
      map_add' a b := by
        change (α.app T (a + b)).val = _
        rw [map_add]
        rfl
      map_smul' r a := by
        change (α.app T (r • a)).val = _
        rw [map_smul]
        rfl }
  have hβ (T T' : V.Etaleᵒᵖ) (g : T ⟶ T') (s : F.obj.obj T)
      (x : c.sectionSpace T'.unop) :
      β T' (F.obj.map g s) x = β T s (c.sectionRestriction g.unop x) := by
    have hn := ConcreteCategory.congr_hom (α.naturality g) s
    exact congrArg (fun t : c.equivariantSectionsOver Λ
      (Scheme.GaloisCover.sectionRepresentationOver Λ c F) T'.unop ↦
      t.val x) hn
  have hcomp := c.ordinaryGraphEvaluation_bijectiveOver Λ P F A h β hβ hα W f
  exact hcomp.of_comp_left hgraph

/-- There is a normalized evaluation morphism into equivariant locally constant functions.
This asserts existence and naturality of the evaluation map, not its bijectivity. -/
private theorem Scheme.GaloisCover.exists_sectionEvaluationOver
    {V : Scheme.{u}} [ConnectedSpace V] (Λ : Type (u + 1)) [CommRing Λ]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (Λ)))
    (A : ModuleCat.{u + 1} (Λ))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (Λ)].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (Λ))).obj A)) :
    ∃ α : F.obj ⟶ Scheme.GaloisCover.sectionRepresentationPresheafOver Λ c F,
      Scheme.GaloisCover.SectionEvaluationNormalizedOver Λ c F α := by
  obtain ⟨β, hβ, hΔ⟩ := c.exists_ordinarySectionEvaluationOver Λ P F A h
  have heq := c.ordinarySectionEvaluation_equivariantOver Λ P F A h β hβ hΔ
  let α : F.obj ⟶ Scheme.GaloisCover.sectionRepresentationPresheafOver Λ c F :=
    { app := fun W ↦ ModuleCat.ofHom
        { toFun := fun s ↦ ⟨β W s, heq W s⟩
          map_add' := by intro s t; apply Subtype.ext; exact map_add (β W) s t
          map_smul' := by intro r s; apply Subtype.ext; exact map_smul (β W) r s }
      naturality := by
        intro W W' f
        ext s
        apply Subtype.ext
        apply LocallyConstant.ext
        intro x
        exact hβ W W' f s x }
  exact ⟨α, hΔ⟩

namespace Scheme.GaloisCover

/-- Descent along a connected finite torsor realizes module representations as sheaves,
recovers a module sheaf trivialized by the torsor. The associated functor is already
constructed; its pullback and coefficient comparisons are proved separately.
This statement constructs no filtration and makes no Sylow or degree assertion. -/
theorem exists_finiteRing_module_descent
    {X : Scheme.{u}} [ConnectedSpace X]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) X) [ConnectedSpace c.P]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (A : ModuleCat.{u + 1} Λ)
    (hF : Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) c.π).obj F ≅
      (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj A)) :
    ∃ M : Rep.{u + 1} Λ P,
      Nonempty ((c.associatedModuleFunctorOver Λ).obj M ≅ F) := by
  classical
  have := c.etale
  have := c.surjective
  obtain ⟨α, hα⟩ := c.exists_sectionEvaluationOver Λ P F A hF
  have hlocal (T : X.Etale) (f : T ⟶ c.sectionObject) :
      Function.Bijective (α.app (Opposite.op T)) :=
    c.sectionEvaluation_bijective_of_sectionOver Λ P F A hF α hα (Opposite.op T) f
  have hcover (T : X.Etale) :
      let U : X.Etale := Etale.mk (pullback.fst T.hom c.π ≫ T.hom)
      let ι : U ⟶ T := MorphismProperty.Over.homMk (pullback.fst T.hom c.π) rfl
      Sieve.ofArrows (fun _ : PUnit.{1} ↦ U) (fun _ ↦ ι) ∈ X.smallEtaleTopology T := by
    dsimp
    apply (ofArrows_mem_smallEtaleTopology_iff _).2
    simp only [Set.iUnion_const]
    exact Set.range_eq_univ.2 (Surjective.surj (f := pullback.fst T.hom c.π))
  have : Presheaf.IsLocallyInjective X.smallEtaleTopology α := by
    constructor
    intro T x y hxy
    let U : X.Etale := Etale.mk (pullback.fst T.unop.hom c.π ≫ T.unop.hom)
    let ι : U ⟶ T.unop :=
      MorphismProperty.Over.homMk (pullback.fst T.unop.hom c.π) rfl
    let f : U ⟶ c.sectionObject :=
      MorphismProperty.Over.homMk (pullback.snd T.unop.hom c.π) pullback.condition.symm
    apply X.smallEtaleTopology.superset_covering _ (hcover T.unop)
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    apply (hlocal U f).1
    change α.app (Opposite.op U) (F.obj.map ι.op x) = α.app (Opposite.op U) (F.obj.map ι.op y)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    exact congrArg ((sectionRepresentationPresheafOver Λ c F).map ι.op) hxy
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology α := by
    constructor
    intro T t
    let U : X.Etale := Etale.mk (pullback.fst T.hom c.π ≫ T.hom)
    let ι : U ⟶ T := MorphismProperty.Over.homMk (pullback.fst T.hom c.π) rfl
    let f : U ⟶ c.sectionObject :=
      MorphismProperty.Over.homMk (pullback.snd T.hom c.π) pullback.condition.symm
    apply X.smallEtaleTopology.superset_covering _ (hcover T)
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    exact (hlocal U f).2 ((sectionRepresentationPresheafOver Λ c F).map ι.op t)
  let S := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  have hW : X.smallEtaleTopology.W α := X.smallEtaleTopology.W_of_isLocallyBijective α
  have : IsIso (S.map α) := (X.smallEtaleTopology.W_iff α).mp hW
  refine ⟨sectionRepresentationOver Λ c F, ⟨?_⟩⟩
  exact (asIso (S.map α)).symm ≪≫
    asIso ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app F)

end Scheme.GaloisCover
end AlgebraicGeometry
