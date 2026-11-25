/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OverlapConjugateRestriction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import WeilConjectures.AlgebraicGeometry.OverlapModelChartFactorization
import WeilConjectures.AlgebraicGeometry.OverlapBaseChangeFormula

/-! # Restricting a stage morphism through a commutative model diagram

Source: Stacks Project, Tags 0095 and 0096; Tag 01ZR (2), first proof.
(blueprint: lem-pc-overlap-stage-model-restriction). -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
namespace AlgebraicGeometry
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Transport of any stage morphism through the model square.
This is transport of an arbitrary tensor compatibility equation, independent of
a limit module, its component isomorphisms, or a prescribed descent transition.
Source: Stacks Project, Tags 0095 and 0096; Tag 01ZR (2), first proof.
(blueprint: lem-pc-overlap-stage-model-restriction).

Proof: Substitute the four comparison equalities. Expand the stage comparison
and the two direct restriction comparisons.
Use functoriality to separate the three factors defining the stage morphism.
Naturality of the composition comparisons moves the central morphism alpha
past them. The equality z ≫ p₀ = l ≫ d identifies the two inverse-image
routes from the iterated overlap to Hₖ. For each chart, the associativity
pentagon and the stated projection equations identify the exterior
composition comparisons. Convert tensor pullbacks to abstract pullbacks
using the unique adjunction comparison. The comparison for the composite
is compatible with the two individual comparisons: apply conjugateIsoEquiv
to both sides, where both become the same pushforward composition map.
The resulting middle factors are σ_F, the tensor pullback of alpha, and
σ_G inverse. Postcompose the supplied compatibility equation by σ_G inverse
and cancel σ_G to identify this middle morphism with theta. Substitute the
equation naming phi. Cancel the remaining source and target comparisons. No
faithfulness or finiteness is used; all arrows may be identities and any
overlap or module may be empty or zero. -/
theorem overlap_stage_model_restriction
    {X Y Z H₀ Hₖ Hlim : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (a b : U.I₀)
    (q₀ : Hₖ ⟶ H₀) (p₀ : Hlim ⟶ Hₖ) (t₀ : Hlim ⟶ H₀) (h₀ : p₀ ≫ q₀ = t₀)
    (r₀a : H₀ ⟶ U.X a) (r₀b : H₀ ⟶ U.X b)
    (d : pullback ((U.pullback₁ q).f a) ((U.pullback₁ q).f b) ⟶ Hₖ)
    (ha : Hlim ⟶ (U.pullback₁ t).X a) (hb : Hlim ⟶ (U.pullback₁ t).X b)
    (hka : (d ≫ q₀) ≫ r₀a = pullback.fst _ _ ≫ U.pullbackHom q a)
    (hkb : (d ≫ q₀) ≫ r₀b = pullback.snd _ _ ≫ U.pullbackHom q b)
    (ka : Hlim ⟶ U.X a) (kb : Hlim ⟶ U.X b)
    (hla : t₀ ≫ r₀a = ka) (hlb : t₀ ≫ r₀b = kb)
    (hda : ha ≫ U.pullbackHom t a = ka)
    (hdb : hb ≫ U.pullbackHom t b = kb)
    (z : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ Hlim)
    (hza : z ≫ ha = pullback.fst _ _ ≫ overlapIteratedChartHom U q p t h a)
    (hzb : z ≫ hb = pullback.snd _ _ ≫ overlapIteratedChartHom U q p t h b)
    (hz : z ≫ p₀ =
      pullback.lift
        (pullback.fst _ _ ≫ Scheme.Cover.pullbackHom (U.pullback₁ q) p a)
        (pullback.snd _ _ ≫ Scheme.Cover.pullbackHom (U.pullback₁ q) p b) (by
          rw [Category.assoc, Category.assoc, Scheme.Cover.pullbackHom_map,
            Scheme.Cover.pullbackHom_map, ← Category.assoc, ← Category.assoc,
            pullback.condition]) ≫ d) :
    let F := (Scheme.Modules.pullback r₀a).obj (N a)
    let G := (Scheme.Modules.pullback r₀b).obj (N b)
    let σ := Scheme.Modules.tensorPullbackCompositionIso p₀ q₀ t₀ h₀
    let canonicalτa := overlapDirectModelComparison t₀ r₀a ka ha
      (U.pullbackHom t a) hla hda (N a)
    let canonicalτb := overlapDirectModelComparison t₀ r₀b kb hb
      (U.pullbackHom t b) hlb hdb (N b)
    let canonicalsa := overlapStageModelComparison d q₀ r₀a
      (pullback.fst _ _) (U.pullbackHom q a) hka (N a)
    let canonicalsb := overlapStageModelComparison d q₀ r₀b
      (pullback.snd _ _) (U.pullbackHom q b) hkb (N b)
    ∀ (τa : (Scheme.Modules.tensorPullback t₀).obj F ≅
        (Scheme.Modules.pullback ha).obj
          ((Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a)))
      (τb : (Scheme.Modules.tensorPullback t₀).obj G ≅
        (Scheme.Modules.pullback hb).obj
          ((Scheme.Modules.pullback (U.pullbackHom t b)).obj (N b)))
      (sa : (Scheme.Modules.pullback d).obj ((Scheme.Modules.tensorPullback q₀).obj F) ≅
        (Scheme.Modules.pullback
          (pullback.fst ((U.pullback₁ q).f a) ((U.pullback₁ q).f b))).obj
          ((Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a)))
      (sb : (Scheme.Modules.pullback d).obj ((Scheme.Modules.tensorPullback q₀).obj G) ≅
        (Scheme.Modules.pullback
          (pullback.snd ((U.pullback₁ q).f a) ((U.pullback₁ q).f b))).obj
          ((Scheme.Modules.pullback (U.pullbackHom q b)).obj (N b))),
      τa = canonicalτa → τb = canonicalτb → sa = canonicalsa → sb = canonicalsb →
    let ξa := overlapDirectRestrictionIso U q p t h N a b a ha z
      (pullback.fst _ _) hza ((Scheme.Modules.tensorPullback t₀).obj F) τa
    let ξb := overlapDirectRestrictionIso U q p t h N a b b hb z
      (pullback.snd _ _) hzb ((Scheme.Modules.tensorPullback t₀).obj G) τb
    ∀ α : (Scheme.Modules.tensorPullback q₀).obj F ⟶
        (Scheme.Modules.tensorPullback q₀).obj G,
    ∀ θ : (Scheme.Modules.tensorPullback t₀).obj F ⟶
        (Scheme.Modules.tensorPullback t₀).obj G,
      σ.hom.app F ≫ (Scheme.Modules.tensorPullback p₀).map α = θ ≫ σ.hom.app G →
    ∀ φ : (Scheme.Modules.pullback
        (pullback.fst ((U.pullback₁ q).f a) ((U.pullback₁ q).f b))).obj
        ((Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a)) ⟶
      (Scheme.Modules.pullback
        (pullback.snd ((U.pullback₁ q).f a) ((U.pullback₁ q).f b))).obj
        ((Scheme.Modules.pullback (U.pullbackHom q b)).obj (N b)),
      φ = sa.inv ≫ (Scheme.Modules.pullback d).map α ≫ sb.hom →
      modulesPseudofunctor.overlapPairBaseChangeHom
        ((U.pullback₁ q).f a) ((U.pullback₁ q).f b) p
        (Scheme.Cover.pullbackHom (U.pullback₁ q) p a)
        (Scheme.Cover.pullbackHom (U.pullback₁ q) p b)
        (((U.pullback₁ q).pullback₁ p).f a) (((U.pullback₁ q).pullback₁ p).f b)
        (Scheme.Cover.pullbackHom_map (U.pullback₁ q) p a)
        (Scheme.Cover.pullbackHom_map (U.pullback₁ q) p b)
        ((Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a))
        ((Scheme.Modules.pullback (U.pullbackHom q b)).obj (N b))
        φ = ξa.inv ≫ (Scheme.Modules.pullback z).map θ ≫ ξb.hom := by
  dsimp only
  intro τa τb sa sb hτa hτb hsa hsb
  subst τa τb sa sb
  intro α θ hθ φ hφ
  let F := (Scheme.Modules.pullback r₀a).obj (N a)
  let G := (Scheme.Modules.pullback r₀b).obj (N b)
  let σ := Scheme.Modules.tensorPullbackCompositionIso p₀ q₀ t₀ h₀
  let sa' := overlapStageModelComparison d q₀ r₀a
    (pullback.fst _ _) (U.pullbackHom q a) hka (N a)
  let sb' := overlapStageModelComparison d q₀ r₀b
    (pullback.snd _ _) (U.pullbackHom q b) hkb (N b)
  let ξa := overlapDirectRestrictionIso U q p t h N a b a ha z
    (pullback.fst _ _) hza ((Scheme.Modules.tensorPullback t₀).obj F)
    (overlapDirectModelComparison t₀ r₀a ka ha (U.pullbackHom t a) hla hda (N a))
  let ξb := overlapDirectRestrictionIso U q p t h N a b b hb z
    (pullback.snd _ _) hzb ((Scheme.Modules.tensorPullback t₀).obj G)
    (overlapDirectModelComparison t₀ r₀b kb hb (U.pullbackHom t b) hlb hdb (N b))
  generalize hl : pullback.lift
    (pullback.fst _ _ ≫ Scheme.Cover.pullbackHom (U.pullback₁ q) p a)
    (pullback.snd _ _ ≫ Scheme.Cover.pullbackHom (U.pullback₁ q) p b) (by
      rw [Category.assoc, Category.assoc, Scheme.Cover.pullbackHom_map,
        Scheme.Cover.pullbackHom_map, ← Category.assoc, ← Category.assoc,
        pullback.condition]) = l at hz
  have hlF : l ≫ pullback.fst ((U.pullback₁ q).f a) ((U.pullback₁ q).f b) =
      pullback.fst _ _ ≫ Scheme.Cover.pullbackHom (U.pullback₁ q) p a := by
    rw [← hl]
    exact pullback.lift_fst _ _ _
  have hlS : l ≫ pullback.snd ((U.pullback₁ q).f a) ((U.pullback₁ q).f b) =
      pullback.snd _ _ ≫ Scheme.Cover.pullbackHom (U.pullback₁ q) p b := by
    rw [← hl]
    exact pullback.lift_snd _ _ _
  let E := Functor.isoWhiskerRight (overlapAdjunctionComparison p₀)
      (Scheme.Modules.pullback z) ≪≫
    Scheme.Modules.pullbackComp z p₀ ≪≫ Scheme.Modules.pullbackCongr hz ≪≫
    (Scheme.Modules.pullbackComp l d).symm
  let Ba := (pullbackCompOfEq l (pullback.fst _ _) _ hlF
      ((Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a))) ≪≫
    ((Scheme.Modules.pullbackComp (pullback.fst _ _)
      (Scheme.Cover.pullbackHom (U.pullback₁ q) p a)).app _).symm
  let Bb := (pullbackCompOfEq l (pullback.snd _ _) _ hlS
      ((Scheme.Modules.pullback (U.pullbackHom q b)).obj (N b))) ≪≫
    ((Scheme.Modules.pullbackComp (pullback.snd _ _)
      (Scheme.Cover.pullbackHom (U.pullback₁ q) p b)).app _).symm
  have hξa := overlap_model_chart_factorization q₀ p₀ t₀ h₀ r₀a d
    (pullback.fst _ _) (U.pullbackHom q a) hka ha (U.pullbackHom t a) ka hla hda
    z l hz (pullback.fst _ _) (Scheme.Cover.pullbackHom (U.pullback₁ q) p a)
    (overlapIteratedChartHom U q p t h a) hlF
    (pullback.lift_snd _ _ _) hza (N a)
  have hξb := overlap_model_chart_factorization q₀ p₀ t₀ h₀ r₀b d
    (pullback.snd _ _) (U.pullbackHom q b) hkb hb (U.pullbackHom t b) kb hlb hdb
    z l hz (pullback.snd _ _) (Scheme.Cover.pullbackHom (U.pullback₁ q) p b)
    (overlapIteratedChartHom U q p t h b) hlS
    (pullback.lift_snd _ _ _) hzb (N b)
  change ξa = (Scheme.Modules.pullback z).mapIso (σ.app F) ≪≫
    E.app ((Scheme.Modules.tensorPullback q₀).obj F) ≪≫
    (Scheme.Modules.pullback l).mapIso sa' ≪≫ Ba at hξa
  change ξb = (Scheme.Modules.pullback z).mapIso (σ.app G) ≪≫
    E.app ((Scheme.Modules.tensorPullback q₀).obj G) ≪≫
    (Scheme.Modules.pullback l).mapIso sb' ≪≫ Bb at hξb
  let bc := modulesPseudofunctor.overlapPairBaseChangeHom
        ((U.pullback₁ q).f a) ((U.pullback₁ q).f b) p
        (Scheme.Cover.pullbackHom (U.pullback₁ q) p a)
        (Scheme.Cover.pullbackHom (U.pullback₁ q) p b)
        (((U.pullback₁ q).pullback₁ p).f a) (((U.pullback₁ q).pullback₁ p).f b)
        (Scheme.Cover.pullbackHom_map (U.pullback₁ q) p a)
        (Scheme.Cover.pullbackHom_map (U.pullback₁ q) p b)
        ((Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a))
        ((Scheme.Modules.pullback (U.pullbackHom q b)).obj (N b))
        φ
  have hBC := overlap_base_change_formula ((U.pullback₁ q).f a) ((U.pullback₁ q).f b) p
      (Scheme.Cover.pullbackHom (U.pullback₁ q) p a)
      (Scheme.Cover.pullbackHom (U.pullback₁ q) p b)
      (((U.pullback₁ q).pullback₁ p).f a) (((U.pullback₁ q).pullback₁ p).f b)
      (Scheme.Cover.pullbackHom_map (U.pullback₁ q) p a)
      (Scheme.Cover.pullbackHom_map (U.pullback₁ q) p b)
      ((Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a))
      ((Scheme.Modules.pullback (U.pullbackHom q b)).obj (N b)) φ l hlF hlS
  dsimp only at hBC
  change σ.hom.app F ≫ (Scheme.Modules.tensorPullback p₀).map α =
    θ ≫ σ.hom.app G at hθ
  have hα : (Scheme.Modules.tensorPullback p₀).map α =
      σ.inv.app F ≫ θ ≫ σ.hom.app G := by
    rw [← hθ]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  have hαz := congrArg (fun f ↦ (Scheme.Modules.pullback z).map f) hα
  simp only [Functor.map_comp] at hαz
  change bc = ξa.inv ≫ (Scheme.Modules.pullback z).map θ ≫ ξb.hom
  dsimp only [bc]
  rw [hBC, hφ, Functor.map_comp, Functor.map_comp, hξa, hξb]
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Iso.app_inv, Iso.app_hom, Category.assoc]
  rw [← reassoc_of% hαz]
  have hE := NatIso.naturality_1 E α
  simp only [Functor.comp_map] at hE
  conv_rhs =>
    arg 2
    arg 2
    rw [reassoc_of% hE]
  conv_rhs =>
    dsimp only [Ba, Bb, sa', sb']
    simp (config := { dsimp := false }) only [Iso.trans_inv, Iso.trans_hom,
      Iso.symm_inv, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Category.assoc]
  rfl

end
end AlgebraicGeometry
