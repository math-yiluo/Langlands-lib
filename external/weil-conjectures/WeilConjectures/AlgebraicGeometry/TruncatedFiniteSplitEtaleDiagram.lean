/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TruncatedEtaleMatchingData
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.LimitsOver

/-!
# Finite split truncated étale diagrams without matching covers

Source: blueprint corollary-cohomology-pro-etale-affine, Detailed form proof,
finite simplicial data and matching-cover sentences.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A specified finite splitting of a truncated étale diagram.
Source: blueprint finite-hypercover-descent, nondegenerate summands paragraph.
(auxiliary; not a blueprint node) -/
structure TruncatedFiniteSplitEtaleSplitting (X : Scheme.{u}) (r : ℕ)
    (S : SimplicialObject.Truncated X.Etale r) where
  N : Fin (r + 1) → X.Etale
  inclusion : ∀ n, N n ⟶ S.obj (op ⟨SimplexCategory.mk n.val,
    Nat.le_of_lt_succ n.isLt⟩)
  splitting : ∀ Δ : (SimplexCategory.Truncated r)ᵒᵖ,
    IsColimit (Cofan.mk (S.obj Δ)
      (fun a : Σ m : Fin (r + 1),
          {α : Δ.unop.obj ⟶ SimplexCategory.mk m.val // Epi α} ↦
        inclusion a.1 ≫ S.map (SimplexCategory.Truncated.Hom.tr a.2.val Δ.unop.property
          (Nat.le_of_lt_succ a.1.isLt)).op))
  N_qcqs : ∀ n, CompactSpace (N n).left ∧ QuasiSeparatedSpace (N n).left



/-- The finite split simplicial data of a truncated hypercover, before imposing matching
covers. Source: blueprint corollary-cohomology-pro-etale-affine, finite-data paragraph.
(auxiliary; not a blueprint node) -/
structure TruncatedFiniteSplitEtaleDiagram (X : Scheme.{u}) (r : ℕ) where
  simplicial : SimplicialObject.Truncated X.Etale r
  N : Fin (r + 1) → X.Etale
  inclusion : ∀ n, N n ⟶ simplicial.obj (op ⟨SimplexCategory.mk n.val,
    Nat.le_of_lt_succ n.isLt⟩)
  splitting : ∀ Δ : (SimplexCategory.Truncated r)ᵒᵖ,
    IsColimit (Cofan.mk (simplicial.obj Δ)
      (fun a : Σ m : Fin (r + 1),
          {α : Δ.unop.obj ⟶ SimplexCategory.mk m.val // Epi α} ↦
        inclusion a.1 ≫ simplicial.map (SimplexCategory.Truncated.Hom.tr a.2.val Δ.unop.property
          (Nat.le_of_lt_succ a.1.isLt)).op))
  finite_each_degree : ∀ n, ∃ (k : ℕ) (V : Fin k → X.Etale)
    (ι : ∀ i, V i ⟶ N n),
    Nonempty (IsColimit (Cofan.mk (N n) ι)) ∧
      ∀ i, CompactSpace (V i).left ∧ QuasiSeparatedSpace (V i).left ∧
        LocallyOfFinitePresentation (V i).hom ∧ QuasiCompact (V i).hom ∧
          QuasiSeparated (V i).hom

  matching : Fin (r + 1) → X.Etale
  projection : ∀ (n : Fin (r + 1)) (Δ : SimplexCategory.Truncated r),
    Δ.obj.len < n.val → (Δ.obj ⟶ SimplexCategory.mk n.val) →
      (matching n ⟶ simplicial.obj (op Δ))
  projection_naturality : ∀ (n : Fin (r + 1)) (Δ Δ' : SimplexCategory.Truncated r)
    (h : Δ.obj.len < n.val) (h' : Δ'.obj.len < n.val) (α : Δ' ⟶ Δ)
    (θ : Δ.obj ⟶ SimplexCategory.mk n.val),
    projection n Δ h θ ≫ simplicial.map α.op =
      projection n Δ' h' (α.hom ≫ θ)
  matching_universal : ∀ (n : Fin (r + 1)) (T : Over X)
    (p : ∀ (Δ : SimplexCategory.Truncated r), Δ.obj.len < n.val →
      (Δ.obj ⟶ SimplexCategory.mk n.val) →
        (T ⟶ (Scheme.Etale.forget X).obj (simplicial.obj (op Δ)))),
    (∀ (Δ Δ' : SimplexCategory.Truncated r)
      (h : Δ.obj.len < n.val) (h' : Δ'.obj.len < n.val) (α : Δ' ⟶ Δ)
      (θ : Δ.obj ⟶ SimplexCategory.mk n.val),
      p Δ h θ ≫ (Scheme.Etale.forget X).map (simplicial.map α.op) =
        p Δ' h' (α.hom ≫ θ)) →
    ∃! f : T ⟶ (Scheme.Etale.forget X).obj (matching n),
      ∀ (Δ : SimplexCategory.Truncated r) (h : Δ.obj.len < n.val)
        (θ : Δ.obj ⟶ SimplexCategory.mk n.val),
        f ≫ (Scheme.Etale.forget X).map (projection n Δ h θ) = p Δ h θ
  matchingMap : ∀ n : Fin (r + 1),
    simplicial.obj (op ⟨SimplexCategory.mk n.val, Nat.le_of_lt_succ n.isLt⟩) ⟶ matching n
  matchingMap_projection : ∀ (n : Fin (r + 1)) (Δ : SimplexCategory.Truncated r)
    (h : Δ.obj.len < n.val) (θ : Δ.obj ⟶ SimplexCategory.mk n.val),
    matchingMap n ≫ projection n Δ h θ =
      simplicial.map (SimplexCategory.Truncated.Hom.tr θ Δ.property
        (Nat.le_of_lt_succ n.isLt)).op
  matching_qcqs : ∀ n, CompactSpace (matching n).left ∧
    QuasiSeparatedSpace (matching n).left


namespace TruncatedFiniteSplitEtaleDiagram

/-- Attach the finite matching limits to a specified splitting. -/
noncomputable def ofSplitting {X : Scheme.{u}} [QuasiSeparatedSpace X] {r : ℕ}
    (S : SimplicialObject.Truncated X.Etale r)
    (T : TruncatedFiniteSplitEtaleSplitting X r S) (M : TruncatedEtaleMatchingData X r S) :
    TruncatedFiniteSplitEtaleDiagram X r where
  simplicial := S
  N := T.N
  inclusion := T.inclusion
  splitting := T.splitting
  finite_each_degree n :=
    ⟨1, fun _ ↦ T.N n, fun _ ↦ 𝟙 _,
      ⟨Cofan.isColimitMkOfUnique (Iso.refl (T.N n)) (Fin 1)⟩,
      fun _ ↦ ⟨(T.N_qcqs n).1, (T.N_qcqs n).2, inferInstance,
        @quasiCompact_of_compactSpace (T.N n).left X (T.N n).hom
          (T.N_qcqs n).1 inferInstance,
        @QuasiSeparated.of_quasiSeparatedSpace (T.N n).left X (T.N n).hom
          (T.N_qcqs n).2⟩⟩
  matching := M.matching
  projection := M.projection
  projection_naturality := M.projection_naturality
  matching_universal := M.matching_universal
  matchingMap := M.matchingMap
  matchingMap_projection := M.matchingMap_projection
  matching_qcqs := M.matching_qcqs


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
noncomputable def finite_etale_cofan_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type*} [Finite A] (V : A → Y.Etale) (W : Y.Etale)
    (ι : ∀ a, V a ⟶ W) (h : IsColimit (Cofan.mk W ι)) :
    IsColimit (Cofan.mk (f.Etale.obj W) (fun a ↦ f.Etale.map (ι a))) := by
  let F := Scheme.Etale.forget Y ⋙ Over.forget Y
  have : Small.{u} A := inferInstance
  have : IsZariskiLocalAtSource @Etale.{u} := inferInstance
  have : CreatesColimitsOfShape (Discrete A)
      (MorphismProperty.Over.forget @Etale.{u} ⊤ Y) := inferInstance
  have : PreservesColimitsOfShape (Discrete A) (Scheme.Etale.forget Y) := by
    unfold Scheme.Etale.forget
    infer_instance
  have h' := isColimitCofanMkObjOfIsColimit F V ι h
  have hau := FinitaryPreExtensive.isUniversal_finiteCoproducts h'
  let G := Scheme.Etale.forget X ⋙ Over.forget X
  have hp : Nonempty (IsColimit (Cofan.mk (pullback W.hom f)
      (fun a ↦ (f.Etale.map (ι a)).left))) := by
    exact hau.nonempty_isColimit_of_isPullback_right (fun a ↦ (V a).hom) W.hom f
      (fun a ↦ pullback.fst (V a).hom f) (fun a ↦ pullback.snd (V a).hom f)
      (fun a ↦ IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
      _ (Iso.refl _) (fun a ↦ by simpa [F] using Over.w ((Scheme.Etale.forget Y).map (ι a)))
      (fun a ↦ by change _ ≫ _ = _ ≫ (ι a).left; exact f.etale_map_left_comp_fst (ι a))
      (fun a ↦ by
        change _ ≫ 𝟙 _ ≫ _ = _
        rw [Category.id_comp]
        exact f.etale_map_left_comp_snd (ι a))
  exact isColimitOfIsColimitCofanMkObj G _ _ hp.some


/-- The underlying diagram of schemes over the base. -/
def diagram {X : Scheme.{u}} {r : ℕ} (U : TruncatedFiniteSplitEtaleDiagram X r) :=
  U.simplicial ⋙ Scheme.Etale.forget X

/-- Base change of the simplicial diagram and its nondegenerate inclusions. -/
def IsBaseChange {X Y : Scheme.{u}} {r : ℕ} (f : X ⟶ Y)
    (U : TruncatedFiniteSplitEtaleDiagram Y r)
    (V : TruncatedFiniteSplitEtaleHypercover X r) : Prop :=
  ∃ e : U.diagram ⋙ Over.pullback f ≅ V.diagram,
    ∀ n : Fin (r + 1),
      ∃ a : (Over.pullback f).obj ((Scheme.Etale.forget Y).obj (U.N n)) ≅
          (Scheme.Etale.forget X).obj (V.N n),
        (Over.pullback f).map ((Scheme.Etale.forget Y).map (U.inclusion n)) ≫
            e.hom.app (op ⟨SimplexCategory.mk n.val, Nat.le_of_lt_succ n.isLt⟩) =
          a.hom ≫ (Scheme.Etale.forget X).map (V.inclusion n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pull back the finite split diagram and all its matching cones. -/
noncomputable def pullback {X Y : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y] {r : ℕ}
    (U : TruncatedFiniteSplitEtaleDiagram Y r) (f : X ⟶ Y) :
    TruncatedFiniteSplitEtaleDiagram X r where
  simplicial := U.simplicial ⋙ f.Etale
  N := fun n ↦ f.Etale.obj (U.N n)
  inclusion := fun n ↦ f.Etale.map (U.inclusion n)
  splitting Δ := by
    simpa only [Functor.comp_obj, Functor.comp_map, Functor.map_comp] using
      finite_etale_cofan_pullback f _ _ _ (U.splitting Δ)
  finite_each_degree n := by
    obtain ⟨k, V, ι, ⟨hι⟩, hV⟩ := U.finite_each_degree n
    refine ⟨k, (fun a ↦ f.Etale.obj (V a)), (fun a ↦ f.Etale.map (ι a)),
      ⟨finite_etale_cofan_pullback f _ _ _ hι⟩, ?_⟩
    intro a
    have := (hV a).2.2.1
    have := (hV a).2.2.2.1
    have := (hV a).2.2.2.2
    have hq : QuasiCompact (f.Etale.obj (V a)).hom := by
      change QuasiCompact (Limits.pullback.snd (V a).hom f)
      infer_instance
    have hs : QuasiSeparated (f.Etale.obj (V a)).hom := by
      change QuasiSeparated (Limits.pullback.snd (V a).hom f)
      infer_instance
    exact ⟨QuasiCompact.compactSpace_of_compactSpace (Y := X) (f.Etale.obj (V a)).hom,
      quasiSeparatedSpace_of_quasiSeparated (Y := X) (f.Etale.obj (V a)).hom,
      inferInstance, hq, hs⟩
  matching := fun n ↦ f.Etale.obj (U.matching n)
  projection := fun n Δ h θ ↦ f.Etale.map (U.projection n Δ h θ)
  projection_naturality n Δ Δ' h h' α θ := by
    simpa only [Functor.comp_map, ← Functor.map_comp] using
      congrArg f.Etale.map (U.projection_naturality n Δ Δ' h h' α θ)
  matching_universal n T p hp := by
    let A := Over.mapPullbackAdj f
    let q (Δ : SimplexCategory.Truncated r) (h : Δ.obj.len < n.val)
        (θ : Δ.obj ⟶ SimplexCategory.mk n.val) :=
      (A.homEquiv T ((Scheme.Etale.forget Y).obj (U.simplicial.obj (op Δ)))).symm
        (p Δ h θ)
    have hq : ∀ (Δ Δ' : SimplexCategory.Truncated r)
        (h : Δ.obj.len < n.val) (h' : Δ'.obj.len < n.val) (α : Δ' ⟶ Δ)
        (θ : Δ.obj ⟶ SimplexCategory.mk n.val),
        q Δ h θ ≫ (Scheme.Etale.forget Y).map (U.simplicial.map α.op) =
          q Δ' h' (α.hom ≫ θ) := by
      intro Δ Δ' h h' α θ
      apply (A.homEquiv _ _).injective
      rw [A.homEquiv_naturality_right]
      dsimp only [q]
      simp only [Equiv.apply_symm_apply]
      exact hp Δ Δ' h h' α θ
    obtain ⟨g, hg, huniq⟩ := U.matching_universal n ((Over.map f).obj T) q hq
    refine ⟨A.homEquiv T _ g, ?_, ?_⟩
    · intro Δ h θ
      change A.homEquiv T _ g ≫ (Over.pullback f).map
        ((Scheme.Etale.forget Y).map (U.projection n Δ h θ)) = _
      rw [← A.homEquiv_naturality_right, hg]
      exact Equiv.apply_symm_apply _ _
    · intro g' hg'
      apply (A.homEquiv T _).symm.injective
      rw [Equiv.symm_apply_apply]
      apply huniq
      intro Δ h θ
      change (A.homEquiv T _).symm g' ≫
        (Scheme.Etale.forget Y).map (U.projection n Δ h θ) = _
      rw [← A.homEquiv_naturality_right_symm]
      exact congrArg (A.homEquiv T _).symm (hg' Δ h θ)
  matchingMap := fun n ↦ f.Etale.map (U.matchingMap n)
  matchingMap_projection n Δ h θ := by
    simpa only [Functor.comp_map, ← Functor.map_comp] using
      congrArg f.Etale.map (U.matchingMap_projection n Δ h θ)
  matching_qcqs n := by
    have := (U.matching_qcqs n).1
    have := (U.matching_qcqs n).2
    have : QuasiCompact (U.matching n).hom :=
      @quasiCompact_of_compactSpace (U.matching n).left Y (U.matching n).hom
        (U.matching_qcqs n).1 inferInstance
    have : QuasiSeparated (U.matching n).hom :=
      @QuasiSeparated.of_quasiSeparatedSpace (U.matching n).left Y
        (U.matching n).hom (U.matching_qcqs n).2
    have : QuasiCompact (f.Etale.obj (U.matching n)).hom := by
      change QuasiCompact (Limits.pullback.snd (U.matching n).hom f)
      infer_instance
    have : QuasiSeparated (f.Etale.obj (U.matching n)).hom := by
      change QuasiSeparated (Limits.pullback.snd (U.matching n).hom f)
      infer_instance
    exact ⟨QuasiCompact.compactSpace_of_compactSpace (Y := X)
      (f.Etale.obj (U.matching n)).hom,
      quasiSeparatedSpace_of_quasiSeparated (Y := X) (f.Etale.obj (U.matching n)).hom⟩

/-- Add matching covers to the already constructed finite split diagram. -/
def toHypercover {X : Scheme.{u}} {r : ℕ} (U : TruncatedFiniteSplitEtaleDiagram X r)
    (hU : ∀ n, Surjective (U.matchingMap n).left) : TruncatedFiniteSplitEtaleHypercover X r where
  simplicial := U.simplicial
  N := U.N
  inclusion := U.inclusion
  splitting := U.splitting
  finite_each_degree := U.finite_each_degree
  matching := U.matching
  projection := U.projection
  projection_naturality := U.projection_naturality
  matching_universal := U.matching_universal
  matchingMap := U.matchingMap
  matchingMap_projection := U.matchingMap_projection
  matching_cover := hU

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Base-change comparisons of the simplicial diagram and nondegenerate inclusions compose. -/
theorem isBaseChange_pullback {X Y Z : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] [QuasiSeparatedSpace Z] {r : ℕ}
    (U : TruncatedFiniteSplitEtaleDiagram Z r)
    (V : TruncatedFiniteSplitEtaleHypercover X r)
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hfg : f ≫ g = k)
    (hU : U.IsBaseChange k V)
    (hcover : ∀ n, Surjective ((U.pullback g).matchingMap n).left) :
    ((U.pullback g).toHypercover hcover).IsBaseChange f V := by
  obtain ⟨e, he⟩ := hU
  let K : Over.pullback g ⋙ Over.pullback f ≅ Over.pullback k :=
    (Over.pullbackComp f g).symm ≪≫ eqToIso (congrArg (fun t ↦ Over.pullback t) hfg)
  let L : (U.pullback g).diagram ⋙ Over.pullback f ≅ U.diagram ⋙ Over.pullback k :=
    Functor.isoWhiskerLeft U.diagram K
  refine ⟨L ≪≫ e, fun n ↦ ?_⟩
  obtain ⟨a, ha⟩ := he n
  refine ⟨K.app ((Scheme.Etale.forget Z).obj (U.N n)) ≪≫ a, ?_⟩
  simp only [Iso.trans_hom, NatTrans.comp_app, L,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  change (Over.pullback f).map ((Over.pullback g).map
      ((Scheme.Etale.forget Z).map (U.inclusion n))) ≫
      K.hom.app _ ≫ e.hom.app _ = (K.hom.app _ ≫ a.hom) ≫ _
  calc
    _ = (K.hom.app _ ≫ (Over.pullback k).map
          ((Scheme.Etale.forget Z).map (U.inclusion n))) ≫ e.hom.app _ :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ e.hom.app _) (K.hom.naturality _))
    _ = _ := by simpa only [Category.assoc] using congrArg (K.hom.app _ ≫ ·) ha

end TruncatedFiniteSplitEtaleDiagram
end AlgebraicGeometry
