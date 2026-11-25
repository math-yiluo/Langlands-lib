/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HypercoverCohomologyColimit
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.TruncatedFiniteSplitEtaleDiagram

/-! # Base change of finite split étale hypercovers

Source: the finite-cochain argument of the blueprint étale cohomology continuity lemma.
-/

@[expose] public section

universe u' u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Base change preserves the splitting, matching objects and matching covers.
Source: blueprint étale cohomology continuity, detailed proof paragraph 2.
Finite étale coproduct cofans remain colimiting under base change. Each finite-presentation qcqs
constituent stays finite-presentation and qcqs over the qcqs new base. The map-pullback adjunction
transfers the universal property of each matching object; naturality transfers its projection
equations. Matching covers remain covers under base change. Apply the inverse-image unit to obtain
the cosimplicial section map, alternating cochain map, and homology map. Unit naturality proves
refinement compatibility.
(auxiliary; not a blueprint node) -/
noncomputable def baseChange {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (U : FiniteSplitEtaleHypercover Y) (f : X ⟶ Y) : FiniteSplitEtaleHypercover X where
  simplicial := U.simplicial ⋙ f.Etale
  splitting :=
    { N := fun n ↦ f.Etale.obj (U.splitting.N n)
      ι := fun n ↦ f.Etale.map (U.splitting.ι n)
      isColimit' := fun Δ ↦ by
        simpa only [SimplicialObject.Splitting.cofan', Functor.comp_obj,
          Functor.comp_map, Functor.map_comp] using
          TruncatedFiniteSplitEtaleDiagram.finite_etale_cofan_pullback f _ _ _
            (U.splitting.isColimit' Δ) }
  finite_each_degree n := by
    obtain ⟨k, V, ι, ⟨hι⟩, hV⟩ := U.finite_each_degree n
    refine ⟨k, (fun a ↦ f.Etale.obj (V a)), (fun a ↦ f.Etale.map (ι a)),
      ⟨TruncatedFiniteSplitEtaleDiagram.finite_etale_cofan_pullback f _ _ _ hι⟩, ?_⟩
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
    let q (Δ : SimplexCategory) (h : Δ.len < n)
        (θ : Δ ⟶ SimplexCategory.mk n) :=
      (A.homEquiv T ((Scheme.Etale.forget Y).obj (U.simplicial.obj (op Δ)))).symm
        (p Δ h θ)
    have hq : ∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
        (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
        q Δ h θ ≫ (Scheme.Etale.forget Y).map (U.simplicial.map α.op) =
          q Δ' h' (α ≫ θ) := by
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
  matching_cover n := by
    let m := (Scheme.Etale.forget Y).map (U.matchingMap n)
    have hp : IsPullback (pullback.fst _ f) ((Over.pullback f).map m).left m.left
        (pullback.fst _ f) := by
      apply IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback _ _)
      convert IsPullback.of_hasPullback
        (U.simplicial.obj (op (SimplexCategory.mk n))).hom f using 1 <;>
        first | rfl | exact Over.w m | simp [Over.pullback]
    exact MorphismProperty.of_isPullback hp (U.matching_cover n)

variable {X Y : Scheme.{u}}
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- A refinement pulls back by whiskering with the étale base-change functor. -/
noncomputable def baseChangeRefinement {U V : FiniteSplitEtaleHypercover Y}
    (r : U.Refinement V) (f : X ⟶ Y) : (U.baseChange f).Refinement (V.baseChange f) :=
  Functor.whiskerRight r f.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- The adjunction unit induces the pullback map on cosimplicial section objects. -/
noncomputable def baseChangeSectionMap (U : FiniteSplitEtaleHypercover Y) (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology A) :
    U.simplicial.rightOp ⋙ F.obj ⟶
      (U.baseChange f).simplicial.rightOp ⋙ ((Etale.upperStar A f).obj F).obj :=
  Functor.whiskerLeft U.simplicial.rightOp
    ((Etale.upperStarLowerStarAdjunction A f).unit.app F).hom

/-- Applying the alternating coface construction gives a morphism of cochain complexes. -/
noncomputable def baseChangeCochainMap (U : FiniteSplitEtaleHypercover Y) (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology A) :
    (AlgebraicTopology.alternatingCofaceMapComplex A).obj (U.simplicial.rightOp ⋙ F.obj) ⟶
      (AlgebraicTopology.alternatingCofaceMapComplex A).obj
        ((U.baseChange f).simplicial.rightOp ⋙ ((Etale.upperStar A f).obj F).obj) :=
  (AlgebraicTopology.alternatingCofaceMapComplex A).map (baseChangeSectionMap A U f F)

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back cosimplicial sections commutes with refinement. -/
theorem baseChangeSectionMap_refinement {U V : FiniteSplitEtaleHypercover Y}
    (r : U.Refinement V) (f : X ⟶ Y) (F : Sheaf Y.smallEtaleTopology A) :
    baseChangeSectionMap A V f F ≫
        Functor.whiskerRight (baseChangeRefinement r f).rightOp
          ((Etale.upperStar A f).obj F).obj =
      Functor.whiskerRight r.rightOp F.obj ≫ baseChangeSectionMap A U f F := by
  ext Δ
  exact (((Etale.upperStarLowerStarAdjunction A f).unit.app F).hom.naturality
    (r.rightOp.app Δ)).symm

/-- Pullback of sections on a single hypercover induces a map on its cohomology. -/
noncomputable def baseChangeCohomologyMap (U : FiniteSplitEtaleHypercover Y)
    (f : X ⟶ Y) (F : Sheaf Y.smallEtaleTopology A) (q : ℕ) :
    (cohomologyFunctor A U q).obj F ⟶
      (cohomologyFunctor A (U.baseChange f) q).obj ((Etale.upperStar A f).obj F) :=
  HomologicalComplex.homologyMap (baseChangeCochainMap A U f F) q

set_option backward.isDefEq.respectTransparency false in
/-- Pullback on cohomology commutes with refinements. -/
theorem baseChangeCohomologyMap_refinement {U V : FiniteSplitEtaleHypercover Y}
    (r : U.Refinement V) (f : X ⟶ Y) (F : Sheaf Y.smallEtaleTopology A) (q : ℕ) :
    (cohomologyRefinement A r q).app F ≫ baseChangeCohomologyMap A U f F q =
      baseChangeCohomologyMap A V f F q ≫
        (cohomologyRefinement A (baseChangeRefinement r f) q).app
          ((Etale.upperStar A f).obj F) := by
  let C := AlgebraicTopology.alternatingCofaceMapComplex A ⋙
    HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q
  change C.map (Functor.whiskerRight r.rightOp F.obj) ≫
      C.map (baseChangeSectionMap A U f F) =
    C.map (baseChangeSectionMap A V f F) ≫
      C.map (Functor.whiskerRight (baseChangeRefinement r f).rightOp
        ((Etale.upperStar A f).obj F).obj)
  simpa only [Functor.map_comp] using
    (C.congr_map (baseChangeSectionMap_refinement A r f F)).symm

end AlgebraicGeometry.FiniteSplitEtaleHypercover
