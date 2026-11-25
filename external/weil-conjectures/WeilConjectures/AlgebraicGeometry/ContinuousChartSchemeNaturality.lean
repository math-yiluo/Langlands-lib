/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData

/-! # Scheme naturality of the canonical continuous coefficient chart -/

@[expose] public section
universe u
open CategoryTheory Limits Opposite MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

private lemma chartMate_homEquiv {W X Y : Scheme.{u}} (f : Y ⟶ X)
    (kX : X ⟶ W) (kY : Y ⟶ W) (hf : f ≫ kX = kY)
    (F : Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
    (M : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (h : (ProEtale.upperStar Ab.{u + 1} kY).obj F ⟶ M) :
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} kX).homEquiv _ _
      ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app
          ((ProEtale.upperStar Ab.{u + 1} kX).obj F) ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map
          ((ProEtale.upperStarComp Ab.{u + 1} f kX).inv.app F ≫
            (eqToHom (congrArg (ProEtale.upperStar Ab.{u + 1}) hf)).app F) ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map h) =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} kY).homEquiv _ _ h ≫
        (lowerStarFactor Ab.{u + 1} hf).inv.app M := by
  subst kY
  simp only [eqToHom_refl, NatTrans.id_app, Category.comp_id,
    Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hu := unit_comp_lowerStar_map_unit_comp_upperStarComp' Ab.{u + 1} f kX F
  simp only [Functor.map_comp] at hu
  rw [reassoc_of% hu]
  have hn := (ProEtale.lowerStarComp Ab.{u + 1} f kX).inv.naturality h
  dsimp only [Functor.comp_map] at hn
  rw [← hn]
  rfl

/-- The canonical continuous coefficient chart commutes with scheme direct image.

Source: Bhatt--Scholze, Section 6.8, continuous coefficient realization.
(auxiliary; not a blueprint node)

Proof: apply the adjunction from condensed coefficients to sheaves over X to the
asserted equality. The coefficient pushforward is the mate of the inverse-image
composition isomorphism. Compatibility of units with this composition identifies
the left adjoint with the adjoint chart over Y, followed by the inverse of the
pushforward composition comparison. The right adjoint is the chart over X followed
by the sectionwise continuous-function pushforward. On a relative profinite test
object, both expressions precompose the same continuous function with the first
projection from the same iterated scheme pullback. Pullback pasting identifies those
projections. Thus the adjoints agree on every test object and every section, and
injectivity of the adjunction Hom equivalence gives the desired equality.
No total disconnectedness, matrix, module morphism, or cokernel hypothesis is needed. -/
theorem continuousChart_scheme_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type) [TopologicalSpace O] [Ring O] [IsTopologicalRing O] :
    condensedPushforwardHom (Profinite.continuousMapRingObj O) f ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map (chartComparison Y O) =
    chartComparison X O ≫ continuousFunctionPushforward f O := by
  let adjX := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  let CY := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf Y O)
  have hleft := chartMate_homEquiv f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f)
    (pointUpperStar.obj (Profinite.continuousMapRingObj O)) CY (chartComparison Y O)
  rw [← condensedPullbackHom_eq (Profinite.continuousMapRingObj O) f] at hleft
  apply (adjX.homEquiv _ _).injective
  conv_rhs => rw [adjX.homEquiv_naturality_right]
  have hchart : adjX.homEquiv _ _ (chartComparison X O) =
      chartComparisonAdjoint X O := Equiv.apply_symm_apply _ _
  rw [hchart]
  simp only [adjX, Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply]
  simp only [← unitAlgHom_comp_map_condensedPullbackHom, Category.assoc]
  erw [hleft, pointUpperStarLowerStarAdjunction.homEquiv_naturality_right]
  have hchartY :
      (pointUpperStarLowerStarAdjunction.comp
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Y))).homEquiv _ _
          (chartComparison Y O) = chartComparisonAdjoint Y O := Equiv.apply_symm_apply _ _
  simp only [Adjunction.comp_homEquiv] at hchartY
  erw [hchartY]
  ext S s
  apply ULift.ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  change ((((lowerStarFactor Ab.{u + 1} (comp_toSpecZ f)).inv.app CY).hom.app
    (op (profiniteToProEt.obj S.unop)))
      (ULift.up (s.down.comp (profiniteTestProjection Y S.unop)))).down =
    (((continuousFunctionPushforward f O).hom.app
      (op ((profiniteToProEtOf X).obj S.unop)))
        (ULift.up (s.down.comp (profiniteTestProjection X S.unop)))).down
  rw [lowerStarFactor_inv_app_hom_app, continuousFunctionPushforward_app]
  change (s.down.comp (profiniteTestProjection Y S.unop)).comp
      (((MorphismProperty.Over.pullbackComp f (toSpecZ X) (toSpecZ Y)
        (comp_toSpecZ f).symm).inv.app (profiniteToProEt.obj S.unop)).left.base.hom) =
    (s.down.comp (profiniteTestProjection X S.unop)).comp
      (pullback.fst (((profiniteToProEtOf X).obj S.unop).hom) f).base.hom
  have hp :
      ((MorphismProperty.Over.pullbackComp f (toSpecZ X) (toSpecZ Y)
        (comp_toSpecZ f).symm).inv.app (profiniteToProEt.obj S.unop)).left ≫
          pullback.fst (toSpecZ (profiniteToScheme.obj S.unop)) (toSpecZ Y) =
      pullback.fst (((profiniteToProEtOf X).obj S.unop).hom) f ≫
        pullback.fst (toSpecZ (profiniteToScheme.obj S.unop)) (toSpecZ X) := by
    simp only [MorphismProperty.Over.pullbackComp_inv_app_left]
    dsimp only [pullback.map]
    erw [Category.assoc, pullback.lift_fst]
    simp only [Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
    rfl
  have hp' := congrArg (fun g ↦ g.base.hom) hp
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp] at hp'
  simp only [profiniteTestProjection, ContinuousMap.comp_assoc]
  rw [hp']

end AlgebraicGeometry.ProEtale.CondensedRing
