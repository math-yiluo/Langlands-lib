/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemRestrictionEvaluation
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSingleCoefficientProjection
import WeilConjectures.CategoryTheory.Adjunction.MateCube

/-! # Evaluation of the normalized system scalar mate

Source: Zheng, Constructions 4.1 and 5.14--5.15, Lemma 5.16; Stacks Tag 0GL6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- Evaluation of the system coefficient mate is the published proper/open map.
Source: Zheng Lemma 5.16; Stacks Tag 0GL6
(blueprint: lem-pur-etale-system-projection-evaluation).

Proof: First take the scalar-adjunction transpose of the system projection. Its word
is compact support applied to the scalar unit followed by inverse scalar restriction.
Evaluate the word using the ordinary sectionwise identity comparisons in Theory.
Their inverse-image mates and their exact localizations preserve the normalized
units and counits, by the mate identities. The proper comparison is consequently
the mate defining scalarRestrictionDirectImageMap. Transpose once more by the
geometric adjunction; its counit word is scalarMate. For the open factor, exact
localization of the ordinary open mate is the canonical scalar/open balancing map.
Its transpose is the open unit followed by scalar unit insertion, hence it is
ExceptionalCoefficients.openIso. Naturality pastes these two words. Cancel the
support and scalar evaluation isomorphisms to obtain the displayed equation in
the target coefficient category. This compares the actual words before evaluation,
and makes no claim that evaluation is faithful on derived morphisms. -/
theorem etaleSystemProjection_evaluation
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (l : ℕ) (t : Theory c l) :
    (∀ (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (n : ℕ)
        (M : Derived X B.rings),
        (scalarExtension (a.app (op n)).hom Y).map
            ((t.supportEvaluation B n).iso.inv.app M) ≫
          (t.scalarEvaluationY a n).iso.inv.app ((t.support B).F.obj M) ≫
          (t.evaluationY C n).E.map ((t.q a).app M) ≫
          (t.supportEvaluation C n).iso.hom.app ((t.scalarX a).model.T.obj M) ≫
          (rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (C.rings.obj (op n))) c).map
              ((t.scalarEvaluationX a n).iso.hom.app M) =
          (compactScalarMap (a.app (op n)).hom c).app ((t.evaluationX B n).E.obj M)) := by
  intro B C a n M
  obtain ⟨d, hd, htranspose⟩ := (etaleSingleCoefficientProjection c l).1
    (B.rings.obj (op n)) (C.rings.obj (op n)) (B.finite n) (C.finite n)
    (B.torsion n) (C.torsion n) (a.app (op n))
  let ax := (t.scalarX a).adjunction
  let ay := (t.scalarY a).adjunction
  let bx := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology (a.app (op n)).hom)
  let bY := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology (a.app (op n)).hom)
  have hx : mateEquiv ax bx
      (TwoSquare.mk _ _ _ _ (t.scalarEvaluationX a n).iso.inv) =
      TwoSquare.mk _ _ _ _ (t.scalarEvaluationX a n).restriction.hom := by
    rw [(t.scalarEvaluationX a n).mate]
    exact (mateEquiv ax bx).apply_symm_apply _
  have hy : mateEquiv ay bY
      (TwoSquare.mk _ _ _ _ (t.scalarEvaluationY a n).iso.inv) =
      TwoSquare.mk _ _ _ _ (t.scalarEvaluationY a n).restriction.hom := by
    rw [(t.scalarEvaluationY a n).mate]
    exact (mateEquiv ay bY).apply_symm_apply _
  have hq : mateEquiv ax ay (TwoSquare.mk _ _ _ _ (t.q a)) =
      TwoSquare.mk _ _ _ _ (t.restriction a).iso.inv :=
    (mateEquiv ax ay).apply_symm_apply _
  have hs : mateEquiv bx bY (TwoSquare.mk _ _ _ _
      (compactScalarMap (a.app (op n)).hom c)) = TwoSquare.mk _ _ _ _ d.inv := by
    apply mateEquiv_eq_of_unit
    intro K
    exact (htranspose K).symm
  have hc := mateEquiv_app_cube_converse ax ay bx bY
    (t.q a) (compactScalarMap (a.app (op n)).hom c)
    (t.scalarEvaluationX a n).iso.inv (t.scalarEvaluationY a n).iso.inv
    (t.supportEvaluation B n).iso.inv (t.supportEvaluation C n).iso.inv
    (fun N ↦ by
      rw [hq, hx, hy, hs]
      exact etaleSystemRestriction_evaluation c l t B C a n d hd N) M
  dsimp only [Functor.comp_obj] at hc
  have ht := congrArg (fun z ↦ z ≫
    (t.supportEvaluation C n).iso.hom.app ((t.scalarX a).model.T.obj M) ≫
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (C.rings.obj (op n))) c).map
        ((t.scalarEvaluationX a n).iso.hom.app M)) hc
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app] at ht
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at ht
  exact ht

end AlgebraicGeometry.Etale.SystemProjection
