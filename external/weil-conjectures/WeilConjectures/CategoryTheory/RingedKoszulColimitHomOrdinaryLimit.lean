/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedHomComplexColimitCone
import WeilConjectures.CategoryTheory.RingedKoszulFiniteEvaluation

/-! # Finite Koszul evaluation and ordinary inverse limits

Source: Stacks Project, sites-cohomology.tex, Tag 0A0A.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option allowUnsafeReducibility true in
attribute [local reducible] ringedKoszulTensorTowerFunctor
  Functor.comp Functor.const Functor.mapHomologicalComplex
  homComplex ringedKoszulAugmentationCocone

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)

private abbrev tensorLimitCone (N : ringedSiteComplex O) :
    Cone ((ringedKoszulTensorTower O r b).obj N) where
  pt := ((lim : (ℕᵒᵖ ⥤ SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤ _).mapHomologicalComplex
      (.up ℤ)).obj (ringedKoszulTensorTowerComplex O r b N)
  π :=
    { app := fun m ↦
        { f := fun n ↦ limit.π ((ringedKoszulTensorTowerComplex O r b N).X n) m
          comm' := fun n k h ↦ by
            have hk : n + 1 = k := h
            subst k
            change _ = limMap _ ≫ _
            rw [limMap_π]
            simp [ringedKoszulTensorTowerComplex, CochainComplex.of_d] }
      naturality := fun {m k} f ↦ by
        apply HomologicalComplex.hom_ext
        intro n
        change 𝟙 _ ≫ limit.π ((ringedKoszulTensorTowerComplex O r b N).X n) k =
          limit.π ((ringedKoszulTensorTowerComplex O r b N).X n) m ≫
            ((ringedKoszulTensorTowerComplex O r b N).X n).map f
        exact (Category.id_comp _).trans
          (limit.w ((ringedKoszulTensorTowerComplex O r b N).X n) f).symm }

private def tensorLimitConeIsLimit (N : ringedSiteComplex O) :
    IsLimit (tensorLimitCone O r b N) :=
  HomologicalComplex.isLimitOfEval _ _ (fun _n ↦ limit.isLimit _)

attribute [local irreducible] homComplexFunctor ringedKoszulDiagram ringedKoszulTensorTower
  ringedHomUnitEvaluationIso ringedKoszulProjection ringedKoszulTensorUnitComponent

set_option backward.isDefEq.respectTransparency true in
/-- Internal Hom from the colimit of positive Koszul complexes is the ordinary limit
of the strict dual tensor tower, naturally in the coefficient complex and compatibly
with the actual degree-zero units. This is a statement before localization.

Source: Stacks Project, sites-cohomology.tex, Tag 0A0A,
lemma-colim-and-lim-of-duals, finite evaluation and Hom of a colimit;
more-algebra.tex, Tag 0913.
(auxiliary; not a blueprint node).

Proof: for each positive Koszul complex P_m, finite evaluation gives
Hom(P_m,N) = N tensor Hom(P_m,O[0]). Its component on the summand of source degree p
and coefficient degree q uses the usual total-complex sign; the two differential
terms therefore agree with d(f) = d_N f - (-1)^degree(f) f d_P. This evaluation is
natural in P_m and N, hence identifies the dual transition maps with the actual
strict tensor-tower transitions. Internal Hom sends colimits in its first variable
to limits: degreewise use the tensor-Hom adjunction and the colimit universal
property, then commute the products over source degrees and tower indices.
The resulting degreewise isomorphisms commute with differentials and coefficient
maps, giving the displayed natural isomorphism. Precomposition with the colimit
augmentation restricts at stage m to precomposition with P_m -> O[0]. Evaluation
at one identifies this with tensoring the dual degree-zero unit, so equality after
every limit projection gives the asserted unit equation. For the empty list these
are the constant unit tower and the unit evaluation isomorphism; zero and invertible
generators require no division in this construction. -/
theorem exists_ringedKoszul_colimitHom_ordinaryLimit_iso :
    ∃ e : (homComplexFunctor (R := O)).obj (op (colimit (ringedKoszulDiagram O r b))) ≅
        ringedKoszulTensorTowerFunctor O r b ⋙
          (lim : (ℕᵒᵖ ⥤ SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤ _).mapHomologicalComplex
              (.up ℤ),
      ∀ N : ringedSiteComplex O, (ringedHomUnitEvaluationIso O N).inv ≫
        ((homComplexFunctor (R := O)).map
          (colimit.desc _ (ringedKoszulAugmentationCocone O r b)).op).app N ≫
        e.hom.app N = (by
          exact ringedKoszulLimitUnit O r b N) := by
  obtain ⟨v, hv, hu⟩ := exists_ringedKoszul_finiteEvaluation O r b
  let c (N : ringedSiteComplex O) :=
    (Cone.postcompose (v N).hom).obj
      (ringedHomComplexColimitCone O (ringedKoszulDiagram O r b) N)
  let hc (N : ringedSiteComplex O) : IsLimit (c N) :=
    (IsLimit.postcomposeHomEquiv (v N) _).symm
      (ringedHomComplexColimitCone_isLimit O _ N).some
  let e (N : ringedSiteComplex O) :
      ((homComplexFunctor (R := O)).obj
        (op (colimit (ringedKoszulDiagram O r b)))).obj N ≅
        (tensorLimitCone O r b N).pt :=
    (hc N).conePointUniqueUpToIso (tensorLimitConeIsLimit O r b N)
  have he (N : ringedSiteComplex O) (m : ℕᵒᵖ) :
      (e N).hom ≫ (tensorLimitCone O r b N).π.app m =
        ((homComplexFunctor (R := O)).map
          (colimit.ι (ringedKoszulDiagram O r b) m.unop).op).app N ≫
            (v N).hom.app m :=
    (hc N).conePointUniqueUpToIso_hom_comp (tensorLimitConeIsLimit O r b N) m
  refine ⟨NatIso.ofComponents e (fun {N M} f ↦ ?_), fun N ↦ ?_⟩
  · apply (tensorLimitConeIsLimit O r b M).hom_ext
    intro m
    rw [Category.assoc, he M m]
    change ((homComplexFunctor (R := O)).obj
      (op (colimit (ringedKoszulDiagram O r b)))).map f ≫
        (((homComplexFunctor (R := O)).map
          (colimit.ι (ringedKoszulDiagram O r b) m.unop).op).app M ≫
            (v M).hom.app m) = (e N).hom ≫
      (((lim : (ℕᵒᵖ ⥤ SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤ _).mapHomologicalComplex
          (.up ℤ)).map (ringedKoszulTensorTowerComplexMap O r b f)) ≫
            (tensorLimitCone O r b M).π.app m
    have hp :
        (((lim : (ℕᵒᵖ ⥤ SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤ _).mapHomologicalComplex
            (.up ℤ)).map (ringedKoszulTensorTowerComplexMap O r b f)) ≫
              (tensorLimitCone O r b M).π.app m =
        (tensorLimitCone O r b N).π.app m ≫
          ((ringedKoszulTensorTower O r b).map f).app m := by
      apply HomologicalComplex.hom_ext
      intro n
      change limMap (ringedKoszulTensorTowerComplexMapF O r b f n) ≫
        limit.π ((ringedKoszulTensorTowerComplex O r b M).X n) m = _
      exact limMap_π _ m
    rw [hp, ← Category.assoc (e N).hom, he N m, Category.assoc, ← hv N M f m]
    simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ (v M).hom.app m)
      (((homComplexFunctor (R := O)).map
        (colimit.ι (ringedKoszulDiagram O r b) m.unop).op).naturality f)
  · simp only [NatIso.ofComponents_hom_app]
    apply (tensorLimitConeIsLimit O r b N).hom_ext
    intro m
    simp only [Category.assoc]
    conv_lhs =>
      arg 2
      arg 2
      rw [he N m]
    change (ringedHomUnitEvaluationIso O N).inv ≫
      ((homComplexFunctor (R := O)).map
        (colimit.desc _ (ringedKoszulAugmentationCocone O r b)).op).app N ≫
      ((homComplexFunctor (R := O)).map
        (colimit.ι (ringedKoszulDiagram O r b) m.unop).op).app N ≫
      (v N).hom.app m = _
    have ha :
        ((homComplexFunctor (R := O)).map
          (colimit.desc _ (ringedKoszulAugmentationCocone O r b)).op).app N ≫
        ((homComplexFunctor (R := O)).map
          (colimit.ι (ringedKoszulDiagram O r b) m.unop).op).app N =
        ((homComplexFunctor (R := O)).map
          (ringedKoszulProjection O r b m.unop).op).app N := by
      have haug :
          (colimit.desc _ (ringedKoszulAugmentationCocone O r b)).op ≫
            (colimit.ι (ringedKoszulDiagram O r b) m.unop).op =
          (ringedKoszulProjection O r b m.unop).op :=
        congrArg (fun g ↦ g.op)
          (colimit.ι_desc (ringedKoszulAugmentationCocone O r b) m.unop)
      exact (congrArg (fun t ↦ t.app N)
        ((homComplexFunctor (R := O)).map_comp
          (colimit.desc _ (ringedKoszulAugmentationCocone O r b)).op
          (colimit.ι (ringedKoszulDiagram O r b) m.unop).op)).symm.trans
        (congrArg (fun g ↦ ((homComplexFunctor (R := O)).map g).app N) haug)
    conv_lhs =>
      arg 2
      rw [← Category.assoc]
      arg 1
      rw [ha]
    rw [hu N m]
    apply HomologicalComplex.hom_ext
    intro n
    change (ringedKoszulTensorUnitComponent O r b N m).f n =
      limit.lift ((ringedKoszulTensorTowerComplex O r b N).X n)
        (ringedKoszulTensorUnitCone O r b N n) ≫
          limit.π ((ringedKoszulTensorTowerComplex O r b N).X n) m
    rw [limit.lift_π]
    rfl

end CategoryTheory
