/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
/-- Canonical section transitions on iterated etale pullbacks compose.
Source: Stacks Project, Tag 09YP, proof of lemma-colimit, canonical Cech comparison.
(blueprint: lem-weil-pbc-etale-pullback-section-composition).

Proof: Expand the section transitions. Naturality of the inverse-image unit and
of the coefficient morphism moves restriction along gamma a through the second
transition. Substitute the coefficient composition law and
upperStarComp_hom_app_unit_app. The combined geometric map is the canonical
iterated-pullback comparison followed by the pullback of gamma a and gamma b.
Its first projection to W0 agrees with gamma (a ≫ b) by hgamma and D.map_comp;
its structural projection agrees because these are morphisms over the same
scheme. Pullback uniqueness identifies these maps. Contravariant functoriality
then identifies their restrictions and proves the displayed equality. This
argument concerns one etale object, with no Cech products or differentials. -/
theorem etale_pullback_section_composition
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (i₀ : I) (W₀ : (D.obj (op i₀)).Etale) :
    let J := {j : I // i₀ ≤ j}
    let Wj := fun j : J ↦
      (MorphismProperty.Over.pullback @Etale ⊤
        (D.map (homOfLE j.property).op)).obj W₀
    ∀ (γ : ∀ (j k : J) (a : j ⟶ k),
        (MorphismProperty.Over.pullback @Etale ⊤
          (D.map (show j.val ⟶ k.val from a).op)).obj (Wj j) ≅ Wj k)
      (hγ : ∀ (j k : J) (a : j ⟶ k),
        (γ j k a).hom.left ≫
            pullback.fst W₀.hom (D.map (homOfLE k.property).op) =
          pullback.fst (Wj j).hom (D.map (show j.val ⟶ k.val from a).op) ≫
            pullback.fst W₀.hom (D.map (homOfLE j.property).op)),
    let T := fun (j k : J) (a : j ⟶ k) ↦
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (D.map (show j.val ⟶ k.val from a).op)).unit.app (F j.val)).hom.app
          (op (Wj j)) ≫
      (φ (show j.val ⟶ k.val from a)).hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤
          (D.map (show j.val ⟶ k.val from a).op)).obj (Wj j))) ≫
      (F k.val).obj.map (γ j k a).inv.op
    ∀ (j k r : J) (a : j ⟶ k) (b : k ⟶ r),
      T j r (a ≫ b) = T j k a ≫ T k r b := by
  intro J Wj γ hγ T j k r a b
  let p := D.map (show j.val ⟶ k.val from a).op
  let q := D.map (show k.val ⟶ r.val from b).op
  let pq := D.map (show j.val ⟶ r.val from a ≫ b).op
  have hpq : pq = q ≫ p := D.map_comp (show k.val ⟶ r.val from b).op
    (show j.val ⟶ k.val from a).op
  let X := Wj j
  let Bq := MorphismProperty.Over.pullback @Etale ⊤ q
  let e := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
    q p pq hpq).app X
  have hg : e.hom ≫ Bq.map (γ j k a).hom ≫ (γ k r b).hom =
      (γ j r (a ≫ b)).hom := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · simp only [MorphismProperty.Comma.comp_left, Category.assoc]
      rw [hγ k r b]
      simp only [Bq, q, MorphismProperty.Over.pullback_map_left, pullback.lift_fst_assoc,
        Category.assoc]
      rw [hγ j k a]
      rw [hγ j r (a ≫ b)]
      change e.hom.left ≫ pullback.fst (pullback.snd X.hom p) q ≫
        pullback.fst X.hom p ≫ pullback.fst W₀.hom
          (D.map (homOfLE j.property).op) =
        pullback.fst X.hom pq ≫ pullback.fst W₀.hom
          (D.map (homOfLE j.property).op)
      simp [e, Category.assoc]
    · exact (MorphismProperty.Over.w
        (e.hom ≫ Bq.map (γ j k a).hom ≫ (γ k r b).hom)).trans
          (MorphismProperty.Over.w (γ j r (a ≫ b)).hom).symm
  have hi : (γ j r (a ≫ b)).inv =
      (γ k r b).inv ≫ Bq.map (γ j k a).inv ≫ e.inv := by
    have heq : e ≪≫ Bq.mapIso (γ j k a) ≪≫ γ k r b = γ j r (a ≫ b) :=
      Iso.ext hg
    exact (congrArg Iso.inv heq).symm
  let Bp := MorphismProperty.Over.pullback @Etale ⊤ p
  let Bpq := MorphismProperty.Over.pullback @Etale ⊤ pq
  let A := (upperStar AddCommGrpCat.{u + 1} q).obj
    ((upperStar AddCommGrpCat.{u + 1} p).obj (F j.val))
  let ψ := (upperStar AddCommGrpCat.{u + 1} q).map
    (φ (show j.val ⟶ k.val from a)) ≫ φ (show k.val ⟶ r.val from b)
  have hs := congrArg (fun z ↦ z.hom.app (op X))
    (upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} q p (F j.val) pq hpq)
  change
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} pq).unit.app
      (F j.val)).hom.app (op X) ≫
      ((upperStarComp AddCommGrpCat.{u + 1} q p pq hpq).hom.app (F j.val)).hom.app
        (op (Bpq.obj X)) =
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).unit.app
      (F j.val)).hom.app (op X) ≫
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app
        ((upperStar AddCommGrpCat.{u + 1} p).obj (F j.val))).hom.app
          (op (Bp.obj X)) ≫ A.obj.map e.hom.op at hs
  let α := φ (show j.val ⟶ k.val from a)
  let β := φ (show k.val ⟶ r.val from b)
  let τ := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app
    (F k.val) ≫ (lowerStar AddCommGrpCat.{u + 1} q).map β
  have ht : (F k.val).obj.map (γ j k a).inv.op ≫ τ.hom.app (op (Wj k)) =
      τ.hom.app (op (Bp.obj X)) ≫
        (F r.val).obj.map (Bq.map (γ j k a).inv).op :=
    τ.hom.naturality (γ j k a).inv.op
  have hn := congrArg (fun z ↦ z.hom.app (op (Bp.obj X)))
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit_naturality α)
  have ha :
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app
        ((upperStar AddCommGrpCat.{u + 1} p).obj (F j.val))).hom.app
          (op (Bp.obj X)) ≫ ψ.hom.app (op (Bq.obj (Bp.obj X))) =
      α.hom.app (op (Bp.obj X)) ≫ τ.hom.app (op (Bp.obj X)) := by
    change
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app
        ((upperStar AddCommGrpCat.{u + 1} p).obj (F j.val))).hom.app
          (op (Bp.obj X)) ≫
        ((upperStar AddCommGrpCat.{u + 1} q).map α).hom.app
          (op (Bq.obj (Bp.obj X))) =
      α.hom.app (op (Bp.obj X)) ≫
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app
          (F k.val)).hom.app (op (Bp.obj X)) at hn
    change
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app
        ((upperStar AddCommGrpCat.{u + 1} p).obj (F j.val))).hom.app
          (op (Bp.obj X)) ≫
        ((upperStar AddCommGrpCat.{u + 1} q).map α).hom.app
          (op (Bq.obj (Bp.obj X))) ≫ β.hom.app (op (Bq.obj (Bp.obj X))) =
      α.hom.app (op (Bp.obj X)) ≫
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app
          (F k.val)).hom.app (op (Bp.obj X)) ≫ β.hom.app (op (Bq.obj (Bp.obj X)))
    simpa only [Category.assoc]
      using congrArg (fun z ↦ z ≫ β.hom.app (op (Bq.obj (Bp.obj X)))) hn
  have hψ : A.obj.map e.hom.op ≫ ψ.hom.app (op (Bpq.obj X)) =
      ψ.hom.app (op (Bq.obj (Bp.obj X))) ≫ (F r.val).obj.map e.hom.op :=
    ψ.hom.naturality e.hom.op
  have hφ := congrArg (fun z ↦ z.hom.app (op (Bpq.obj X)))
    (hcomposition j.val k.val r.val (show j.val ⟶ k.val from a)
      (show k.val ⟶ r.val from b))
  change T j r (a ≫ b) = T j k a ≫ T k r b
  dsimp only [T]
  change
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} pq).unit.app
      (F j.val)).hom.app (op X) ≫
      (φ (show j.val ⟶ r.val from a ≫ b)).hom.app (op (Bpq.obj X)) ≫
      (F r.val).obj.map (γ j r (a ≫ b)).inv.op =
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).unit.app
      (F j.val)).hom.app (op X) ≫ α.hom.app (op (Bp.obj X)) ≫
      (F k.val).obj.map (γ j k a).inv.op ≫ τ.hom.app (op (Wj k)) ≫
      (F r.val).obj.map (γ k r b).inv.op
  change (φ (show j.val ⟶ r.val from a ≫ b)).hom.app (op (Bpq.obj X)) =
    ((upperStarComp AddCommGrpCat.{u + 1} q p pq hpq).hom.app (F j.val)).hom.app
      (op (Bpq.obj X)) ≫ ψ.hom.app (op (Bpq.obj X)) at hφ
  rw [hφ]
  simp only [Category.assoc]
  rw [reassoc_of% hs, reassoc_of% hψ, reassoc_of% ha]
  rw [reassoc_of% ht]
  congr 3
  rw [hi]
  simp only [op_comp, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc]
  simp

end AlgebraicGeometry.Etale
