/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
public import WeilConjectures.AlgebraicGeometry.AffineEtaleSiteBaseChange

/-!
# Comparison of arrows on canonical affine étale pullbacks

Source: Stacks Project, Étale Cohomology 0EYL and Limits 01ZM.
(blueprint: lem-pbc-affine-etale-pullback-arrow-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Étale Cohomology 0EYL; Limits 01ZM(2).
Proof: form the canonical affine étale pullbacks of A and B along f, and define
fi by the pullback lift of ψj and the second projection. Pasting their pullback
squares with the qT-squares, and using hr, gives pullback squares over r.
Compare these with the qS-squares by uniqueness of pullbacks. The resulting
scheme isomorphisms commute with the structure maps to L, hence lift to the
full affine étale category. To check the arrow equation, apply the faithful
forgetful functor to schemes and use the qS-square's hom_ext: the first
projection equality is hdesc, and the second is the structure-map equation.
For an empty family the object comparison alone remains; f=id gives the
usual identity base-change comparison. No finiteness or limit descent is
asserted here: ψj and its limit compatibility are hypotheses.
(blueprint: lem-pbc-affine-etale-pullback-arrow-comparison). -/
theorem affineEtale_pullback_arrow_comparison
    {S T L : Scheme.{u}} (f : T ⟶ S) [IsAffineHom f]
    (p : L ⟶ T) (r : L ⟶ S) (hr : p ≫ f = r)
    (vS : S.FullAffineEtale ⥤ L.FullAffineEtale)
    (vT : T.FullAffineEtale ⥤ L.FullAffineEtale)
    (qS : vS ⋙ fullAffineEtaleInclusion L ⋙ Etale.forget L ⋙ Over.forget L ⟶
      fullAffineEtaleInclusion S ⋙ Etale.forget S ⋙ Over.forget S)
    (qT : vT ⋙ fullAffineEtaleInclusion L ⋙ Etale.forget L ⋙ Over.forget L ⟶
      fullAffineEtaleInclusion T ⋙ Etale.forget T ⋙ Over.forget T)
    (hS : ∀ A : S.FullAffineEtale,
      IsPullback (qS.app A) (vS.obj A).obj.hom A.obj.hom r)
    (hT : ∀ A : T.FullAffineEtale,
      IsPullback (qT.app A) (vT.obj A).obj.hom A.obj.hom p)
    (n : ℕ) (A : S.FullAffineEtale) (B : Fin n → S.FullAffineEtale)
    (g : ∀ a, vS.obj (B a) ⟶ vS.obj A)
    (ψj : ∀ a, pullback (B a).obj.hom f ⟶ A.obj.left)
    (hψj : ∀ a, ψj a ≫ A.obj.hom = pullback.fst (B a).obj.hom f ≫ (B a).obj.hom)
    (hdesc : ∀ a,
      pullback.map (B a).obj.hom r (B a).obj.hom f
        (𝟙 _) p (𝟙 _) (by simp) (by simpa using hr.symm) ≫ ψj a =
        (hS (B a)).isoPullback.inv ≫ (g a).hom.left ≫ qS.app A) :
    ∃ (fi : ∀ a, (affineEtaleBaseChange f).obj (B a) ⟶
        (affineEtaleBaseChange f).obj A)
      (t : vT.obj ((affineEtaleBaseChange f).obj A) ≅ vS.obj A)
      (s : ∀ a, vT.obj ((affineEtaleBaseChange f).obj (B a)) ≅ vS.obj (B a)),
      ∀ a, vT.map (fi a) ≫ t.hom = (s a).hom ≫ g a  := by
  let U := affineEtaleBaseChange f
  let fi (a : Fin n) : U.obj (B a) ⟶ U.obj A :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk
      (pullback.lift (ψj a) (pullback.snd (B a).obj.hom f)
        (by
          change ψj a ≫ A.obj.hom = pullback.snd (B a).obj.hom f ≫ f
          rw [hψj a, pullback.condition])) (by
            change pullback.lift _ _ _ ≫ pullback.snd A.obj.hom f = _
            simp only [pullback.lift_snd]
            rfl))
  have hU (X : S.FullAffineEtale) :
      IsPullback (qT.app (U.obj X) ≫ pullback.fst X.obj.hom f)
        (vT.obj (U.obj X)).obj.hom X.obj.hom r := by
    have H := (hT (U.obj X)).paste_horiz (IsPullback.of_hasPullback X.obj.hom f)
    simpa only [hr] using H
  let e (X : S.FullAffineEtale) := (hU X).isoPullback ≪≫ (hS X).isoPullback.symm
  have he (X : S.FullAffineEtale) :
      (e X).hom ≫ (vS.obj X).obj.hom = (vT.obj (U.obj X)).obj.hom := by
    dsimp [e]
    simp
  let t (X : S.FullAffineEtale) : vT.obj (U.obj X) ≅ vS.obj X :=
    ObjectProperty.isoMk (fun X : L.Etale ↦ IsAffine X.left)
      (MorphismProperty.Over.isoMk (e X) (he X))
  have ht (X : S.FullAffineEtale) :
      (t X).hom.hom.left ≫ qS.app X = qT.app (U.obj X) ≫ pullback.fst X.obj.hom f := by
    dsimp [t, e]
    simp
  refine ⟨fi, t A, (fun a ↦ t (B a)), ?_⟩
  intro a
  apply ObjectProperty.hom_ext
  apply MorphismProperty.Over.Hom.ext
  apply (hS A).hom_ext
  · change ((vT.map (fi a)).hom.left ≫ (t A).hom.hom.left) ≫ qS.app A =
      ((t (B a)).hom.hom.left ≫ (g a).hom.left) ≫ qS.app A
    rw [Category.assoc, ht]
    have hnat : (vT.map (fi a)).hom.left ≫ qT.app (U.obj A) =
        qT.app (U.obj (B a)) ≫ (fi a).hom.left := qT.naturality (fi a)
    rw [← Category.assoc, hnat, Category.assoc]
    change qT.app (U.obj (B a)) ≫
      (pullback.lift (ψj a) (pullback.snd (B a).obj.hom f) _ ≫
        pullback.fst A.obj.hom f) = _
    rw [pullback.lift_fst]
    have hm : (hU (B a)).isoPullback.hom ≫
        pullback.map (B a).obj.hom r (B a).obj.hom f
          (𝟙 _) p (𝟙 _) (by simp) (by simpa using hr.symm) =
        qT.app (U.obj (B a)) := by
      apply pullback.hom_ext
      · simp [IsPullback.isoPullback_hom_fst]
      · simp only [Category.assoc, pullback.lift_snd,
          IsPullback.isoPullback_hom_snd_assoc]
        exact (hT (U.obj (B a))).w.symm
    rw [← hm, Category.assoc, hdesc a]
    change (hU (B a)).isoPullback.hom ≫ (hS (B a)).isoPullback.inv ≫
      (g a).hom.left ≫ qS.app A = ((e (B a)).hom ≫ (g a).hom.left) ≫ qS.app A
    dsimp [e]
    simp only [Category.assoc]
  · change ((vT.map (fi a)).hom.left ≫ (t A).hom.hom.left) ≫ (vS.obj A).obj.hom =
      ((t (B a)).hom.hom.left ≫ (g a).hom.left) ≫ (vS.obj A).obj.hom
    simp only [Category.assoc, MorphismProperty.Over.w]


end AlgebraicGeometry.Scheme
