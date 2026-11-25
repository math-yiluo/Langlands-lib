/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
import WeilConjectures.AlgebraicGeometry.AffineEtaleFiniteDiagramObjects
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Descent of finite affine étale factorization data

Source: Stacks Project, Étale Cohomology Tag 0EYL (lemma-colimit-affine-sites), and
Limits Tags 01ZM and 01ZC, finite-presentation descent of objects and morphisms.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
-- Descend maps out of already chosen affine models, with no finiteness on the targets.
private theorem finite_maps_from_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) {i i₀ : Iᵒᵖ} (f : i ⟶ i₀)
    {A : Type} [Finite A]
    (X : A → (D.obj i).FullAffineEtale) (Y : A → (D.obj i₀).Etale)
    (ψ : ∀ q, pullback (X q).obj.hom (c.π.app i) ⟶ (Y q).left)
    (hψ : ∀ q, ψ q ≫ (Y q).hom =
      pullback.fst (X q).obj.hom (c.π.app i) ≫ (X q).obj.hom ≫ D.map f) :
    ∃ (j : Over i) (g : ∀ q,
      pullback (X q).obj.hom (D.map j.hom) ⟶ (Y q).left),
      (∀ q, (baseChangeCone D c (X q).obj.hom).π.app j ≫ g q = ψ q) ∧
      (∀ q, g q ≫ (Y q).hom =
        pullback.fst (X q).obj.hom (D.map j.hom) ≫ (X q).obj.hom ≫ D.map f) := by
  classical
  let _ := Fintype.ofFinite A
  have h (q : A) : ∃ (j : Over i)
      (g : (baseChangeDiagram D (X q).obj.hom).obj j ⟶ (Y q).left),
      (baseChangeCone D c (X q).obj.hom).π.app j ≫ g = ψ q ∧
      g ≫ (Y q).hom =
        pullback.fst (X q).obj.hom (D.map j.hom) ≫ (X q).obj.hom ≫ D.map f := by
    have : IsAffine ((𝟭 Scheme).obj (X q).obj.left) := (X q).property
    have : IsAffine (X q).obj.left := (X q).property
    have : CompactSpace (X q).obj.left := inferInstance
    have : QuasiSeparatedSpace (X q).obj.left := inferInstance
    have (j : Over i) : CompactSpace ((baseChangeDiagram D (X q).obj.hom).obj j) := by
      change CompactSpace (pullback (X q).obj.hom (D.map j.hom) : Scheme)
      infer_instance
    have (j : Over i) : QuasiSeparatedSpace ((baseChangeDiagram D (X q).obj.hom).obj j) := by
      change QuasiSeparatedSpace (pullback (X q).obj.hom (D.map j.hom) : Scheme)
      infer_instance
    let t : baseChangeDiagram D (X q).obj.hom ⟶
        (Functor.const (Over i)).obj (D.obj i₀) :=
      baseChangeDiagramStructure D (X q).obj.hom ≫ (Functor.const _).map (D.map f)
    obtain ⟨j, g, hg, hw⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (baseChangeDiagram D (X q).obj.hom) t (Y q).hom
      (baseChangeCone D c (X q).obj.hom)
      (isLimitBaseChangeCone D c (X q).obj.hom hc) (ψ q) (by
        ext j
        simpa [t, Category.assoc] using (hψ q).symm)
    exact ⟨j, g, hg, hw⟩
  choose j g hg hw using h
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  let m (q : A) : k ⟶ j q :=
    (hk (Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩)).some
  refine ⟨k, (fun q ↦ (baseChangeDiagram D (X q).obj.hom).map (m q) ≫ g q),
    ?_, ?_⟩
  · intro q
    rw [← Category.assoc, (baseChangeCone D c (X q).obj.hom).w (m q), hg q]
  · intro q
    rw [Category.assoc, hw q]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- Descend finitely many affine étale sources and their two families of arrows.
No covering assumption or conclusion is involved.

Source: Stacks, Étale Cohomology 0EYL, qcqs proof; Limits 01ZM and 01ZC.
(blueprint: lem-weil-pbc-etale-finite-factorization-data-descent).

Proof: Restrict to the cofinal tail above i₀. By affine étale object and arrow
 descent, descend each affine V_q and its map to W. Choose a common stage for
 these finitely many models. For each model, its base-change diagram on the tail
 has affine transitions and affine terms, and limit V_q. Compose b_q with the
 projection to U_q. Since U_q is étale over D(i₀), its structure map is locally
 finitely presented. Limits 01ZC(3) descends this morphism from the qcqs source
 diagram without imposing quasi-compactness on U_q. Its structure equation and
 the pullback universal property give the required stage arrow into the pullback
 of U_q. Choose a common stage for the finitely many arrows and equations.
 Pullback pasting identifies the same source model with V_q for both arrows,
 giving both displayed equations. Affineness survives further base change.
 When n=0 take the identity stage and the empty families. -/
theorem etale_finiteFactorizationDataDescent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (W : (D.obj (op i₀)).FullAffineEtale)
    (n : ℕ) (V : Fin n → c.pt.Etale)
    (a : ∀ q, V q ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W.obj)
    (U : Fin n → (D.obj (op i₀)).Etale)
    (b : ∀ q, V q ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj (U q))
    (hV : ∀ q, IsAffine (V q).left) :
    let B := fun j : Over (op i₀) ↦ MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)
    let F := fun j : Over (op i₀) ↦ MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)
    let e := fun (j : Over (op i₀)) (Z : (D.obj (op i₀)).Etale) ↦
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (c.π.app j.left) (D.map j.hom) (c.π.app (op i₀)) (c.w j.hom).symm).app Z
    ∃ (j : Over (op i₀)) (Vj : Fin n → (D.obj j.left).Etale)
      (aj : ∀ q, Vj q ⟶ (F j).obj W.obj)
      (bj : ∀ q, Vj q ⟶ (F j).obj (U q))
      (d : ∀ q, (B j).obj (Vj q) ≅ V q),
      (∀ q, IsAffine (Vj q).left) ∧
      (∀ q, (B j).map (aj q) ≫ (e j W.obj).inv = (d q).hom ≫ a q) ∧
      (∀ q, (B j).map (bj q) ≫ (e j (U q)).inv = (d q).hom ≫ b q) := by
  classical
  dsimp only
  let V' : Fin n → c.pt.FullAffineEtale := fun q ↦ ⟨V q, hV q⟩
  obtain ⟨i, Xi, hXi⟩ := Scheme.affineEtale_common_models D c hc n V'
  choose r hr using hXi
  obtain ⟨i', hi, hi₀⟩ := exists_ge_ge i i₀
  let f : op i' ⟶ op i₀ := (homOfLE hi₀).op
  let f' : op i' ⟶ op i := (homOfLE hi).op
  let X (q : Fin n) : (D.obj (op i')).FullAffineEtale :=
    ⟨(MorphismProperty.Over.pullback @Etale ⊤ (D.map f')).obj (Xi q).obj, by
      have : IsAffine ((𝟭 Scheme).obj (Xi q).obj.left) := (Xi q).property
      change IsAffine (pullback (Xi q).obj.hom (D.map f'))
      infer_instance⟩
  let r' (q : Fin n) := isPullbackLift D c f' (hr q)
  have hr' (q : Fin n) :
      IsPullback (r' q) (V q).hom (X q).obj.hom (c.π.app (op i')) :=
    isPullback_isPullbackLift f' (hr q)
  -- One common stage for both arrow families; the source model depends only on q.
  let Y : Fin n × Bool → (D.obj (op i₀)).Etale :=
    fun q ↦ if q.2 then U q.1 else W.obj
  let arrow (q : Fin n × Bool) : V q.1 ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj (Y q) := by
    cases q with
    | mk q t => cases t
                · exact a q
                · exact b q
  let ψ (q : Fin n × Bool) :=
    (hr' q.1).isoPullback.inv ≫ (arrow q).left ≫
      pullback.fst (Y q).hom (c.π.app (op i₀))
  have hψ (q : Fin n × Bool) : ψ q ≫ (Y q).hom =
      pullback.fst (X q.1).obj.hom (c.π.app (op i')) ≫
        (X q.1).obj.hom ≫ D.map f := by
    have haw : (arrow q).left ≫ pullback.snd (Y q).hom (c.π.app (op i₀)) =
        (V q.1).hom := (arrow q).w
    dsimp only [ψ]
    rw [Category.assoc, Category.assoc, pullback.condition,
      ← Category.assoc (arrow q).left, haw]
    rw [← Category.assoc, (hr' q.1).isoPullback_inv_snd]
    rw [← c.w f, pullback.condition_assoc]
  obtain ⟨j, g, hg, hw⟩ := finite_maps_from_models D c hc f
    (fun q : Fin n × Bool ↦ X q.1) Y ψ hψ
  let k : Over (op i₀) := Over.mk (j.hom ≫ f)
  let Z (q : Fin n) : (D.obj j.left).Etale :=
    (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj (X q).obj
  have hZ (q : Fin n) : IsAffine (Z q).left := by
    have : IsAffine ((𝟭 Scheme).obj (X q).obj.left) := (X q).property
    change IsAffine (pullback (X q).obj.hom (D.map j.hom))
    infer_instance
  let hj (q : Fin n) := isPullback_isPullbackLift j.hom (hr' q)
  let d (q : Fin n) :
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)).obj (Z q) ≅ V q :=
    MorphismProperty.Over.isoMk (hj q).isoPullback.symm (by
      exact (hj q).isoPullback_inv_snd)
  let gj (q : Fin n × Bool) : Z q.1 ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ (D.map k.hom)).obj (Y q) :=
    MorphismProperty.Over.homMk
      (pullback.lift (g q) (Z q.1).hom (by
        rw [hw q]
        change _ = pullback.snd (X q.1).obj.hom (D.map j.hom) ≫ D.map (j.hom ≫ f)
        rw [Functor.map_comp, pullback.condition_assoc])) (by simp) (by trivial)
  -- The same cartesian source comparison works for both target projections.
  have hM (q : Fin n) : (hj q).isoPullback.inv ≫ (hr' q).isoPullback.hom ≫
      (baseChangeCone D c (X q).obj.hom).π.app j =
      pullback.fst (Z q).hom (c.π.app j.left) := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, baseChangeCone_π_app_fst,
        (hr' q).isoPullback_hom_fst]
      calc
        _ = (hj q).isoPullback.inv ≫
            isPullbackLift D c j.hom (hr' q) ≫
              pullback.fst (X q).obj.hom (D.map j.hom) :=
          congrArg ((hj q).isoPullback.inv ≫ ·) (isPullbackLift_fst j.hom (hr' q)).symm
        _ = _ := by
          rw [← Category.assoc, (hj q).isoPullback_inv_fst]
          rfl
    · rw [Category.assoc, Category.assoc, baseChangeCone_π_app_snd,
        ← Category.assoc (hr' q).isoPullback.hom, (hr' q).isoPullback_hom_snd,
        ← Category.assoc, (hj q).isoPullback_inv_snd]
      exact pullback.condition.symm
  have heq (q : Fin n × Bool) :
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)).map (gj q) ≫
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
          (c.π.app j.left) (D.map k.hom) (c.π.app (op i₀))
          (c.w k.hom).symm).app (Y q)).inv = (d q.1).hom ≫ arrow q := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change (((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)).map
          (gj q)).left ≫
          ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
            (c.π.app j.left) (D.map k.hom) (c.π.app (op i₀))
            (c.w k.hom).symm).app (Y q)).inv.left) ≫
          pullback.fst (Y q).hom (c.π.app (op i₀)) =
        ((d q.1).hom.left ≫ (arrow q).left) ≫
          pullback.fst (Y q).hom (c.π.app (op i₀))
      simp only [Category.assoc]
      have hcomp :
          ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
            (c.π.app j.left) (D.map k.hom) (c.π.app (op i₀))
            (c.w k.hom).symm).app (Y q)).inv.left ≫
            pullback.fst (Y q).hom (c.π.app (op i₀)) =
          pullback.fst (pullback.snd (Y q).hom (D.map k.hom)) (c.π.app j.left) ≫
            pullback.fst (Y q).hom (D.map k.hom) := by
        simp [MorphismProperty.Over.pullbackComp]
      rw [hcomp]
      have hmap :
          ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)).map (gj q)).left ≫
            pullback.fst (pullback.snd (Y q).hom (D.map k.hom)) (c.π.app j.left) =
          pullback.fst (Z q.1).hom (c.π.app j.left) ≫ (gj q).left := by
        exact pullback.lift_fst ..
      rw [← Category.assoc, hmap, Category.assoc]
      have hgj : (gj q).left ≫ pullback.fst (Y q).hom (D.map k.hom) = g q := by
        simp [gj]
      rw [hgj, ← hM q.1]
      simp only [Category.assoc, hg q]
      simp [ψ, d]
    · exact ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)).map (gj q) ≫
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
          (c.π.app j.left) (D.map k.hom) (c.π.app (op i₀))
          (c.w k.hom).symm).app (Y q)).inv).w.trans
          ((d q.1).hom ≫ arrow q).w.symm
  refine ⟨k, Z, (fun q ↦ gj (q, false)), (fun q ↦ gj (q, true)), d,
    hZ, ?_, ?_⟩
  · intro q
    exact heq (q, false)
  · intro q
    exact heq (q, true)

end AlgebraicGeometry
