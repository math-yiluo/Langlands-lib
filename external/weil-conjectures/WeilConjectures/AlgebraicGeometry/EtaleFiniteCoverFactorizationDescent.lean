/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
import WeilConjectures.AlgebraicGeometry.EtaleFiniteFactorizationDataDescent
import WeilConjectures.AlgebraicGeometry.EtaleFactorizationDataBaseChange
import WeilConjectures.AlgebraicGeometry.AffineEtaleCoveringEventually
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Descent of a finite affine covering with finitely many factorizations

Source: Stacks Project, Étale Cohomology Tag 0EYL (lemma-colimit-affine-sites), and
Limits Tags 01ZM and 01ZC, finite-presentation descent of objects and morphisms.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry


set_option backward.isDefEq.respectTransparency false in
private theorem canonical_covering_eventually
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ j : Iᵒᵖ, CompactSpace (D.obj j)]
    [∀ j : Iᵒᵖ, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (A : (D.obj (op i)).Etale) (hA : IsAffine A.left)
    (n : ℕ) (V : Fin n → (D.obj (op i)).Etale)
    (a : ∀ q, V q ⟶ A) (hV : ∀ q, IsAffine (V q).left)
    (hcov : Sieve.ofArrows
      (fun q ↦ (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i))).obj (V q))
      (fun q ↦ (MorphismProperty.Over.pullback @Etale ⊤
        (c.π.app (op i))).map (a q)) ∈ c.pt.smallEtaleTopology
          ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i))).obj A)) :
    ∃ (j : I) (h : i ≤ j),
      Sieve.ofArrows
        (fun q ↦ (MorphismProperty.Over.pullback @Etale ⊤
          (D.map (homOfLE h).op)).obj (V q))
        (fun q ↦ (MorphismProperty.Over.pullback @Etale ⊤
          (D.map (homOfLE h).op)).map (a q)) ∈ (D.obj (op j)).smallEtaleTopology
            ((MorphismProperty.Over.pullback @Etale ⊤
              (D.map (homOfLE h).op)).obj A) := by
  classical
  have : ∀ j, IsAffineHom (c.π.app j) := isAffineHom_π_app D c hc
  let T {S R : Scheme.{u}} (f : R ⟶ S) [IsAffineHom f] :
      S.FullAffineEtale ⥤ R.FullAffineEtale :=
    { obj := fun Z : S.FullAffineEtale ↦
        ⟨(MorphismProperty.Over.pullback @Etale ⊤ f).obj Z.obj, by
          let : IsAffine ((𝟭 Scheme).obj Z.obj.left) := Z.property
          change IsAffine (pullback Z.obj.hom f)
          infer_instance⟩
      map := fun g ↦ ⟨(MorphismProperty.Over.pullback @Etale ⊤ f).map g.hom⟩
      map_id := fun _ ↦ by ext; simp
      map_comp := fun _ _ ↦ by ext; simp }
  let U := fun (i j : I) (h : i ≤ j) ↦ T (D.map (homOfLE h).op)
  let v := fun i : I ↦ T (c.π.app (op i))
  let p (i j : I) (h : i ≤ j) :
      U i j h ⋙ Scheme.fullAffineEtaleInclusion (D.obj (op j)) ⋙
        Scheme.Etale.forget (D.obj (op j)) ⋙ Over.forget (D.obj (op j)) ⟶
      Scheme.fullAffineEtaleInclusion (D.obj (op i)) ⋙
        Scheme.Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)) :=
    { app := fun Z ↦ pullback.fst Z.obj.hom (D.map (homOfLE h).op)
      naturality := fun X Y g ↦ by
        change ((MorphismProperty.Over.pullback @Etale ⊤
          (D.map (homOfLE h).op)).map g.hom).left ≫
            pullback.fst Y.obj.hom (D.map (homOfLE h).op) =
          pullback.fst X.obj.hom (D.map (homOfLE h).op) ≫ g.hom.left
        simp [MorphismProperty.Over.pullback_map_left] }
  let q (i : I) :
      v i ⋙ Scheme.fullAffineEtaleInclusion c.pt ⋙
        Scheme.Etale.forget c.pt ⋙ Over.forget c.pt ⟶
      Scheme.fullAffineEtaleInclusion (D.obj (op i)) ⋙
        Scheme.Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)) :=
    { app := fun Z ↦ pullback.fst Z.obj.hom (c.π.app (op i))
      naturality := fun X Y g ↦ by
        change ((MorphismProperty.Over.pullback @Etale ⊤
          (c.π.app (op i))).map g.hom).left ≫
            pullback.fst Y.obj.hom (c.π.app (op i)) =
          pullback.fst X.obj.hom (c.π.app (op i)) ≫ g.hom.left
        simp [MorphismProperty.Over.pullback_map_left] }
  let Ai : (D.obj (op i)).FullAffineEtale := ⟨A, hA⟩
  let Vi : Fin n → (D.obj (op i)).FullAffineEtale := fun q ↦ ⟨V q, hV q⟩
  let ai : ∀ q, Vi q ⟶ Ai := fun q ↦ ⟨a q⟩
  have hcov' : Presieve.ofArrows (fun q ↦ (v i).obj (Vi q))
      (fun q ↦ (v i).map (ai q)) ∈
        Scheme.fullAffineEtalePrecoverage c.pt ((v i).obj Ai) := by
    refine ⟨n, _, _, rfl, fun _ ↦ inferInstance, ?_⟩
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at hcov
    intro x
    have hx : x ∈ ⋃ q, Set.range
        ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i))).map (a q)).left := by
      rw [hcov]
      trivial
    exact Set.mem_iUnion.mp hx
  obtain ⟨j, hij, hj⟩ := Scheme.affineEtale_covering_eventually D c hc U v p q
    (fun _ _ _ _ ↦ IsPullback.of_hasPullback _ _)
    (fun _ _ ↦ IsPullback.of_hasPullback _ _) i n Ai Vi ai hcov'
  refine ⟨j, hij, ?_⟩
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  obtain ⟨m, B, f, heq, _, hsurj⟩ := hj
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨r, z, hz⟩ := hsurj x
  have hf : Presieve.ofArrows (fun q ↦ (U i j hij).obj (Vi q))
      (fun q ↦ (U i j hij).map (ai q)) (f r) := heq ▸ Presieve.ofArrows.mk r
  have hfactor : ∀ {Z : (D.obj (op j)).FullAffineEtale}
      {g : Z ⟶ (U i j hij).obj Ai},
      Presieve.ofArrows (fun q ↦ (U i j hij).obj (Vi q))
        (fun q ↦ (U i j hij).map (ai q)) g → ∀ z : Z.obj.left,
      ∃ q z', ((U i j hij).map (ai q)).hom.left z' = g.hom.left z := by
    intro Z g hg
    cases hg with
    | mk q => intro z; exact ⟨q, z, rfl⟩
  obtain ⟨r', z', hz'⟩ := hfactor hf z
  exact Set.mem_iUnion.mpr ⟨r', z', hz'.trans hz⟩

set_option backward.isDefEq.respectTransparency false in
private theorem covering_of_iso
    {S : Scheme.{u}} {n : ℕ} {A A' : S.Etale}
    (V V' : Fin n → S.Etale) (a : ∀ q, V q ⟶ A) (a' : ∀ q, V' q ⟶ A')
    (t : A ≅ A') (d : ∀ q, V q ≅ V' q)
    (heq : ∀ q, a q ≫ t.hom = (d q).hom ≫ a' q)
    (ha : Sieve.ofArrows V a ∈ S.smallEtaleTopology A) :
    Sieve.ofArrows V' a' ∈ S.smallEtaleTopology A' := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at ha ⊢
  apply Set.eq_univ_of_forall
  intro x
  have hx : t.inv.left x ∈ ⋃ q, Set.range (a q).left := by rw [ha]; trivial
  obtain ⟨q, y, hy⟩ := Set.mem_iUnion.mp hx
  refine Set.mem_iUnion.mpr ⟨q, (d q).hom.left y, ?_⟩
  have he := congrArg (fun f ↦ f.left y) (heq q)
  change t.hom.left ((a q).left y) = (a' q).left ((d q).hom.left y) at he
  rw [hy] at he
  have ht := congrArg (fun f ↦ f.left x) t.inv_hom_id
  change t.hom.left (t.inv.left x) = x at ht
  exact he.symm.trans ht

set_option backward.isDefEq.respectTransparency false in
/-- A finite affine covering of a fixed base-changed object, together with one map from
 each covering object into a base-changed original étale object, descends to a common
 stage. This is a geometric assertion: it contains no sheaf or section.

Source: Stacks Project, Étale Cohomology Tag 0EYL (lemma-colimit-affine-sites), qcqs case,
and Limits Tags 01ZM and 01ZC, descent of finite-presentation objects and arrows.
(blueprint: lem-weil-pbc-etale-finite-cover-factorization-descent).

Proof: Work on the cofinal tail above i₀. Each affine étale V_q has finite presentation
 over the qcqs limit scheme. Descend its object and its arrow into the fixed affine
 W using the object and arrow clauses of the affine étale site colimit. For each
 arrow b_q into the possibly non-affine base change of U_q, consider the inverse
 system of base changes of the descended affine source on its tail. Its transition
 maps are affine, its terms are affine (hence qcqs), and its limit is V_q by base
 change of limits. Composing b_q with the projection to U_q gives a morphism over
 the original base D(i₀). The structure morphism of U_q is étale, hence locally
 of finite presentation. Apply 01ZC(3), or Mathlib's
 Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation, to descend this
 morphism over D(i₀). The pullback universal property converts it to a map
 into the stage base change of U_q. No quasi-compactness or separation assumption
 on U_q is needed. Choose a common stage for this finite collection of
 data and equations. The maps to W and U_q then base change to a_q and b_q under
 the same source isomorphism d_q; these are the displayed equations with the
 canonical pullback-composition isomorphisms. Finally the finite union of images
 of the descended arrows to W is constructible. Since it covers W at the limit,
 covering descent makes it cover at a later stage. Base change preserves the
 factorization equations and affineness. When n = 0, covering descent says that
 the fixed test object becomes empty at a later stage; no factorization data is
 required. -/
theorem etale_finiteCoverFactorizationDescent
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
    (ha : Sieve.ofArrows V a ∈ c.pt.smallEtaleTopology
      ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W.obj))
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
      Sieve.ofArrows Vj aj ∈ (D.obj j.left).smallEtaleTopology ((F j).obj W.obj) ∧
      (∀ q, IsAffine (Vj q).left) ∧
      (∀ q, (B j).map (aj q) ≫ (e j W.obj).inv = (d q).hom ≫ a q) ∧
      (∀ q, (B j).map (bj q) ≫ (e j (U q)).inv = (d q).hom ≫ b q) := by
  classical
  dsimp only
  obtain ⟨j, Vj, aj, bj, d, hVj, haj, hbj⟩ :=
    etale_finiteFactorizationDataDescent D c hc i₀ W n V a U b hV
  let B := fun j : Over (op i₀) ↦ MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)
  let F := fun j : Over (op i₀) ↦ MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)
  let e := fun (j : Over (op i₀)) (Z : (D.obj (op i₀)).Etale) ↦
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      (c.π.app j.left) (D.map j.hom) (c.π.app (op i₀)) (c.w j.hom).symm).app Z
  have hlim : Sieve.ofArrows (fun q ↦ (B j).obj (Vj q))
      (fun q ↦ (B j).map (aj q)) ∈ c.pt.smallEtaleTopology ((B j).obj ((F j).obj W.obj)) := by
    apply covering_of_iso V (fun q ↦ (B j).obj (Vj q)) a
      (fun q ↦ (B j).map (aj q)) (e j W.obj) (fun q ↦ (d q).symm) _ ha
    intro q
    apply (cancel_mono (e j W.obj).inv).mp
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using
      (congrArg (fun f ↦ (d q).inv ≫ f) (haj q)).symm
  have hWj : IsAffine ((F j).obj W.obj).left := by
    let : IsAffine ((𝟭 Scheme).obj W.obj.left) := W.property
    change IsAffine (pullback W.obj.hom (D.map j.hom))
    infer_instance
  obtain ⟨k, hjk, hcover⟩ := canonical_covering_eventually D c hc j.left.unop
    ((F j).obj W.obj) hWj n Vj aj hVj hlim
  let k' : Over (op i₀) := Over.mk ((homOfLE hjk).op ≫ j.hom)
  let t : k' ⟶ j := Over.homMk (homOfLE hjk).op
  obtain ⟨ak, bk, dk, tw, hak, hbk, htw⟩ :=
    etale_factorizationData_baseChange D c i₀ W n V a U b j k' t Vj aj bj d haj hbj
  let P := MorphismProperty.Over.pullback @Etale ⊤ (D.map (homOfLE hjk).op)
  refine ⟨k', (fun q ↦ P.obj (Vj q)), ak, bk, dk, ?_, ?_, hak, hbk⟩
  · apply covering_of_iso (fun q ↦ P.obj (Vj q)) (fun q ↦ P.obj (Vj q))
      (fun q ↦ P.map (aj q)) ak tw (fun q ↦ Iso.refl _) _ hcover
    intro q
    exact (htw q).trans (Category.id_comp _).symm
  · intro q
    let : IsAffine ((𝟭 Scheme).obj (Vj q).left) := hVj q
    change IsAffine (pullback (Vj q).hom (D.map (homOfLE hjk).op))
    infer_instance

end AlgebraicGeometry
