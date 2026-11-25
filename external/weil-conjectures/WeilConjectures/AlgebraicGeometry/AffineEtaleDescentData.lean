/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Sites.Pullback

import WeilConjectures.AlgebraicGeometry.AffineEtaleFiniteDiagramDescent
import WeilConjectures.AlgebraicGeometry.AffineEtaleCoveringEventually

/-!
# AffineEtaleDescentData

Source: Stacks Project, Étale Cohomology 0EYL; Sites 09YL.
(blueprint: lem-weil-pbc-affine-etale-descent-data).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem covering_iff_jointly_surjective
    {S : Scheme.{u}} {n : ℕ} {A : S.FullAffineEtale}
    (B : Fin n → S.FullAffineEtale) (f : ∀ a, B a ⟶ A) :
    Presieve.ofArrows B f ∈ fullAffineEtalePrecoverage S A ↔
      ∀ x : A.obj.left, ∃ (a : Fin n) (y : (B a).obj.left), (f a).hom.left y = x := by
  constructor
  · rintro ⟨m, V, g, heq, _, hsurj⟩ x
    obtain ⟨a, y, hy⟩ := hsurj x
    have hg : Presieve.ofArrows B f (g a) := heq ▸ Presieve.ofArrows.mk a
    have hfactor : ∀ {W : S.FullAffineEtale} {g : W ⟶ A},
        Presieve.ofArrows B f g → ∀ y : W.obj.left,
          ∃ b z, (f b).hom.left z = g.hom.left y := by
      intro W g hg
      cases hg with
      | mk b => intro y; exact ⟨b, y, rfl⟩
    obtain ⟨b, z, hz⟩ := hfactor hg y
    exact ⟨b, z, hz.trans hy⟩
  · intro hsurj
    exact ⟨n, B, f, rfl, fun _ ↦ inferInstance, hsurj⟩

private theorem covering_of_comparison
    {S : Scheme.{u}} {n : ℕ} {A A' : S.FullAffineEtale}
    (B B' : Fin n → S.FullAffineEtale) (f : ∀ a, B a ⟶ A) (f' : ∀ a, B' a ⟶ A')
    (t : A' ≅ A) (s : ∀ a, B' a ≅ B a)
    (h : ∀ a, f' a ≫ t.hom = (s a).hom ≫ f a)
    (hcov : Presieve.ofArrows B' f' ∈ fullAffineEtalePrecoverage S A') :
    Presieve.ofArrows B f ∈ fullAffineEtalePrecoverage S A := by
  rw [covering_iff_jointly_surjective] at hcov ⊢
  intro x
  obtain ⟨a, y, hy⟩ := hcov (t.inv.hom.left x)
  refine ⟨a, (s a).hom.hom.left y, ?_⟩
  have heq := congrArg (fun g ↦ g.hom.left y) (h a)
  change t.hom.hom.left ((f' a).hom.left y) =
    (f a).hom.left ((s a).hom.hom.left y) at heq
  rw [hy] at heq
  have ht := congrArg (fun g ↦ g.hom.left x) t.inv_hom_id
  change t.hom.hom.left (t.inv.hom.left x) = x at ht
  exact heq.symm.trans ht

/-- Source: Stacks Project, Étale Cohomology 0EYL, proof of the qcqs case;
Limits 01ZM, 01YZ, 01Z6, 07RP, and 07RR.

Proof (steps 5--7 of lem-weil-pbc-affine-etale-site-colimit):
1. Every affine étale object is of finite presentation over the quasi-separated base.
   The limit is qcqs because its projections are affine. Apply 01ZM to descend an object
   to a finite-presentation model. Its base-change tail has the given object as limit
   (01YZ). Apply 01Z6 to make the model affine, then 07RP to make it étale at a later
   stage. Further base changes preserve affineness. The q-pullback squares identify the
   resulting isomorphism with the stated v-presentation.
2. For a map between two v-images, use the q-pullback identifications and 01ZM(2) to
   descend the map. The p-pullback identifications give a map between the U-images.
   The delta first-projection equation and pullback uniqueness identify its image with
   the original map, giving the displayed conjugation formula.
3. Descend the finitely many objects and arrows of a covering by the first two steps,
   taking common upper bounds. The finite disjoint union of its source objects is affine,
   hence qcqs. Its map to the target is étale, hence locally finitely presented. Its
   base change to the limit is surjective. Apply 07RR to make it surjective at a stage;
   this means that the descended family covers. Delta gives the stated comparisons.
4. Conversely, preservation of coverings by v and invariance under the displayed
   source and target isomorphisms show that any such descended covering covers.
   This includes n = 0: the coproduct is empty and 07RR applies to its map.
(blueprint: lem-weil-pbc-affine-etale-descent-data). -/
theorem affineEtale_descent_data
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c)
    (U : ∀ (i j : I), i ≤ j → (D.obj (op i)).FullAffineEtale ⥤
          (D.obj (op j)).FullAffineEtale)
      (v : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ c.pt.FullAffineEtale)
      (p : ∀ (i j : I) (h : i ≤ j),
        U i j h ⋙ fullAffineEtaleInclusion (D.obj (op j)) ⋙
          Etale.forget (D.obj (op j)) ⋙ Over.forget (D.obj (op j)) ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙
          Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)))
      (q : ∀ i : I,
        v i ⋙ fullAffineEtaleInclusion c.pt ⋙ Etale.forget c.pt ⋙ Over.forget c.pt ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙
          Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)))
      (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
        U i j h ⋙ U j k h' ≅ U i k (h.trans h'))
      (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i)
    (h1 : (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
        IsPullback ((p i j h).app A) ((U i j h).obj A).obj.hom
          A.obj.hom (D.map (homOfLE h).op)))
    (h2 : (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale),
        IsPullback ((q i).app A) ((v i).obj A).obj.hom A.obj.hom (c.π.app (op i))))
    (h7 : (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
        ((delta i j h).hom.app A).hom.left ≫ (q i).app A =
          (q j).app ((U i j h).obj A) ≫ (p i j h).app A))
    (h10 : (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
        R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A →
          R.map (U i j h) ∈ fullAffineEtalePrecoverage (D.obj (op j)) ((U i j h).obj A)))
    (h12 : (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
        R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A →
          R.map (v i) ∈ fullAffineEtalePrecoverage c.pt ((v i).obj A)))
    :
      (∀ A : c.pt.FullAffineEtale,
        ∃ (i : I) (Ai : (D.obj (op i)).FullAffineEtale), Nonempty ((v i).obj Ai ≅ A))
      ∧ (∀ (n : ℕ) (A : c.pt.FullAffineEtale) (B : Fin n → c.pt.FullAffineEtale)
        (f : ∀ a : Fin n, B a ⟶ A),
        Presieve.ofArrows B f ∈ fullAffineEtalePrecoverage c.pt A ↔
          ∃ (i : I) (Ai : (D.obj (op i)).FullAffineEtale)
            (Bi : Fin n → (D.obj (op i)).FullAffineEtale) (fi : ∀ a : Fin n, Bi a ⟶ Ai)
            (t : (v i).obj Ai ≅ A) (s : ∀ a : Fin n, (v i).obj (Bi a) ≅ B a),
            Presieve.ofArrows Bi fi ∈ fullAffineEtalePrecoverage (D.obj (op i)) Ai ∧
              ∀ a : Fin n, (v i).map (fi a) ≫ t.hom = (s a).hom ≫ f a) := by
  have _ := gamma
  have _ := h7
  have _ := h10
  have hdiag := affineEtale_finite_diagram_descent D c hc v q h2
  constructor
  · intro A
    obtain ⟨i, Ai, _, _, t, _, _⟩ :=
      hdiag 0 A (fun a ↦ Fin.elim0 a) (fun a ↦ Fin.elim0 a)
    exact ⟨i, Ai, ⟨t⟩⟩
  · intro n A B f
    constructor
    · intro hcov
      obtain ⟨i, Ai, Bi, fi, t, s, heq⟩ := hdiag n A B f
      have hlim : Presieve.ofArrows (fun a ↦ (v i).obj (Bi a))
          (fun a ↦ (v i).map (fi a)) ∈ fullAffineEtalePrecoverage c.pt ((v i).obj Ai) := by
        apply covering_of_comparison (fun a ↦ (v i).obj (Bi a)) B
          (fun a ↦ (v i).map (fi a)) f t.symm (fun a ↦ (s a).symm) _ hcov
        intro a
        apply (cancel_mono t.hom).1
        simpa only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
          Iso.inv_hom_id_assoc] using
            (congrArg (fun g ↦ (s a).inv ≫ g) (heq a)).symm
      obtain ⟨j, hij, hj⟩ := affineEtale_covering_eventually D c hc U v p q h1 h2 i n Ai Bi fi hlim
      refine ⟨j, (U i j hij).obj Ai, (fun a ↦ (U i j hij).obj (Bi a)),
        (fun a ↦ (U i j hij).map (fi a)), (delta i j hij).app Ai ≪≫ t,
        (fun a ↦ (delta i j hij).app (Bi a) ≪≫ s a), hj, ?_⟩
      intro a
      change (v j).map ((U i j hij).map (fi a)) ≫
          (delta i j hij).hom.app Ai ≫ t.hom =
        (delta i j hij).hom.app (Bi a) ≫ (s a).hom ≫ f a
      have hn := (delta i j hij).hom.naturality (fi a)
      change (v j).map ((U i j hij).map (fi a)) ≫ (delta i j hij).hom.app Ai =
        (delta i j hij).hom.app (Bi a) ≫ (v i).map (fi a) at hn
      rw [← Category.assoc, hn, Category.assoc, heq a]
    · rintro ⟨i, Ai, Bi, fi, t, s, hcov, heq⟩
      have hv := h12 i Ai (Presieve.ofArrows Bi fi) hcov
      rw [Presieve.map_ofArrows] at hv
      exact covering_of_comparison B (fun a ↦ (v i).obj (Bi a)) f
        (fun a ↦ (v i).map (fi a)) t s heq hv


end AlgebraicGeometry.Scheme
