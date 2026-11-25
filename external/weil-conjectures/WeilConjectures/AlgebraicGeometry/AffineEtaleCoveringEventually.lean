/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
import WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Eventual covering for a finite affine étale family

Source: Stacks Project, Étale Cohomology 0EYL and Limits 01ZM.
(blueprint: lem-weil-pbc-affine-etale-covering-eventually).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem constructible_baseChange_eventually
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
      (p : Y ⟶ D.obj (op i₀)) (E : Set Y) (hE : Topology.IsConstructible E)
      (himage : Set.range (pullback.fst p (c.π.app (op i₀))) ⊆ E) :
      ∃ (i : I) (hi : i₀ ≤ i),
        Set.range (pullback.fst p (D.map (homOfLE hi).op)) ⊆ E := by
    classical
    let : Nonempty I := ⟨i₀⟩
    let J := {i : I // i₀ ≤ i}
    let j₀ : J := ⟨i₀, le_rfl⟩
    let : Nonempty J := ⟨j₀⟩
    let : IsDirected J (· ≤ ·) := ⟨fun a b ↦ by
      obtain ⟨k, ha, hb⟩ := exists_ge_ge a.val b.val
      exact ⟨⟨k, a.property.trans ha⟩, ha, hb⟩⟩
    let F : Jᵒᵖ ⥤ Over (op i₀) :=
      { obj := fun j ↦ Over.mk (homOfLE j.unop.property).op
        map := fun f ↦ Over.homMk (homOfLE (leOfHom f.unop)).op (by subsingleton) }
    let : F.Faithful := ⟨fun _ ↦ Subsingleton.elim _ _⟩
    let : F.Full := ⟨fun {a b} f ↦
      ⟨(homOfLE (show b.unop ≤ a.unop from leOfHom f.left.unop)).op,
        by ext; apply Subsingleton.elim⟩⟩
    let : F.EssSurj := ⟨fun j ↦ by
      refine ⟨op (⟨j.left.unop, leOfHom j.hom.unop⟩ : J), ⟨?_⟩⟩
      exact Over.isoMk (Iso.refl _) (by subsingleton)⟩
    let : F.IsEquivalence := {}
    let B := F ⋙ baseChangeDiagram D p
    let bc := (baseChangeCone D c p).whisker F
    have hbc : IsLimit bc :=
      (Functor.Initial.isLimitWhiskerEquiv F _).symm (isLimitBaseChangeCone D c p hc)
    let : ∀ j : Jᵒᵖ, CompactSpace (B.obj j) := fun j ↦ by
      change CompactSpace ((baseChangeDiagram D p).obj (F.obj j))
      infer_instance
    let : ∀ j : Jᵒᵖ, QuasiSeparatedSpace (B.obj j) := fun j ↦ by
      change QuasiSeparatedSpace ((baseChangeDiagram D p).obj (F.obj j))
      infer_instance
    let : ∀ {j k : Jᵒᵖ} (f : j ⟶ k), IsAffineHom (B.map f) := fun f ↦ by
      change IsAffineHom ((baseChangeDiagram D p).map (F.map f))
      infer_instance
    have hE' : Topology.IsConstructible
        ((pullback.fst p (D.map (F.obj (op j₀)).hom)) ⁻¹' E) :=
      (pullback.fst p (D.map (F.obj (op j₀)).hom)).isConstructible_preimage hE
    have himage' : Set.range (bc.π.app (op j₀)) ⊆
        ((pullback.fst p (D.map (F.obj (op j₀)).hom)) ⁻¹' E) := by
      rintro _ ⟨x, rfl⟩
      change pullback.fst p (D.map (F.obj (op j₀)).hom)
        ((baseChangeCone D c p).π.app (F.obj (op j₀)) x) ∈ E
      have heq := congrArg (fun f : bc.pt ⟶ Y ↦ f x)
        (baseChangeCone_π_app_fst D c p (F.obj (op j₀)))
      rw [Scheme.Hom.comp_apply] at heq
      exact heq.symm ▸ himage ⟨x, rfl⟩
    obtain ⟨j, hj, hstage⟩ := exists_eventually_range_subset_of_isConstructible
      B bc hbc j₀ _ hE' himage'
    refine ⟨j.val, j.property, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hx := hstage j le_rfl ⟨x, rfl⟩
    change pullback.fst p (D.map (F.obj (op j₀)).hom)
      ((baseChangeDiagram D p).map (F.map (homOfLE (hj.trans le_rfl)).op) x) ∈ E at hx
    have heq := congrArg
      (fun f : (B.obj (op j)) ⟶ Y ↦ f x)
      (baseChangeDiagram_map_fst D p (F.map (homOfLE (hj.trans le_rfl)).op))
    rw [Scheme.Hom.comp_apply] at heq
    exact heq ▸ hx

/-- Source: Stacks Project, Étale Cohomology 0EYL, qcqs case; Limits 07RR,
05F4, and 01YZ; Morphisms 054K.

Proof:
1. Let E be the finite union of the images of the stage arrows fi. Every fi is étale
   between affine schemes, hence finitely presented. Chevalley's theorem makes E
   constructible, also for n = 0 when E is empty.
2. The q-pullback isomorphism for Ai and naturality of q show that the covering of
   v_i(Ai) forces the canonical limit pullback projection to have image in E.
3. Restrict the canonical base-change diagram of Ai to the directed upper tail.
   Its stages are qcqs, its transitions affine, and its limit the pullback to c.pt.
   Pull E back to the initial stage and apply the limit-contained-in-constructible
   theorem. The cone and transition projection identities yield a later j whose
   canonical projection to Ai has image in E.
4. Transfer this containment along the p-pullback isomorphism for Ai. For a point
   of U_ij(Ai), choose a stage arrow fi whose image contains its p-projection.
   The source and target p-squares and naturality make the arrow square a pullback
   by pullback cancellation. The point-lifting theorem for scheme pullbacks gives
   a point in U_ij(Bi) mapping to the chosen point. Thus the U-image family covers.
   For n = 0 the resulting containment in E = empty forces the target empty.
(blueprint: lem-weil-pbc-affine-etale-covering-eventually). -/
theorem affineEtale_covering_eventually
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
    (h1 : (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
        IsPullback ((p i j h).app A) ((U i j h).obj A).obj.hom
          A.obj.hom (D.map (homOfLE h).op)))
    (h2 : (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale),
        IsPullback ((q i).app A) ((v i).obj A).obj.hom A.obj.hom (c.π.app (op i))))
    : ∀ (i : I) (n : ℕ) (Ai : (D.obj (op i)).FullAffineEtale)
        (Bi : Fin n → (D.obj (op i)).FullAffineEtale) (fi : ∀ a : Fin n, Bi a ⟶ Ai),
        Presieve.ofArrows (fun a ↦ (v i).obj (Bi a)) (fun a ↦ (v i).map (fi a)) ∈
          fullAffineEtalePrecoverage c.pt ((v i).obj Ai) →
        ∃ (j : I) (h : i ≤ j),
          Presieve.ofArrows (fun a ↦ (U i j h).obj (Bi a))
            (fun a ↦ (U i j h).map (fi a)) ∈
              fullAffineEtalePrecoverage (D.obj (op j)) ((U i j h).obj Ai) := by
  classical
  intro i n Ai Bi fi hcov
  let hAi : IsAffine Ai.obj.left := Ai.property
  let hBi (a : Fin n) : IsAffine (Bi a).obj.left := (Bi a).property
  let E : Set Ai.obj.left := ⋃ a, Set.range (fi a).hom.left
  have hE : Topology.IsConstructible E := by
    apply Topology.IsConstructible.iUnion
    intro a
    simpa using (fi a).hom.left.isConstructible_image Topology.IsConstructible.univ
  have himage : Set.range (pullback.fst Ai.obj.hom (c.π.app (op i))) ⊆ E := by
    rintro _ ⟨y, rfl⟩
    let e := (h2 i Ai).isoPullback
    obtain ⟨m, V, g, heq, _, hsurj⟩ := hcov
    obtain ⟨a, z, hz⟩ := hsurj (e.inv y)
    have hg : Presieve.ofArrows (fun a ↦ (v i).obj (Bi a))
        (fun a ↦ (v i).map (fi a)) (g a) := heq ▸ Presieve.ofArrows.mk a
    have hfactor : ∀ {W : c.pt.FullAffineEtale} {g : W ⟶ (v i).obj Ai},
        Presieve.ofArrows (fun a ↦ (v i).obj (Bi a))
          (fun a ↦ (v i).map (fi a)) g → ∀ z : W.obj.left,
        ∃ a z', ((v i).map (fi a)).hom.left z' = g.hom.left z := by
      intro W g hg
      cases hg with
      | mk a => intro z; exact ⟨a, z, rfl⟩
    obtain ⟨a, z, hz'⟩ := hfactor hg z
    refine Set.mem_iUnion.mpr ⟨a, (q i).app (Bi a) z, ?_⟩
    have hn := (q i).naturality (fi a)
    change ((v i).map (fi a)).hom.left ≫ (q i).app Ai =
      (q i).app (Bi a) ≫ (fi a).hom.left at hn
    have he := congrArg (fun g ↦ g z) hn
    simp only [Scheme.Hom.comp_apply] at he
    rw [hz', hz] at he
    have hi := congrArg (fun g ↦ g y) ((h2 i Ai).isoPullback_inv_fst)
    exact he.symm.trans hi
  obtain ⟨j, hij, hj⟩ := constructible_baseChange_eventually D c hc i
    (Y := Ai.obj.left) Ai.obj.hom E hE himage
  refine ⟨j, hij, n, (fun a ↦ (U i j hij).obj (Bi a)),
    (fun a ↦ (U i j hij).map (fi a)), rfl, fun _ ↦ inferInstance, ?_⟩
  intro y
  have hy : (p i j hij).app Ai y ∈ E := by
    apply hj
    exact ⟨(h1 i j hij Ai).isoPullback.hom y, by
      exact congrArg (fun g ↦ g y) (h1 i j hij Ai).isoPullback_hom_fst⟩
  obtain ⟨a, z, hz⟩ := Set.mem_iUnion.mp hy
  have hn := (p i j hij).naturality (fi a)
  change ((U i j hij).map (fi a)).hom.left ≫ (p i j hij).app Ai =
    (p i j hij).app (Bi a) ≫ (fi a).hom.left at hn
  have hb := h1 i j hij (Bi a)
  have ha := h1 i j hij Ai
  have hw := (fi a).hom.w
  change (fi a).hom.left ≫ Ai.obj.hom = (Bi a).obj.hom at hw
  have hw' := ((U i j hij).map (fi a)).hom.w
  change ((U i j hij).map (fi a)).hom.left ≫ ((U i j hij).obj Ai).obj.hom =
    ((U i j hij).obj (Bi a)).obj.hom at hw' 
  have houter : IsPullback ((U i j hij).map (fi a)).hom.left
      ((p i j hij).app (Bi a)) ((p i j hij).app Ai) (fi a).hom.left := by
    apply IsPullback.of_right _ hn ha.flip
    simpa only [hw, hw'] using hb.flip
  obtain ⟨z', hz', _⟩ := Scheme.exists_preimage_of_isPullback houter y z hz.symm
  exact ⟨a, z', hz'⟩


end AlgebraicGeometry.Scheme
