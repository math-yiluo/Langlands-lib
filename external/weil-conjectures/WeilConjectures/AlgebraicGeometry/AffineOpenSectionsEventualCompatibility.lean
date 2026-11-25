/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.EtaleUnitZeroNeighbourhood
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Pairwise eventual agreement of inverse-image representatives -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem affine_stage_open_containment
    {X : Scheme.{u + 1}} {J : Type (u + 1)} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ X.Etale) [∀ j, IsAffine (D.obj j).left]
    (c : Cone (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X)) (hc : IsLimit c)
    (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ (D.obj j).hom = p)
    (j : J) (V : X.Etale) (v : V ⟶ D.obj j) [IsAffine V.left]
    (U : V.left.Opens)
    (hU : Set.range (pullback.fst V.hom p) ⊆ (U : Set V.left)) :
    ∃ (k : J) (f : k ⟶ j),
      Set.range (pullback.fst v.left (D.map f).left) ⊆ (U : Set V.left) := by
  let E := D ⋙ Scheme.Etale.forget X ⋙ Over.forget X
  have : ∀ i, IsAffine (E.obj i) := fun i ↦ inferInstanceAs (IsAffine (D.obj i).left)
  have : ∀ {i k : J} (f : i ⟶ k), IsAffineHom (E.map f) := fun f ↦
    inferInstanceAs (IsAffineHom (D.map f).left)
  let B := baseChangeDiagram E v.left
  let d := baseChangeCone E c v.left
  have : ∀ i, CompactSpace (B.obj i) := fun i ↦ inferInstance
  have ht : d.π.app (Over.mk (𝟙 j)) ⁻¹ᵁ
      (pullback.fst v.left (E.map (𝟙 j)) ⁻¹ᵁ U) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    have hfac : pullback.fst v.left (c.π.app j) ≫ V.hom =
        pullback.snd v.left (c.π.app j) ≫ p := by
      have hv : v.left ≫ (D.obj j).hom = V.hom := v.w
      erw [← hv, ← Category.assoc, pullback.condition, Category.assoc, hp j]
    let b := pullback.lift (pullback.fst v.left (c.π.app j))
      (pullback.snd v.left (c.π.app j)) hfac
    have hx := hU ⟨b x, rfl⟩
    have hb : b ≫ pullback.fst V.hom p = pullback.fst v.left (c.π.app j) :=
      pullback.lift_fst _ _ _
    rw [← Scheme.Hom.comp_apply, hb] at hx
    change ((d.π.app (Over.mk (𝟙 j))) ≫
      pullback.fst v.left (E.map (𝟙 j))) x ∈ U
    dsimp only [d]
    erw [baseChangeCone_π_app_fst]
    exact hx
  obtain ⟨k, f, hf⟩ := exists_map_eq_top B d
    (isLimitBaseChangeCone E c v.left hc) _ ht
  refine ⟨k.left, k.hom, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx := hf.ge (Set.mem_univ x)
  change ((B.map f) ≫ pullback.fst v.left (E.map (𝟙 j))) x ∈ U at hx
  dsimp only [B] at hx
  erw [baseChangeDiagram_map_fst] at hx
  exact hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Two affine local representatives with the same inverse-image section agree over
some later stage, without constructing or choosing a covering refinement.
Source: Stacks Project, Tags 03Q6 and 09XM, equality-open and limit-containment arguments.
(blueprint: lem-weil-pbc-affine-open-inverse-image-compatible-refinement-compatibility).

Proof: Form the affine overlap of V and W over D(j) and subtract the restricted
sections. After base change to the limit its unit is zero, by naturality of the unit
and the uniqueness of maps to the terminal object. Localize the adjunction to that
base-changed overlap; the zero-neighbourhood theorem gives an open containing its
limit image on which the difference is zero. On the cofiltered tail over j, the
base-changed overlaps form an affine-transition diagram of compact affine schemes.
Its limit is the base change of the overlap to c.pt, by the pullback universal
property. Eventual containment in the agreement open supplies k and f:k→j.
Any test object with a map to D(k) and compatible maps to V and W maps to this
base-changed overlap, so restriction of the zero difference gives the equality.
For an empty overlap all sections are zero; no nonemptiness assumption is used. -/
theorem affineOpenSections_pair_eventual_agreement
    {X : Scheme.{u + 1}} {J : Type (u + 1)} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ X.Etale)
    [∀ j, IsAffine (D.obj j).left] [∀ j, IsOpenImmersion (D.obj j).hom]
    (c : Cone (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X))
    (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ (D.obj j).hom = p)
    (hc : IsLimit c)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology c.pt.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (t : (H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt))))
    (j : J) (V W : X.Etale) (v : V ⟶ D.obj j) (w : W ⟶ D.obj j)
    (s : F.obj.obj (op V)) (r : F.obj.obj (op W))
    (πV : p.Etale.obj V ⟶ Scheme.Etale.mk (𝟙 c.pt))
    (πW : p.Etale.obj W ⟶ Scheme.Etale.mk (𝟙 c.pt))
    (hV : IsAffine V.left) (hW : IsAffine W.left)
    (hs : (H.obj F).obj.map πV.op t = (hH.unit.app F).hom.app (op V) s)
    (hr : (H.obj F).obj.map πW.op t = (hH.unit.app F).hom.app (op W) r) :
    ∃ (k : J) (f : k ⟶ j),
      ∀ (U : X.Etale) (a : U ⟶ V) (a' : U ⟶ W) (q : U ⟶ D.obj k),
        a ≫ v = q ≫ D.map f → a' ≫ w = q ≫ D.map f →
        F.obj.map a.op s = F.obj.map a'.op r := by
  let := hV
  let := hW
  let O : X.Etale := Scheme.Etale.mk
    (pullback.fst v.left w.left ≫ V.hom)
  let b : O ⟶ V := MorphismProperty.Over.homMk (pullback.fst v.left w.left) rfl
  let b' : O ⟶ W := MorphismProperty.Over.homMk (pullback.snd v.left w.left) (by
    change pullback.snd v.left w.left ≫ W.hom =
      pullback.fst v.left w.left ≫ V.hom
    have hv : v.left ≫ (D.obj j).hom = V.hom := v.w
    have hw : w.left ≫ (D.obj j).hom = W.hom := w.w
    rw [← hv, ← hw, ← Category.assoc, ← Category.assoc, pullback.condition])
  let z : F.obj.obj (op O) := F.obj.map b.op s - F.obj.map b'.op r
  have hz : (hH.unit.app F).hom.app (op O) z = 0 := by
    have hn := (hH.unit.app F).hom.naturality b.op
    have hn' := (hH.unit.app F).hom.naturality b'.op
    change F.obj.map b.op ≫ (hH.unit.app F).hom.app (op O) =
      (hH.unit.app F).hom.app (op V) ≫
        (H.obj F).obj.map (p.Etale.map b).op at hn
    change F.obj.map b'.op ≫ (hH.unit.app F).hom.app (op O) =
      (hH.unit.app F).hom.app (op W) ≫
        (H.obj F).obj.map (p.Etale.map b').op at hn'
    have he : p.Etale.map b ≫ πV = p.Etale.map b' ≫ πW := by
      apply MorphismProperty.Over.Hom.ext
      have h1 := (p.Etale.map b ≫ πV).w
      have h2 := (p.Etale.map b' ≫ πW).w
      change (p.Etale.map b ≫ πV).left ≫ 𝟙 c.pt = _ at h1
      change (p.Etale.map b' ≫ πW).left ≫ 𝟙 c.pt = _ at h2
      erw [Category.comp_id] at h1 h2
      exact h1.trans h2.symm
    dsimp only [z]
    rw [map_sub]
    apply sub_eq_zero.mpr
    have hnₛ := congrArg (fun f ↦ f s) hn
    have hnᵣ := congrArg (fun f ↦ f r) hn'
    simp only [AddCommGrpCat.comp_apply] at hnₛ hnᵣ
    erw [hnₛ, hnᵣ, ← hs, ← hr]
    change ((H.obj F).obj.map πV.op ≫ (H.obj F).obj.map (p.Etale.map b).op) t =
      ((H.obj F).obj.map πW.op ≫ (H.obj F).obj.map (p.Etale.map b').op) t
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, he]
  obtain ⟨A, hA, hzero⟩ := etaleUnit_zero_neighbourhood p H hH F O z hz
  have : IsAffine O.left := inferInstanceAs (IsAffine (pullback v.left w.left))
  obtain ⟨k, f, hf⟩ := affine_stage_open_containment D c hc p hp j O (b ≫ v) A hA
  refine ⟨k, f, ?_⟩
  intro U a a' q ha ha'
  let l : U.left ⟶ O.left := pullback.lift a.left a'.left (by
    have h1 := congrArg (fun z : U ⟶ D.obj j ↦ z.left) ha
    have h2 := congrArg (fun z : U ⟶ D.obj j ↦ z.left) ha'
    exact h1.trans h2.symm)
  let d : U ⟶ O := MorphismProperty.Over.homMk l (by
    change l ≫ (pullback.fst v.left w.left ≫ V.hom) = U.hom
    rw [← Category.assoc, pullback.lift_fst]
    exact a.w)
  have hdb : d ≫ b = a := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_fst _ _ _
  have hdb' : d ≫ b' = a' := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_snd _ _ _
  have hd : Set.range d.left ⊆ (A : Set O.left) := by
    let e := pullback.lift d.left q.left (by
      have h := congrArg (fun z : U ⟶ D.obj j ↦ z.left) ha
      change d.left ≫ (b.left ≫ v.left) = q.left ≫ (D.map f).left
      rw [← Category.assoc]
      have hba := congrArg (fun z : U ⟶ V ↦ z.left) hdb
      change d.left ≫ b.left = a.left at hba
      rw [hba]
      exact h)
    rintro _ ⟨x, rfl⟩
    have hx := hf ⟨e x, rfl⟩
    have he : e ≫ pullback.fst (b ≫ v).left (D.map f).left = d.left :=
      pullback.lift_fst _ _ _
    change (e ≫ pullback.fst (b ≫ v).left (D.map f).left) x ∈ A at hx
    erw [he] at hx
    exact hx
  let gleft := IsOpenImmersion.lift A.ι d.left (by
    rw [Scheme.Opens.range_ι]
    exact hd)
  let g : U ⟶ Scheme.Etale.mk (A.ι ≫ O.hom) :=
    MorphismProperty.Over.homMk gleft (by
      change gleft ≫ (A.ι ≫ O.hom) = U.hom
      rw [← Category.assoc]
      dsimp only [gleft]
      rw [IsOpenImmersion.lift_fac]
      exact d.w)
  let i : Scheme.Etale.mk (A.ι ≫ O.hom) ⟶ O :=
    MorphismProperty.Over.homMk A.ι rfl
  have hgi : g ≫ i = d := by
    apply MorphismProperty.Over.Hom.ext
    exact IsOpenImmersion.lift_fac _ _ _
  have hdz : F.obj.map d.op z = 0 := by
    rw [← hgi, op_comp, Functor.map_comp, AddCommGrpCat.comp_apply]
    change F.obj.map g.op (F.obj.map i.op z) = 0
    rw [hzero, map_zero]
  dsimp only [z] at hdz
  rw [map_sub] at hdz
  apply sub_eq_zero.mp
  simpa only [← AddCommGrpCat.comp_apply, ← Functor.map_comp, ← op_comp,
    hdb, hdb'] using hdz
