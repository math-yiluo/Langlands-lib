/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import Mathlib.Data.Fintype.Order

/-! # Descent of a finite qcqs étale diagram

Source: Stacks Project, Limits, Tags 01ZM and 07RP.
(blueprint: lem-weil-pbc-etale-limit-finite-diagram-descent). -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
open Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem qcqs_etale_single_model
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (X : c.pt.Etale)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] :
    ∃ (i : I) (Xi : (D.obj (op i)).Etale)
      (r : X.left ⟶ Xi.left),
      IsPullback r X.hom Xi.hom (c.π.app (op i)) ∧
      CompactSpace Xi.left ∧ QuasiSeparatedSpace Xi.left := by
  classical
  let : CompactSpace ((𝟭 Scheme).obj X.left) := inferInstanceAs (CompactSpace X.left)
  let : QuasiSeparatedSpace ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (QuasiSeparatedSpace X.left)
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have : IsAffineHom (c.π.app (op i₀)) := isAffineHom_π_app D c hc (op i₀)
  have : QuasiSeparatedSpace c.pt :=
    quasiSeparatedSpace_of_quasiSeparated (c.π.app (op i₀))
  let : QuasiSeparatedSpace ((Functor.fromPUnit c.pt).obj X.right) :=
    inferInstanceAs (QuasiSeparatedSpace c.pt)
  have : QuasiCompact X.hom := quasiCompact_of_compactSpace X.hom
  have : QuasiSeparated X.hom := QuasiSeparated.of_quasiSeparatedSpace X.hom
  obtain ⟨i, Y, p, hp, hqc, hqs, r, hr⟩ :=
    exists_isPullback_of_finitePresentation hc X.hom
  have := hp
  have := hqc
  have := hqs
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  let p' := p
  let j := i
  have hr' := hr
  have : Etale (pullback.snd p' (c.π.app j)) :=
    (MorphismProperty.cancel_left_of_respectsIso @Etale hr'.isoPullback.hom
      (pullback.snd p' (c.π.app j))).mp (by
        rw [hr'.isoPullback_hom_snd]
        infer_instance)
  let X₀ : Over (D.obj j) := Over.mk p'
  let Y₀ : Over (D.obj j) := Over.mk (𝟙 _)
  let f₀ : X₀ ⟶ Y₀ := Over.homMk p'
  have hf : Etale (((Over.pullback (c.π.app j)).map f₀).left) := by
    have hcomp : Etale (((Over.pullback (c.π.app j)).map f₀).left ≫
        pullback.snd (𝟙 _) (c.π.app j)) := by
      simpa [X₀, Y₀, f₀, Over.pullback] using
        (inferInstanceAs (Etale (pullback.snd p' (c.π.app j))))
    exact Etale.of_comp _ (pullback.snd (𝟙 _) (c.π.app j))
  let : CompactSpace X₀.left := inferInstanceAs
    (CompactSpace Y)
  let : QuasiSeparatedSpace X₀.left := inferInstanceAs
    (QuasiSeparatedSpace Y)
  let : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj j))
  let : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj j))
  have : LocallyOfFinitePresentation f₀.left := inferInstanceAs
    (LocallyOfFinitePresentation p')
  obtain ⟨k, hk, het⟩ := Etale.exists_stage_of_inverseLimit D c hc j.unop
    X₀ Y₀ f₀ hf
  have := het
  have hpk : Etale (pullback.snd p' (D.map (homOfLE hk).op)) := by
    have hcomp : Etale (((Over.pullback (D.map (homOfLE hk).op)).map f₀).left ≫
        pullback.snd (𝟙 _) (D.map (homOfLE hk).op)) := inferInstance
    simpa [X₀, Y₀, f₀, Over.pullback] using hcomp
  let p'' := pullback.snd p' (D.map (homOfLE hk).op)
  let Xi : (D.obj (op k)).Etale := MorphismProperty.Over.mk ⊤ p'' hpk
  refine ⟨k, Xi, isPullbackLift D c (homOfLE hk).op hr',
    isPullback_isPullbackLift (homOfLE hk).op hr', ?_, ?_⟩
  · exact QuasiCompact.compactSpace_of_compactSpace p''
  · exact quasiSeparatedSpace_of_quasiSeparated p''


private theorem finite_qcqs_pullback_hom_descent
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i : I) (K : Type (u + 1)) [Finite K]
    (V : K → Scheme.{u}) (W : Scheme.{u})
    (pV : ∀ a, V a ⟶ D.obj (op i)) (pW : W ⟶ D.obj (op i))
    [∀ a, LocallyOfFinitePresentation (pV a)] [∀ a, QuasiCompact (pV a)]
    [∀ a, QuasiSeparated (pV a)]
    [LocallyOfFinitePresentation pW] [QuasiCompact pW] [QuasiSeparated pW]
    (ψ : ∀ a, pullback (pV a) (c.π.app (op i)) ⟶ W)
    (hψ : ∀ a, ψ a ≫ pW = pullback.fst (pV a) (c.π.app (op i)) ≫ pV a) :
    ∃ (j : I) (h : i ≤ j)
      (ψj : ∀ a, pullback (pV a) (D.map (homOfLE h).op) ⟶ W),
      (∀ a, ψj a ≫ pW = pullback.fst (pV a) (D.map (homOfLE h).op) ≫ pV a) ∧
      ∀ a,
        pullback.map (pV a) (c.π.app (op i)) (pV a) (D.map (homOfLE h).op)
          (𝟙 _) (c.π.app (op j)) (𝟙 _) (by simp) (by simp) ≫ ψj a = ψ a  := by
  classical
  have hex (a : K) := Scheme.exists_pullback_hom_of_isLimit hc (pV a) pW (ψ a) (hψ a)
  choose k b θ hθ heq using hex
  obtain ⟨l, hl⟩ := Finite.bddAbove_range (fun a ↦ (k a).unop)
  obtain ⟨j, hij, hlj⟩ := exists_ge_ge i l
  have hkj (a : K) : (k a).unop ≤ j := le_trans (hl ⟨a, rfl⟩) hlj
  let m (a : K) : op j ⟶ k a := (homOfLE (hkj a)).op
  have hf (a : K) : D.map (homOfLE hij).op = D.map (m a) ≫ D.map (b a) := by
    rw [← D.map_comp]
    congr 1
  let M (a : K) := pullback.map (pV a) (D.map (homOfLE hij).op)
    (pV a) (D.map (b a)) (𝟙 _) (D.map (m a)) (𝟙 _) (by simp) (by simp [hf a])
  refine ⟨j, hij, (fun a ↦ M a ≫ θ a), ?_, ?_⟩
  · intro a
    simp only [Category.assoc, hθ a]
    dsimp [M]
    simp
  · intro a
    have hm : pullback.map (pV a) (c.π.app (op i)) (pV a)
        (D.map (homOfLE hij).op) (𝟙 _) (c.π.app (op j)) (𝟙 _)
        (by simp) (by simp) ≫ M a =
        pullback.map (pV a) (c.π.app (op i)) (pV a) (D.map (b a))
          (𝟙 _) (c.π.app (k a)) (𝟙 _) (by simp) (by simp) := by
      apply pullback.hom_ext
      · simp [M]
      · simp [M, c.w (m a)]
    rw [← Category.assoc, hm]
    exact heq a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Descend a finite star diagram, without a covering assumption or conclusion.
Source: Stacks Project, Limits, Tags 01ZM(1),(2) and 07RP.
(blueprint: lem-weil-pbc-etale-limit-finite-diagram-descent).

Proof: Affine-limit permanence gives a qcqs limit base. The qcqs sources and
étale structure maps make every object finitely presented over this base.
Apply 01ZM(1) to U and each V_k. The resulting finitely presented models over
qcqs stages are qcqs. Apply 07RP to their structure maps to make them étale,
then take a common upper bound of the finitely many stages, including U's stage.
Base change preserves étaleness and the qcqs properties; pullback composition
retains the identifications with U and V_k. For each k, conjugate f_k by these
identifications to obtain an arrow between the limit pullbacks of the fixed
models. Apply 01ZM(2) to descend this arrow. Take a common upper bound of these
finitely many arrow stages and pull back all models and arrows to it. Naturality
of pullback composition gives the displayed equations. For empty K only U is
spread out and the arrow and source clauses are vacuous. No surjectivity is used. -/
theorem exists_etale_limit_finite_diagram_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (U : c.pt.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (K : Type (u + 1)) [Finite K] (V : K → c.pt.Etale) (f : ∀ k, V k ⟶ U)
    (hV : ∀ k, CompactSpace (V k).left ∧ QuasiSeparatedSpace (V k).left)
    :
    ∃ (i₀ : I) (U₀ : (D.obj (op i₀)).Etale)
    (V₀ : K → (D.obj (op i₀)).Etale) (f₀ : ∀ k, V₀ k ⟶ U₀)
    (eU : (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj U₀ ≅ U)
    (eV : ∀ k,
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj (V₀ k) ≅ V k),
    (CompactSpace U₀.left ∧ QuasiSeparatedSpace U₀.left) ∧
    (∀ k, CompactSpace (V₀ k).left ∧ QuasiSeparatedSpace (V₀ k).left) ∧
    (∀ k, (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).map (f₀ k) ≫
      eU.hom = (eV k).hom ≫ f k) := by
  classical
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a) := fun a ↦ inferInstance
  let X : Option K → c.pt.Etale := fun a ↦ a.elim U V
  have hXc (a : Option K) : CompactSpace (X a).left := by
    cases a with
    | none => exact inferInstanceAs (CompactSpace U.left)
    | some k => exact (hV k).1
  have hXs (a : Option K) : QuasiSeparatedSpace (X a).left := by
    cases a with
    | none => exact inferInstanceAs (QuasiSeparatedSpace U.left)
    | some k => exact (hV k).2
  have hm (a : Option K) := qcqs_etale_single_model D c hc (X a)
  choose i Xi r hr hcXi hsXi using hm
  obtain ⟨j, hj⟩ := Finite.bddAbove_range i
  have h (a : Option K) : i a ≤ j := hj ⟨a, rfl⟩
  let Y (a : Option K) :=
    (MorphismProperty.Over.pullback @Etale ⊤ (D.map (homOfLE (h a)).op)).obj (Xi a)
  have hYc (a : Option K) : CompactSpace (Y a).left :=
    @QuasiCompact.compactSpace_of_compactSpace _ _
      (pullback.fst (Xi a).hom (D.map (homOfLE (h a)).op)) inferInstance (hcXi a)
  have hYs (a : Option K) : QuasiSeparatedSpace (Y a).left :=
    @quasiSeparatedSpace_of_quasiSeparated _ _
      (pullback.fst (Xi a).hom (D.map (homOfLE (h a)).op)) (hsXi a) inferInstance
  have hY (a : Option K) := isPullback_isPullbackLift (homOfLE (h a)).op (hr a)
  let e (a : Option K) :
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op j))).obj (Y a) ≅ X a :=
    MorphismProperty.Over.isoMk (hY a).isoPullback.symm (by
      exact (hY a).isoPullback_inv_snd)
  let A := Y none
  let B : K → (D.obj (op j)).Etale := fun k ↦ Y (some k)
  let L := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op j))
  let g : ∀ k, L.obj (B k) ⟶ L.obj A :=
    fun k ↦ (e (some k)).hom ≫ f k ≫ (e none).inv
  let ψ : ∀ k, pullback (B k).hom (c.π.app (op j)) ⟶ A.left :=
    fun k ↦ (g k).left ≫ pullback.fst A.hom (c.π.app (op j))
  have hψ (k : K) : ψ k ≫ A.hom =
      pullback.fst (B k).hom (c.π.app (op j)) ≫ (B k).hom := by
    dsimp [ψ]
    have hw : (g k).left ≫ pullback.snd A.hom (c.π.app (op j)) =
        pullback.snd (B k).hom (c.π.app (op j)) := MorphismProperty.Over.w (g k)
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw, ← pullback.condition]
  have hAc : QuasiCompact A.hom :=
    @quasiCompact_of_compactSpace A.left (D.obj (op j)) A.hom (hYc none) inferInstance
  have hAs : QuasiSeparated A.hom :=
    @QuasiSeparated.of_quasiSeparatedSpace A.left (D.obj (op j)) A.hom (hYs none)
  have hBc (k : K) : QuasiCompact (B k).hom :=
    @quasiCompact_of_compactSpace (B k).left (D.obj (op j)) (B k).hom
      (hYc (some k)) inferInstance
  have hBs (k : K) : QuasiSeparated (B k).hom :=
    @QuasiSeparated.of_quasiSeparatedSpace (B k).left (D.obj (op j)) (B k).hom
      (hYs (some k))
  obtain ⟨l, hjl, ψl, hψl, hdesc⟩ := finite_qcqs_pullback_hom_descent D c hc j K
    (fun k ↦ (B k).left) A.left (fun k ↦ (B k).hom) A.hom ψ hψ
  let q := D.map (homOfLE hjl).op
  let F := MorphismProperty.Over.pullback @Etale ⊤ q
  let Ll := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op l))
  let fl (k : K) : F.obj (B k) ⟶ F.obj A :=
    MorphismProperty.Over.homMk
      (pullback.lift (ψl k) (pullback.snd (B k).hom q) (by
        rw [hψl k, pullback.condition])) (by
        change pullback.lift _ _ _ ≫ pullback.snd A.hom q = pullback.snd (B k).hom q
        exact pullback.lift_snd _ _ _)
  have hS (Z : (D.obj (op j)).Etale) :
      IsPullback (pullback.fst Z.hom (c.π.app (op j)))
        (L.obj Z).hom Z.hom (c.π.app (op j)) := IsPullback.of_hasPullback _ _
  have hT (Z : (D.obj (op j)).Etale) :
      IsPullback (pullback.fst (F.obj Z).hom (c.π.app (op l)))
        (Ll.obj (F.obj Z)).hom (F.obj Z).hom (c.π.app (op l)) :=
    IsPullback.of_hasPullback _ _
  have hcomp : c.π.app (op l) ≫ q = c.π.app (op j) := c.w (homOfLE hjl).op
  have hU (Z : (D.obj (op j)).Etale) :
      IsPullback (pullback.fst (F.obj Z).hom (c.π.app (op l)) ≫ pullback.fst Z.hom q)
        (Ll.obj (F.obj Z)).hom Z.hom (c.π.app (op j)) := by
    have H := (hT Z).paste_horiz (IsPullback.of_hasPullback Z.hom q)
    simpa only [hcomp] using H
  let t (Z : (D.obj (op j)).Etale) : Ll.obj (F.obj Z) ≅ L.obj Z :=
    MorphismProperty.Over.isoMk ((hU Z).isoPullback ≪≫ (hS Z).isoPullback.symm) (by
      simp)
  have ht (Z : (D.obj (op j)).Etale) :
      (t Z).hom.left ≫ pullback.fst Z.hom (c.π.app (op j)) =
        pullback.fst (F.obj Z).hom (c.π.app (op l)) ≫ pullback.fst Z.hom q := by
    dsimp [t]
    simp
  have heq (k : K) : Ll.map (fl k) ≫ (t A).hom = (t (B k)).hom ≫ g k := by
    apply MorphismProperty.Over.Hom.ext
    apply (hS A).hom_ext
    · change ((Ll.map (fl k)).left ≫ (t A).hom.left) ≫
          pullback.fst A.hom (c.π.app (op j)) =
        ((t (B k)).hom.left ≫ (g k).left) ≫ pullback.fst A.hom (c.π.app (op j))
      rw [Category.assoc, ht]
      have hnat : (Ll.map (fl k)).left ≫
          pullback.fst (F.obj A).hom (c.π.app (op l)) =
        pullback.fst (F.obj (B k)).hom (c.π.app (op l)) ≫ (fl k).left := by
          simp [Ll, MorphismProperty.Over.pullback]
      rw [← Category.assoc, hnat, Category.assoc]
      change pullback.fst (F.obj (B k)).hom (c.π.app (op l)) ≫
          (pullback.lift (ψl k) (pullback.snd (B k).hom q) _ ≫ pullback.fst A.hom q) = _
      rw [pullback.lift_fst]
      have hm : (hU (B k)).isoPullback.hom ≫
          pullback.map (B k).hom (c.π.app (op j)) (B k).hom q
            (𝟙 _) (c.π.app (op l)) (𝟙 _) (by simp) (by simpa using hcomp.symm) =
          pullback.fst (F.obj (B k)).hom (c.π.app (op l)) := by
        apply pullback.hom_ext
        · simp [IsPullback.isoPullback_hom_fst]
        · simp only [Category.assoc, pullback.lift_snd,
            IsPullback.isoPullback_hom_snd_assoc]
          exact (hT (B k)).w.symm
      rw [← hm, Category.assoc]
      change (hU (B k)).isoPullback.hom ≫
          pullback.map (B k).hom (c.π.app (op j)) (B k).hom
            (D.map (homOfLE hjl).op) (𝟙 (B k).left) (c.π.app (op l))
            (𝟙 (D.obj (op j))) (by simp) (by simp) ≫ ψl k = _
      rw [hdesc k]
      have hi : (hS (B k)).isoPullback.inv = 𝟙 _ := by
        apply pullback.hom_ext
        · simpa only [Category.id_comp] using (hS (B k)).isoPullback_inv_fst
        · have hs := (hS (B k)).isoPullback_inv_snd
          change (hS (B k)).isoPullback.inv ≫
            pullback.snd (B k).hom (c.π.app (op j)) =
              pullback.snd (B k).hom (c.π.app (op j)) at hs
          simpa only [Category.id_comp] using hs
      dsimp [t, ψ]
      simp only [MorphismProperty.Over.isoMk_hom_left, Iso.trans_hom, Iso.symm_hom,
        hi, Category.comp_id, Category.assoc]
    · change ((Ll.map (fl k)).left ≫ (t A).hom.left) ≫ (L.obj A).hom =
        ((t (B k)).hom.left ≫ (g k).left) ≫ (L.obj A).hom
      simp only [Category.assoc, MorphismProperty.Over.w]
  refine ⟨l, F.obj A, (fun k ↦ F.obj (B k)), fl,
    t A ≪≫ e none, (fun k ↦ t (B k) ≪≫ e (some k)), ?_, ?_, ?_⟩
  · exact ⟨@QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.fst A.hom q)
      inferInstance (hYc none), @quasiSeparatedSpace_of_quasiSeparated _ _
      (pullback.fst A.hom q) (hYs none) inferInstance⟩
  · intro k
    exact ⟨@QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.fst (B k).hom q)
      inferInstance (hYc (some k)), @quasiSeparatedSpace_of_quasiSeparated _ _
      (pullback.fst (B k).hom q) (hYs (some k)) inferInstance⟩
  · intro k
    change Ll.map (fl k) ≫ (t A).hom ≫ (e none).hom =
      (t (B k)).hom ≫ (e (some k)).hom ≫ f k
    rw [← Category.assoc, heq k]
    simp [g, Category.assoc]


end AlgebraicGeometry.Etale
