/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.Data.Fintype.Order
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.FiniteDiagramLiftOfModels
import WeilConjectures.AlgebraicGeometry.FiniteFamilyJointSurjectivityStage

/-!
# Blueprint statements

lemma-acyclicity-pulled-back-injectives.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem pullbackComp_inv_fst {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (W : Over Z) :
    ((Over.pullbackComp f g).inv.app W).left ≫ pullback.fst W.hom (f ≫ g) =
      pullback.fst (pullback.snd W.hom g) f ≫ pullback.fst W.hom g := by
  simp [Over.pullbackComp, Adjunction.comp_counit_app]

private theorem comparison_fst {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) (W : Over Z) :
    ((((Over.pullbackComp f g).symm ≪≫
      eqToIso (congrArg (fun t : X ⟶ Z ↦ Over.pullback t) h)).app W).hom).left ≫
        pullback.fst W.hom k =
      pullback.fst (pullback.snd W.hom g) f ≫ pullback.fst W.hom g := by
  subst k
  simpa using pullbackComp_inv_fst f g W

/-- Blueprint: lemma-acyclicity-pulled-back-injectives. -/
theorem etale_finite_data_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    (∀ U : Over c.pt,
      (Etale U.hom ∧ LocallyOfFinitePresentation U.hom ∧
        QuasiCompact U.hom ∧ QuasiSeparated U.hom) →
      ∃ (i : Iᵒᵖ) (Ui : Over (D.obj i)),
        (Etale Ui.hom ∧ LocallyOfFinitePresentation Ui.hom ∧
          QuasiCompact Ui.hom ∧ QuasiSeparated Ui.hom) ∧
        Nonempty ((Over.pullback (c.π.app i)).obj Ui ≅ U)) ∧
    (∀ (i : Iᵒᵖ) (U V : Over (D.obj i)),
      (Etale U.hom ∧ LocallyOfFinitePresentation U.hom ∧
        QuasiCompact U.hom ∧ QuasiSeparated U.hom) →
      (Etale V.hom ∧ LocallyOfFinitePresentation V.hom ∧
        QuasiCompact V.hom ∧ QuasiSeparated V.hom) →
      ∀ ψ : (Over.pullback (c.π.app i)).obj U ⟶ (Over.pullback (c.π.app i)).obj V,
        ∃ (j : Iᵒᵖ) (h : j ⟶ i)
          (ψj : (Over.pullback (D.map h)).obj U ⟶ (Over.pullback (D.map h)).obj V),
          (Over.pullback (c.π.app j)).map ψj ≫
              (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
                eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))).app
                  V).hom =
            (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
                eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))).app
                  U).hom ≫ ψ) ∧
    (∀ (i : Iᵒᵖ) (U V : Over (D.obj i)),
      (Etale U.hom ∧ LocallyOfFinitePresentation U.hom ∧
        QuasiCompact U.hom ∧ QuasiSeparated U.hom) →
      (Etale V.hom ∧ LocallyOfFinitePresentation V.hom ∧
        QuasiCompact V.hom ∧ QuasiSeparated V.hom) →
      ∀ ψ χ : U ⟶ V, (Over.pullback (c.π.app i)).map ψ = (Over.pullback (c.π.app i)).map χ →
        ∃ (j : Iᵒᵖ) (h : j ⟶ i),
          (Over.pullback (D.map h)).map ψ = (Over.pullback (D.map h)).map χ) ∧
    (∀ (A : Type v) [Finite A] [Quiver.{v} A]
      [Finite (Σ a b : A, Quiver.Hom a b)]
      (R : Type v) [Finite R] (s t : R → Paths A)
      (p q : ∀ r, s r ⟶ t r) (F : Paths A ⥤ Over c.pt),
      (∀ a, Etale (F.obj a).hom ∧ LocallyOfFinitePresentation (F.obj a).hom ∧
        QuasiCompact (F.obj a).hom ∧ QuasiSeparated (F.obj a).hom) →
      (∀ r, F.map (p r) = F.map (q r)) →
        ∃ (i : Iᵒᵖ) (G : Paths A ⥤ Over (D.obj i)) (α : G ⋙ Over.pullback (c.π.app i) ≅ F),
          (∀ a, Etale (G.obj a).hom ∧ LocallyOfFinitePresentation (G.obj a).hom ∧
            QuasiCompact (G.obj a).hom ∧ QuasiSeparated (G.obj a).hom) ∧
          (∀ r, G.map (p r) = G.map (q r)) ∧
          ∀ (j : Iᵒᵖ) (h : j ⟶ i),
            (∀ a, Etale ((G ⋙ Over.pullback (D.map h)).obj a).hom ∧
              LocallyOfFinitePresentation ((G ⋙ Over.pullback (D.map h)).obj a).hom ∧
              QuasiCompact ((G ⋙ Over.pullback (D.map h)).obj a).hom ∧
              QuasiSeparated ((G ⋙ Over.pullback (D.map h)).obj a).hom) ∧
            (∀ r, (G ⋙ Over.pullback (D.map h)).map (p r) =
              (G ⋙ Over.pullback (D.map h)).map (q r)) ∧
            ∀ (a b : Paths A) (f : a ⟶ b),
              ((G ⋙ Over.pullback (D.map h)) ⋙ Over.pullback (c.π.app j)).map f ≫
                  (Functor.isoWhiskerLeft G ((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
                    eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))) ≪≫
                      α).hom.app b =
                (Functor.isoWhiskerLeft G ((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
                    eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))) ≪≫
                      α).hom.app a ≫ F.map f) ∧
    (∀ (A : Type v) [Finite A] [Quiver.{v} A]
      [Finite (Σ a b : A, Quiver.Hom a b)]
      (i : Iᵒᵖ) (G : Paths A ⥤ Over (D.obj i)) (F : Paths A ⥤ Over c.pt)
      (_α : G ⋙ Over.pullback (c.π.app i) ≅ F),
      (∀ a, Etale (G.obj a).hom ∧ LocallyOfFinitePresentation (G.obj a).hom ∧
        QuasiCompact (G.obj a).hom ∧ QuasiSeparated (G.obj a).hom) →
      ∀ (b : A) (B : Finset (Σ a : A, Quiver.Hom a b)),
        (∀ x : (F.obj b).left, ∃ e ∈ B, ∃ y : (F.obj e.1).left,
          (F.map ((Paths.of A).map e.2)).left y = x) →
        ∃ (i₁ : Iᵒᵖ) (h₁ : i₁ ⟶ i), ∀ (j : Iᵒᵖ) (h : j ⟶ i₁),
          (∀ e ∈ B,
            Etale (((G ⋙ Over.pullback (D.map (h ≫ h₁))).map ((Paths.of A).map e.2)).left)) ∧
          (∀ x : ((G ⋙ Over.pullback (D.map (h ≫ h₁))).obj b).left,
            ∃ e ∈ B, ∃ y : ((G ⋙ Over.pullback (D.map (h ≫ h₁))).obj e.1).left,
              ((G ⋙ Over.pullback (D.map (h ≫ h₁))).map ((Paths.of A).map e.2)).left y = x)) := by
  classical
  have objects : ∀ U : Over c.pt,
      (Etale U.hom ∧ LocallyOfFinitePresentation U.hom ∧
        QuasiCompact U.hom ∧ QuasiSeparated U.hom) →
      ∃ (i : Iᵒᵖ) (Ui : Over (D.obj i)),
        (Etale Ui.hom ∧ LocallyOfFinitePresentation Ui.hom ∧
          QuasiCompact Ui.hom ∧ QuasiSeparated Ui.hom) ∧
        Nonempty ((Over.pullback (c.π.app i)).obj Ui ≅ U) := by
    intro U hU
    obtain ⟨hUe, hUp, hUc, hUs⟩ := hU
    obtain ⟨i, Y, p, hp, hpc, hps, f, hf⟩ :=
      Scheme.exists_isPullback_of_finitePresentation hc U.hom
    let V : Over (D.obj i) := Over.mk p
    let e : (Over.pullback (c.π.app i)).obj V ≅ U :=
      Over.isoMk hf.isoPullback.symm (by simp [V])
    have : Etale ((Over.pullback (c.π.app i)).obj V).hom := by
      rw [← Over.w e.hom]
      infer_instance
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
    have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
    let T : Over (D.obj i) := Over.mk (𝟙 _)
    have : IsIso T.hom := by dsimp [T]; infer_instance
    have : CompactSpace V.left := by dsimp [V]; infer_instance
    have : QuasiSeparatedSpace V.left := by dsimp [V]; infer_instance
    have : CompactSpace T.left := by dsimp [T]; infer_instance
    have : QuasiSeparatedSpace T.left := by dsimp [T]; infer_instance
    let g : V ⟶ T := Over.homMk p (by simp [V, T])
    have : LocallyOfFinitePresentation g.left := hp
    have : Etale ((Over.pullback (c.π.app i)).obj T).hom := by
      dsimp [T]; infer_instance
    have hg : Etale (((Over.pullback (c.π.app i)).map g).left) := by
      have : Etale (((Over.pullback (c.π.app i)).map g).left ≫
          ((Over.pullback (c.π.app i)).obj T).hom) := by
        rw [Over.w]; infer_instance
      exact Etale.of_comp (((Over.pullback (c.π.app i)).map g).left)
        ((Over.pullback (c.π.app i)).obj T).hom
    obtain ⟨j, h, hj⟩ := Etale.exists_stage_of_inverseLimit D c hc i.unop V T g hg
    let a : op j ⟶ i := (homOfLE h).op
    let W := (Over.pullback (D.map a)).obj V
    have hWe : Etale W.hom := by
      have : Etale (((Over.pullback (D.map a)).map g).left) := hj
      have hw : W.hom = ((Over.pullback (D.map a)).map g).left ≫
          ((Over.pullback (D.map a)).obj T).hom := (Over.w _).symm
      have : Etale ((Over.pullback (D.map a)).obj T).hom := by
        dsimp [T]; infer_instance
      rw [hw]
      infer_instance
    refine ⟨op j, W, ⟨hWe, ?_, ?_, ?_⟩, ?_⟩
    · dsimp [W, V]; infer_instance
    · dsimp [W, V]; infer_instance
    · dsimp [W, V]; infer_instance
    · exact ⟨(((Over.pullbackComp (c.π.app (op j)) (D.map a)).symm ≪≫
        eqToIso (congrArg (fun f ↦ Over.pullback f) (c.w a))).app V) ≪≫ e⟩
  refine ⟨objects, ?_, ?_, ?_, ?_⟩
  · intro i U V hU hV ψ
    obtain ⟨hUe, hUp, hUc, hUs⟩ := hU
    obtain ⟨hVe, hVp, hVc, hVs⟩ := hV
    let θ := ψ.left ≫ pullback.fst V.hom (c.π.app i)
    have hθ : θ ≫ V.hom = pullback.fst U.hom (c.π.app i) ≫ U.hom := by
      dsimp [θ]
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      change (ψ.left ≫ ((Over.pullback (c.π.app i)).obj V).hom) ≫ c.π.app i = _
      rw [Over.w, pullback.condition]
      rfl
    obtain ⟨j, h, θj, hθj, hj⟩ := Scheme.exists_pullback_hom_of_isLimit hc
      U.hom V.hom θ hθ
    let ψj : (Over.pullback (D.map h)).obj U ⟶ (Over.pullback (D.map h)).obj V :=
      Over.homMk (pullback.lift θj (pullback.snd U.hom (D.map h))
        (hθj.trans pullback.condition)) (by simp)
    let K := (Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
      eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))
    have hK (W : Over (D.obj i)) :
        (K.hom.app W).left ≫ pullback.fst W.hom (c.π.app i) =
          pullback.fst (pullback.snd W.hom (D.map h)) (c.π.app j) ≫
            pullback.fst W.hom (D.map h) :=
      comparison_fst _ _ _ (c.w h) W
    have hM : (K.hom.app U).left ≫
        pullback.map U.hom (c.π.app i) U.hom (D.map h)
          (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) =
        pullback.fst (pullback.snd U.hom (D.map h)) (c.π.app j) := by
      apply pullback.hom_ext
      · simpa using hK U
      · simp only [Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id]
        change (K.hom.app U).left ≫ ((Over.pullback (c.π.app i)).obj U).hom ≫
          c.π.app j = _
        rw [← Category.assoc, Over.w]
        exact pullback.condition.symm
    refine ⟨j, h, ψj, ?_⟩
    ext1
    apply pullback.hom_ext
    · change (((Over.pullback (c.π.app j)).map ψj).left ≫
          (K.hom.app V).left) ≫ pullback.fst V.hom (c.π.app i) =
        ((K.hom.app U).left ≫ ψ.left) ≫ pullback.fst V.hom (c.π.app i)
      rw [Category.assoc, hK V]
      have hmapp : ((Over.pullback (c.π.app j)).map ψj).left ≫
          pullback.fst (pullback.snd V.hom (D.map h)) (c.π.app j) =
          pullback.fst (pullback.snd U.hom (D.map h)) (c.π.app j) ≫ ψj.left := by
        simp
      rw [← Category.assoc, hmapp, Category.assoc]
      change pullback.fst _ _ ≫ ψj.left ≫ pullback.fst V.hom (D.map h) =
        (K.hom.app U).left ≫ θ
      simp only [ψj, Over.homMk_left, pullback.lift_fst]
      rw [← hj, ← Category.assoc, hM]
      rfl
    · change (((Over.pullback (c.π.app j)).map ψj).left ≫
          (K.hom.app V).left) ≫ ((Over.pullback (c.π.app i)).obj V).hom =
        ((K.hom.app U).left ≫ ψ.left) ≫ ((Over.pullback (c.π.app i)).obj V).hom
      exact (Over.w (((Over.pullback (c.π.app j)).map ψj) ≫ K.hom.app V)).trans
        (Over.w (K.hom.app U ≫ ψ)).symm
  · intro i U V hU hV ψ χ heq
    obtain ⟨hUe, hUp, hUc, hUs⟩ := hU
    obtain ⟨hVe, hVp, hVc, hVs⟩ := hV
    have heq' : pullback.fst U.hom (c.π.app i) ≫ ψ.left =
        pullback.fst U.hom (c.π.app i) ≫ χ.left := by
      have H := congrArg (fun f ↦ f.left ≫ pullback.fst V.hom (c.π.app i)) heq
      simpa using H
    obtain ⟨j, h, hj⟩ := Scheme.exists_pullback_fst_comp_eq_of_isLimit hc
      U.hom V.hom ψ.left χ.left (Over.w ψ) (Over.w χ) heq'
    refine ⟨j, h, ?_⟩
    ext1
    apply pullback.hom_ext
    · simpa using hj
    · simp
  · intro A _ _ _ R _ s t p q F hF hR
    choose ia Va hVa ea using fun a : A ↦ objects (F.obj a) (hF a)
    obtain ⟨i, hi⟩ := Finite.exists_le (fun a ↦ (ia a).unop)
    let ha (a : A) : op i ⟶ ia a := (homOfLE (hi a)).op
    let V (a : A) : Over (D.obj (op i)) := (Over.pullback (D.map (ha a))).obj (Va a)
    have hV (a : A) : Etale (V a).hom ∧ LocallyOfFinitePresentation (V a).hom ∧
        QuasiCompact (V a).hom ∧ QuasiSeparated (V a).hom := by
      obtain ⟨he, hp, hq, hs⟩ := hVa a
      dsimp [V]
      exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
    let e (a : A) : (Over.pullback (c.π.app (op i))).obj (V a) ≅ F.obj a :=
      (((Over.pullbackComp (c.π.app (op i)) (D.map (ha a))).symm ≪≫
        eqToIso (congrArg (fun f ↦ Over.pullback f) (c.w (ha a)))).app (Va a)) ≪≫
          (ea a).some
    obtain ⟨j, h, G, ⟨α⟩, hG, hGR⟩ := finite_diagram_lift_of_models D c hc A R s t p q F
      (op i) V (fun a ↦ (hV a).2) e hR
    have hGp (a : A) : Etale (G.obj a).hom ∧ LocallyOfFinitePresentation (G.obj a).hom ∧
        QuasiCompact (G.obj a).hom ∧ QuasiSeparated (G.obj a).hom := by
      rw [hG a]
      obtain ⟨he, hp, hq, hs⟩ := hV a
      dsimp
      exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
    refine ⟨j, G, α, hGp, hGR, ?_⟩
    intro k hk
    refine ⟨?_, ?_, ?_⟩
    · intro a
      obtain ⟨he, hp, hq, hs⟩ := hGp a
      dsimp
      exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
    · intro r
      exact congrArg (fun f ↦ (Over.pullback (D.map hk)).map f) (hGR r)
    · intro a b f
      exact (Functor.isoWhiskerLeft G
        ((Over.pullbackComp (c.π.app k) (D.map hk)).symm ≪≫
          eqToIso (congrArg (fun f ↦ Over.pullback f) (c.w hk))) ≪≫ α).hom.naturality f
  · intro A _ _ _ i G F α hG b B hB
    let U (e : B) : Over (D.obj i) := G.obj e.val.1
    let V : Over (D.obj i) := G.obj b
    let f (e : B) : U e ⟶ V := G.map ((Paths.of A).map e.val.2)
    have hU (e : B) : LocallyOfFinitePresentation (U e).hom ∧
        QuasiCompact (U e).hom ∧ QuasiSeparated (U e).hom := (hG e.val.1).2
    have hV : LocallyOfFinitePresentation V.hom ∧ QuasiCompact V.hom ∧
        QuasiSeparated V.hom := (hG b).2
    have hf (e : B) : LocallyOfFinitePresentation (f e).left := by
      have := (hG e.val.1).1
      have := (hG b).1
      have : Etale ((f e).left ≫ V.hom) := by rw [Over.w]; exact (hG e.val.1).1
      have : Etale (f e).left := Etale.of_comp (f e).left V.hom
      infer_instance
    have hcov : ∀ x : ((Over.pullback (c.π.app i)).obj V).left,
        ∃ e : B, ∃ y : ((Over.pullback (c.π.app i)).obj (U e)).left,
          ((Over.pullback (c.π.app i)).map (f e)).left y = x := by
      intro x
      obtain ⟨e, he, y, hy⟩ := hB ((α.hom.app b).left x)
      refine ⟨⟨e, he⟩, (α.inv.app e.1).left y, ?_⟩
      have hn := α.inv.naturality ((Paths.of A).map e.2)
      have hp := congrArg (fun k ↦ k.left y) hn
      dsimp [f, U, V]
      change (α.inv.app b).left ((F.map ((Paths.of A).map e.2)).left y) =
        ((Over.pullback (c.π.app i)).map (G.map ((Paths.of A).map e.2))).left
          ((α.inv.app e.1).left y) at hp
      rw [hy] at hp
      have hx := congrArg (fun k ↦ k.left x) (α.hom_inv_id_app b)
      exact hp.symm.trans hx
    obtain ⟨i₁, h₁, hstage⟩ := finite_family_joint_surjectivity_stage D c hc B i U V f
      hU hV hf hcov
    refine ⟨i₁, h₁, ?_⟩
    intro j h
    refine ⟨?_, ?_⟩
    · intro e he
      let T := G ⋙ Over.pullback (D.map (h ≫ h₁))
      have hsource : Etale (T.obj ((Paths.of A).obj e.1)).hom := by
        have := (hG ((Paths.of A).obj e.1)).1
        dsimp [T]
        infer_instance
      have htarget : Etale (T.obj ((Paths.of A).obj b)).hom := by
        have := (hG ((Paths.of A).obj b)).1
        dsimp [T]
        infer_instance
      have : Etale ((T.map ((Paths.of A).map e.2)).left ≫
          (T.obj ((Paths.of A).obj b)).hom) := by
        rw [Over.w]
        exact hsource
      exact Etale.of_comp _ (T.obj ((Paths.of A).obj b)).hom
    · intro x
      obtain ⟨e, y, hy⟩ := hstage j h x
      exact ⟨e.val, e.property, y, hy⟩

end AlgebraicGeometry
