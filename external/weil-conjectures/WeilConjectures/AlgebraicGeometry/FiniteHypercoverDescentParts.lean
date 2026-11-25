/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
import all WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentStages

/-!
# Blueprint statements

lemma-weil-pbc-finite-hypercover-descent-objects, lemma-weil-pbc-finite-hypercover-descent-
morphisms, lemma-weil-pbc-finite-hypercover-descent-equalities.
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Blueprint: lemma-weil-pbc-finite-hypercover-descent-objects. -/
theorem finite_hypercover_descent_objects
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    ∀ (r : ℕ) (U : TruncatedFiniteSplitEtaleHypercover c.pt r),
      ∃ (i : Iᵒᵖ) (Ui : TruncatedFiniteSplitEtaleHypercover (D.obj i) r),
        Ui.IsBaseChange (c.π.app i) U ∧
          ∀ (j : Iᵒᵖ) (h : j ⟶ i) (n : Fin (r + 1)),
            Surjective ((Over.pullback (D.map h)).map
              ((Scheme.Etale.forget (D.obj i)).map (Ui.matchingMap n))).left := by
  intro r U
  exact finite_hypercover_descent_of_diagram_models D c hc r U
    (split_diagram_model D c hc r U)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Blueprint: lemma-weil-pbc-finite-hypercover-descent-morphisms. -/
theorem finite_hypercover_descent_morphisms
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    ∀ (r : ℕ) (i : Iᵒᵖ)
      (U V : TruncatedFiniteSplitEtaleHypercover (D.obj i) r)
      (φ : U.diagram ⋙ Over.pullback (c.π.app i) ⟶
        V.diagram ⋙ Over.pullback (c.π.app i)),
      ∃ (j : Iᵒᵖ) (h : j ⟶ i)
        (ψ : U.diagram ⋙ Over.pullback (D.map h) ⟶
          V.diagram ⋙ Over.pullback (D.map h)),
        ∀ Δ : (SimplexCategory.Truncated r)ᵒᵖ,
          (Over.pullback (c.π.app j)).map (ψ.app Δ) ≫
              (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
                eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f)
                  (c.w h))).app (V.diagram.obj Δ)).hom =
            (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
              eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f)
                (c.w h))).app (U.diagram.obj Δ)).hom ≫ φ.app Δ := by
  classical
  intro r i U V φ
  have := truncated_finite r
  have : Finite (SimplexCategory.Truncated r)ᵒᵖ :=
    Finite.of_injective Opposite.unop Opposite.unop_injective
  let C := (SimplexCategory.Truncated r)ᵒᵖ
  obtain ⟨j, h, ψj, hj⟩ := finite_components_lift D c hc C i
    U.diagram.obj V.diagram.obj (truncated_terms_finitePresentation U)
    (truncated_terms_finitePresentation V) φ.app
  let F := U.diagram ⋙ Over.pullback (D.map h)
  let G := V.diagram ⋙ Over.pullback (D.map h)
  let K := (Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
    eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))
  let R := Σ a b : C, a ⟶ b
  have : ∀ a b : C, Finite (a ⟶ b) := by
    intro a b
    apply Finite.of_injective (fun f : a ⟶ b ↦ f.unop.hom)
    intro f g hfg
    apply Quiver.Hom.unop_inj
    exact SimplexCategory.Truncated.Hom.ext _ _
      (congrArg SimplexCategory.Hom.toOrderHom hfg)
  have : Finite R := inferInstance
  change ∀ a, (Over.pullback (c.π.app j)).map (ψj a) ≫ K.hom.app (V.diagram.obj a) =
    K.hom.app (U.diagram.obj a) ≫ φ.app a at hj
  have hF (a : C) : LocallyOfFinitePresentation (F.obj a).hom ∧
      QuasiCompact (F.obj a).hom ∧ QuasiSeparated (F.obj a).hom := by
    obtain ⟨hp, hq, hs⟩ := truncated_terms_finitePresentation U a
    dsimp [F]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hG (a : C) : LocallyOfFinitePresentation (G.obj a).hom ∧
      QuasiCompact (G.obj a).hom ∧ QuasiSeparated (G.obj a).hom := by
    obtain ⟨hp, hq, hs⟩ := truncated_terms_finitePresentation V a
    dsimp [G]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hn (a b : C) (f : a ⟶ b) :
      (Over.pullback (c.π.app j)).map (F.map f ≫ ψj b) =
        (Over.pullback (c.π.app j)).map (ψj a ≫ G.map f) := by
    apply (cancel_mono (K.hom.app (V.diagram.obj b))).mp
    simp only [Functor.map_comp, Category.assoc]
    rw [hj b]
    have hKU := K.hom.naturality (U.diagram.map f)
    have hKV := K.hom.naturality (V.diagram.map f)
    simp only [Functor.comp_map] at hKU hKV
    change (Over.pullback (c.π.app j)).map ((Over.pullback (D.map h)).map
      (U.diagram.map f)) ≫ K.hom.app (U.diagram.obj b) ≫ φ.app b = _
    rw [← Category.assoc, hKU, Category.assoc]
    have hφ := φ.naturality f
    simp only [Functor.comp_map] at hφ
    rw [hφ]
    rw [← Category.assoc, ← Category.assoc, ← hj a]
    exact congrArg ((Over.pullback (c.π.app j)).map (ψj a) ≫ ·) hKV.symm
  obtain ⟨k, l, hl⟩ := finite_morphism_equalities_lift D c hc R j
    (fun f ↦ F.obj f.1) (fun f ↦ G.obj f.2.1)
    (fun f ↦ hF f.1) (fun f ↦ hG f.2.1)
    (fun f ↦ F.map f.2.2 ≫ ψj f.2.1)
    (fun f ↦ ψj f.1 ≫ G.map f.2.2) (fun f ↦ hn f.1 f.2.1 f.2.2)
  let χ : F ⋙ Over.pullback (D.map l) ⟶ G ⋙ Over.pullback (D.map l) :=
    { app := fun a ↦ (Over.pullback (D.map l)).map (ψj a)
      naturality := fun {a b} f ↦ by
        simpa only [Functor.comp_map, ← Functor.map_comp] using hl ⟨a, b, f⟩ }
  let T : Over.pullback (D.map (l ≫ h)) ≅
      Over.pullback (D.map h) ⋙ Over.pullback (D.map l) :=
    eqToIso (congrArg (fun f ↦ Over.pullback f) (D.map_comp l h)) ≪≫
      Over.pullbackComp (D.map l) (D.map h)
  let ψ : U.diagram ⋙ Over.pullback (D.map (l ≫ h)) ⟶
      V.diagram ⋙ Over.pullback (D.map (l ≫ h)) :=
    (Functor.isoWhiskerLeft U.diagram T).hom ≫ χ ≫
      (Functor.isoWhiskerLeft V.diagram T).inv
  let L := (Over.pullbackComp (c.π.app k) (D.map l)).symm ≪≫
    eqToIso (congrArg (fun f : c.pt ⟶ D.obj j ↦ Over.pullback f) (c.w l))
  let M := (Over.pullbackComp (c.π.app k) (D.map (l ≫ h))).symm ≪≫
    eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w (l ≫ h)))
  have hT (W : Over (D.obj i)) :
      (T.hom.app W).left ≫ pullback.fst (pullback.snd W.hom (D.map h)) (D.map l) ≫
          pullback.fst W.hom (D.map h) = pullback.fst W.hom (D.map (l ≫ h)) := by
    have hInv : (T.inv.app W).left ≫ pullback.fst W.hom (D.map (l ≫ h)) =
        pullback.fst (pullback.snd W.hom (D.map h)) (D.map l) ≫
          pullback.fst W.hom (D.map h) := by
      simpa [T] using comparison_fst (D.map l) (D.map h) (D.map (l ≫ h))
        (D.map_comp l h).symm W
    rw [← hInv, ← Category.assoc, ← Over.comp_left, T.hom_inv_id_app]
    simp
  have coherence (W : Over (D.obj i)) :
      (Over.pullback (c.π.app k)).map (T.hom.app W) ≫
          L.hom.app ((Over.pullback (D.map h)).obj W) ≫ K.hom.app W = M.hom.app W := by
    ext1
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      have hK := comparison_fst _ _ _ (c.w h) W
      have hL := comparison_fst _ _ _ (c.w l) ((Over.pullback (D.map h)).obj W)
      have hM := comparison_fst _ _ _ (c.w (l ≫ h)) W
      change ((Over.pullback (c.π.app k)).map (T.hom.app W)).left ≫
        (L.hom.app ((Over.pullback (D.map h)).obj W)).left ≫
        (K.hom.app W).left ≫ pullback.fst W.hom (c.π.app i) = _
      change (K.hom.app W).left ≫ pullback.fst W.hom (c.π.app i) = _ at hK
      change (L.hom.app ((Over.pullback (D.map h)).obj W)).left ≫
        pullback.fst (pullback.snd W.hom (D.map h)) (c.π.app j) = _ at hL
      change (M.hom.app W).left ≫ pullback.fst W.hom (c.π.app i) = _ at hM
      rw [hK, ← Category.assoc (L.hom.app _).left, hL]
      simp only [Category.assoc]
      have hmapp : ((Over.pullback (c.π.app k)).map (T.hom.app W)).left ≫
          pullback.fst ((Over.pullback (D.map l)).obj
            ((Over.pullback (D.map h)).obj W)).hom (c.π.app k) =
        pullback.fst ((Over.pullback (D.map (l ≫ h))).obj W).hom (c.π.app k) ≫
          (T.hom.app W).left := by
        simp
      simp only [Over.pullback_obj_hom] at hmapp ⊢
      rw [← Category.assoc ((Over.pullback (c.π.app k)).map (T.hom.app W)).left,
        hmapp]
      simpa only [Category.assoc, hT] using hM.symm
    · exact (Over.w _).trans (Over.w _).symm
  refine ⟨k, l ≫ h, ψ, ?_⟩
  intro Δ
  change (Over.pullback (c.π.app k)).map (ψ.app Δ) ≫ M.hom.app (V.diagram.obj Δ) =
    M.hom.app (U.diagram.obj Δ) ≫ φ.app Δ
  rw [← coherence (V.diagram.obj Δ), ← coherence (U.diagram.obj Δ)]
  simp only [ψ, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [← Category.assoc
    ((Over.pullback (c.π.app k)).map (T.inv.app (V.diagram.obj Δ)))
    ((Over.pullback (c.π.app k)).map (T.hom.app (V.diagram.obj Δ))),
    ← Functor.map_comp, T.inv_hom_id_app]
  rw [(Over.pullback (c.π.app k)).map_id]
  simp only [Category.id_comp]
  have heq : (Over.pullback (c.π.app k)).map (χ.app Δ) ≫
      L.hom.app ((Over.pullback (D.map h)).obj (V.diagram.obj Δ)) =
    L.hom.app ((Over.pullback (D.map h)).obj (U.diagram.obj Δ)) ≫
      (Over.pullback (c.π.app j)).map (ψj Δ) := L.hom.naturality (ψj Δ)
  rw [← Category.assoc ((Over.pullback (c.π.app k)).map (χ.app Δ)), heq]
  simp only [Category.assoc]
  rw [hj Δ]

/-- Blueprint: lemma-weil-pbc-finite-hypercover-descent-equalities. -/
theorem finite_hypercover_descent_equalities
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    ∀ (r : ℕ) (i : Iᵒᵖ)
      (U V : TruncatedFiniteSplitEtaleHypercover (D.obj i) r)
      (φ ψ : U.diagram ⟶ V.diagram),
      Functor.whiskerRight φ (Over.pullback (c.π.app i)) =
        Functor.whiskerRight ψ (Over.pullback (c.π.app i)) →
      ∃ (j : Iᵒᵖ) (h : j ⟶ i),
        Functor.whiskerRight φ (Over.pullback (D.map h)) =
          Functor.whiskerRight ψ (Over.pullback (D.map h)) := by
  classical
  intro r i U V φ ψ hφψ
  have := truncated_finite r
  have : Finite (SimplexCategory.Truncated r)ᵒᵖ :=
    Finite.of_injective Opposite.unop Opposite.unop_injective
  obtain ⟨j, h, hj⟩ := finite_morphism_equalities_lift D c hc
    ((SimplexCategory.Truncated r)ᵒᵖ) i U.diagram.obj V.diagram.obj
    (truncated_terms_finitePresentation U) (truncated_terms_finitePresentation V)
    φ.app ψ.app (fun Δ ↦ NatTrans.congr_app hφψ Δ)
  refine ⟨j, h, ?_⟩
  exact NatTrans.ext (funext hj)

end AlgebraicGeometry
