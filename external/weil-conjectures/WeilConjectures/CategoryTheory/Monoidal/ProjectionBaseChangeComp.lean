/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.ProjectionBaseChange
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate

/-!

# Compatibility of projection morphisms with base change: composition and open immersions

This file contains two diagram chases, for abstract functors, on the compatibility
`CategoryTheory.ProjectionBaseChange.PFBaseChange` of projection morphisms with base change.

## Main statements

- `CategoryTheory.ProjectionBaseChange.pfBaseChange_comp`: `PFBaseChange` is stable under
  vertical composition of base change squares.
- `CategoryTheory.ProjectionBaseChange.pfBaseChange_of_projectionComparison`: the projection
  morphisms which are inverse to the projection comparisons of adjunctions `j_! ⊣ j^*` (with `j^*`
  monoidal) are compatible with a base change which is the exchange morphism of a monoidal
  identification `θ`.

-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.ProjectionBaseChange

section Comp

variable {𝒳 𝒵 𝒴 𝒳' 𝒵' 𝒴' : Type*} [Category 𝒳] [Category 𝒵] [Category 𝒴] [Category 𝒳']
  [Category 𝒵'] [Category 𝒴'] [MonoidalCategory 𝒳] [MonoidalCategory 𝒵] [MonoidalCategory 𝒴]
  [MonoidalCategory 𝒳'] [MonoidalCategory 𝒵'] [MonoidalCategory 𝒴']

/-- **`PFBaseChange` is stable under vertical composition**: for `f = j ⋙ p` and `f' = j' ⋙ p'`
(through `c`, `c'`, with inverse images `fs ≅ ps ⋙ js`, `fs' ≅ ps' ⋙ js'`), if the projection
morphisms of `f` and `f'` are the composites of those of `j` and `p` (`hpf`, `hpf'`), the base
change of `f` is the pasting of those of `p` and `j` (`hBC`) and the identification `θf` is the
pasting of `θp` and `θj` (`hθ`), then `PFBaseChange` for the squares of `p` and of `j` implies
`PFBaseChange` for the square of `f`. -/
lemma pfBaseChange_comp {j : 𝒳 ⥤ 𝒵} {js : 𝒵 ⥤ 𝒳} {p : 𝒵 ⥤ 𝒴} {ps : 𝒴 ⥤ 𝒵} {f : 𝒳 ⥤ 𝒴}
    {fs : 𝒴 ⥤ 𝒳} {j' : 𝒳' ⥤ 𝒵'} {js' : 𝒵' ⥤ 𝒳'} {p' : 𝒵' ⥤ 𝒴'} {ps' : 𝒴' ⥤ 𝒵'}
    {f' : 𝒳' ⥤ 𝒴'} {fs' : 𝒴' ⥤ 𝒳'}
    (q : 𝒴 ⥤ 𝒴') [q.Monoidal] (qZ : 𝒵 ⥤ 𝒵') [qZ.Monoidal] (qX : 𝒳 ⥤ 𝒳') [qX.Monoidal]
    (BCp : p ⋙ q ⟶ qZ ⋙ p') (BCj : j ⋙ qZ ⟶ qX ⋙ j') (BCf : f ⋙ q ⟶ qX ⋙ f')
    (θp : q ⋙ ps' ≅ ps ⋙ qZ) (θj : qZ ⋙ js' ≅ js ⋙ qX) (θf : q ⋙ fs' ≅ fs ⋙ qX)
    (pfp : curriedTensorInsertFunctor₁ p ⟶
      curriedTensorPost p ⋙ (Functor.whiskeringLeft 𝒴 𝒵 𝒴).obj ps)
    (pfj : curriedTensorInsertFunctor₁ j ⟶
      curriedTensorPost j ⋙ (Functor.whiskeringLeft 𝒵 𝒳 𝒵).obj js)
    (pff : curriedTensorInsertFunctor₁ f ⟶
      curriedTensorPost f ⋙ (Functor.whiskeringLeft 𝒴 𝒳 𝒴).obj fs)
    (pfp' : curriedTensorInsertFunctor₁ p' ⟶
      curriedTensorPost p' ⋙ (Functor.whiskeringLeft 𝒴' 𝒵' 𝒴').obj ps')
    (pfj' : curriedTensorInsertFunctor₁ j' ⟶
      curriedTensorPost j' ⋙ (Functor.whiskeringLeft 𝒵' 𝒳' 𝒵').obj js')
    (pff' : curriedTensorInsertFunctor₁ f' ⟶
      curriedTensorPost f' ⋙ (Functor.whiskeringLeft 𝒴' 𝒳' 𝒴').obj fs')
    (c : f ≅ j ⋙ p) (c' : f' ≅ j' ⋙ p') (u : fs ≅ ps ⋙ js) (u' : fs' ≅ ps' ⋙ js')
    (hpf : ∀ K B, (pff.app K).app B ≫ c.hom.app (K ⊗ fs.obj B) ≫
        p.map (j.map (K ◁ u.hom.app B)) =
      c.hom.app K ▷ B ≫ (pfp.app (j.obj K)).app B ≫ p.map ((pfj.app K).app (ps.obj B)))
    (hpf' : ∀ K B, (pff'.app K).app B ≫ c'.hom.app (K ⊗ fs'.obj B) ≫
        p'.map (j'.map (K ◁ u'.hom.app B)) =
      c'.hom.app K ▷ B ≫ (pfp'.app (j'.obj K)).app B ≫ p'.map ((pfj'.app K).app (ps'.obj B)))
    (hBC : ∀ M, BCf.app M ≫ c'.hom.app (qX.obj M) =
      q.map (c.hom.app M) ≫ BCp.app (j.obj M) ≫ p'.map (BCj.app M))
    (hθ : ∀ B, θf.inv.app B = qX.map (u.hom.app B) ≫ θj.inv.app (ps.obj B) ≫
      js'.map (θp.inv.app B) ≫ u'.inv.app (q.obj B))
    (hp : PFBaseChange q qZ BCp θp pfp pfp') (hj : PFBaseChange qZ qX BCj θj pfj pfj') :
    PFBaseChange q qX BCf θf pff pff' := by
  intro K B
  rw [← cancel_mono (c'.hom.app (qX.obj K ⊗ fs'.obj (q.obj B)) ≫
    p'.map (j'.map (qX.obj K ◁ u'.hom.app (q.obj B))))]
  -- the right-hand side
  have hR : δ q (f.obj K) B ≫ (BCf.app K ▷ q.obj B) ≫ (pff'.app (qX.obj K)).app (q.obj B) ≫
      c'.hom.app (qX.obj K ⊗ fs'.obj (q.obj B)) ≫
      p'.map (j'.map (qX.obj K ◁ u'.hom.app (q.obj B))) =
      q.map (c.hom.app K ▷ B) ≫ q.map ((pfp.app (j.obj K)).app B) ≫
        BCp.app (j.obj K ⊗ ps.obj B) ≫ p'.map (qZ.map ((pfj.app K).app (ps.obj B)) ≫
          BCj.app (K ⊗ js.obj (ps.obj B)) ≫ j'.map (δ qX K (js.obj (ps.obj B))) ≫
          j'.map (qX.obj K ◁ θj.inv.app (ps.obj B)) ≫
          j'.map (qX.obj K ◁ js'.map (θp.inv.app B))) := by
    have hn := congrArg (fun φ ↦ NatTrans.app φ (q.obj B)) (pfp'.naturality (BCj.app K))
    have hn' := (pfj'.app (qX.obj K)).naturality (θp.inv.app B)
    dsimp at hn hn'
    have hin : δ qZ (j.obj K) (ps.obj B) ≫ (qZ.obj (j.obj K) ◁ θp.inv.app B) ≫
        (BCj.app K ▷ ps'.obj (q.obj B)) ≫ (pfj'.app (qX.obj K)).app (ps'.obj (q.obj B)) =
        qZ.map ((pfj.app K).app (ps.obj B)) ≫ BCj.app (K ⊗ js.obj (ps.obj B)) ≫
          j'.map (δ qX K (js.obj (ps.obj B))) ≫ j'.map (qX.obj K ◁ θj.inv.app (ps.obj B)) ≫
          j'.map (qX.obj K ◁ js'.map (θp.inv.app B)) := by
      erw [whisker_exchange_assoc]
      erw [hn']
      rw [← reassoc_of% (hj K (ps.obj B))]
    rw [hpf', ← comp_whiskerRight_assoc, hBC, comp_whiskerRight, comp_whiskerRight]
    simp only [Category.assoc]
    rw [δ_natural_left_assoc, reassoc_of% hn]
    erw [← reassoc_of% (hp (j.obj K) B)]
    rw [← hin]
    simp only [Functor.map_comp]
  have hθ' : qX.obj K ◁ θf.inv.app B ≫ qX.obj K ◁ u'.hom.app (q.obj B) =
      qX.obj K ◁ qX.map (u.hom.app B) ≫
        qX.obj K ◁ (θj.inv.app (ps.obj B) ≫ js'.map (θp.inv.app B)) := by
    rw [hθ]
    simp
  have hBCj := BCj.naturality (K ◁ u.hom.app B)
  have hBCp := BCp.naturality (j.map (K ◁ u.hom.app B))
  have hBCp' := BCp.naturality ((pfj.app K).app (ps.obj B))
  have hc₁ := c'.hom.naturality (qX.obj K ◁ θf.inv.app B)
  have hc₂ := c'.hom.naturality (δ qX K (fs.obj B))
  dsimp at hBCj hBCp hBCp' hc₁ hc₂
  simp only [Category.assoc]
  rw [hR, reassoc_of% hc₁, reassoc_of% hc₂, reassoc_of% (hBC _)]
  rw [← p'.map_comp, ← p'.map_comp, ← j'.map_comp, ← j'.map_comp, hθ']
  rw [δ_natural_right_assoc, j'.map_comp, p'.map_comp, ← p'.map_comp_assoc (BCj.app _), ← hBCj,
    p'.map_comp_assoc, ← reassoc_of% hBCp, ← q.map_comp_assoc, ← q.map_comp_assoc,
    Category.assoc, hpf]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hBCp']
  simp

end Comp

section ProjectionComparison

variable {𝒱 𝒲 𝒴 𝒵 : Type*} [Category 𝒱] [Category 𝒲] [Category 𝒴] [Category 𝒵]
  [MonoidalCategory 𝒱] [MonoidalCategory 𝒲] [MonoidalCategory 𝒴] [MonoidalCategory 𝒵]

/-- A natural isomorphism `θ : q ⋙ Gs ≅ gs ⋙ qZ` of monoidal functors compatible with the
comultiplications has an inverse compatible with the multiplications, in the form used for the
transposition of projection comparisons. -/
lemma whiskerLeft_hom_μ_inv_of_δ {Gs : 𝒲 ⥤ 𝒱} [Gs.Monoidal] {gs : 𝒴 ⥤ 𝒵} [gs.Monoidal]
    (q : 𝒴 ⥤ 𝒲) [q.Monoidal] (qZ : 𝒵 ⥤ 𝒱) [qZ.Monoidal] (θ : q ⋙ Gs ≅ gs ⋙ qZ)
    (hθ : ∀ A B, θ.hom.app (A ⊗ B) ≫ qZ.map (δ gs A B) ≫ δ qZ (gs.obj A) (gs.obj B) =
      Gs.map (δ q A B) ≫ δ Gs (q.obj A) (q.obj B) ≫ (θ.hom.app A ⊗ₘ θ.hom.app B)) (M B : 𝒴) :
    (qZ.obj (gs.obj M) ◁ θ.hom.app B) ≫ μ qZ (gs.obj M) (gs.obj B) ≫ qZ.map (μ gs M B) ≫
        θ.inv.app (M ⊗ B) =
      (θ.inv.app M ▷ Gs.obj (q.obj B)) ≫ μ Gs (q.obj M) (q.obj B) ≫ Gs.map (μ q M B) := by
  rw [← cancel_mono (θ.hom.app (M ⊗ B) ≫ qZ.map (δ gs M B) ≫ δ qZ (gs.obj M) (gs.obj B))]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [hθ]
  simp only [tensorHom_def]
  simp

/-- The transpose of a projection comparison under an exchange morphism: for adjunctions
`go ⊣ gs` and `Go ⊣ Gs` with monoidal right adjoints, and the exchange morphism
`E : qZ ⋙ Go ⟶ go ⋙ q` of a monoidal isomorphism `θ : q ⋙ Gs ≅ gs ⋙ qZ`, the projection
comparisons are compatible with `E`. -/
lemma projectionComparison_exchangeLeft {go : 𝒵 ⥤ 𝒴} {gs : 𝒴 ⥤ 𝒵} [gs.Monoidal]
    (ag : go ⊣ gs) {Go : 𝒱 ⥤ 𝒲} {Gs : 𝒲 ⥤ 𝒱} [Gs.Monoidal] (aG : Go ⊣ Gs)
    (q : 𝒴 ⥤ 𝒲) [q.Monoidal] (qZ : 𝒵 ⥤ 𝒱) [qZ.Monoidal] (θ : q ⋙ Gs ≅ gs ⋙ qZ)
    (hθ : ∀ A B, θ.hom.app (A ⊗ B) ≫ qZ.map (δ gs A B) ≫ δ qZ (gs.obj A) (gs.obj B) =
      Gs.map (δ q A B) ≫ δ Gs (q.obj A) (q.obj B) ≫ (θ.hom.app A ⊗ₘ θ.hom.app B)) (A : 𝒵)
    (B : 𝒴) :
    Go.map (qZ.obj A ◁ θ.hom.app B ≫ μ qZ A (gs.obj B)) ≫
        (Adjunction.exchangeLeft ag aG θ.symm).app (A ⊗ gs.obj B) ≫
        q.map (ag.projectionComparison A B) =
      aG.projectionComparison (qZ.obj A) (q.obj B) ≫
        ((Adjunction.exchangeLeft ag aG θ.symm).app A ▷ q.obj B) ≫ μ q (go.obj A) B := by
  have hE (K : 𝒵) : aG.homEquiv _ _ ((Adjunction.exchangeLeft ag aG θ.symm).app K) =
      qZ.map (ag.unit.app K) ≫ θ.inv.app (go.obj K) := by
    rw [Adjunction.exchangeLeft_app, ← Functor.map_comp_assoc, aG.homEquiv_naturality_left,
      Adjunction.homEquiv_unit]
    simp
  have hPC : ag.unit.app (A ⊗ gs.obj B) ≫ gs.map (ag.projectionComparison A B) =
      ag.unit.app A ▷ gs.obj B ≫ μ gs (go.obj A) B := by
    erw [← ag.homEquiv_unit, Adjunction.projectionComparison, Equiv.apply_symm_apply]
  have hPCG : aG.homEquiv _ _ (aG.projectionComparison (qZ.obj A) (q.obj B)) =
      aG.unit.app (qZ.obj A) ▷ Gs.obj (q.obj B) ≫ μ Gs (Go.obj (qZ.obj A)) (q.obj B) := by
    rw [Adjunction.projectionComparison, Equiv.apply_symm_apply]
  apply (aG.homEquiv _ _).injective
  rw [aG.homEquiv_naturality_left, aG.homEquiv_naturality_right, hE,
    aG.homEquiv_naturality_right]
  erw [hPCG]
  have hθn := θ.inv.naturality (ag.projectionComparison A B)
  dsimp at hθn
  simp only [Category.assoc]
  rw [← hθn, ← qZ.map_comp_assoc, hPC, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← μ_natural_left_assoc, ← μ_natural_left_assoc, ← comp_whiskerRight_assoc]
  erw [← aG.homEquiv_unit, hE A]
  erw [whisker_exchange_assoc, whiskerLeft_hom_μ_inv_of_δ q qZ θ hθ]
  rw [comp_whiskerRight_assoc]
  rfl


/-- **Projection morphisms inverse to projection comparisons are compatible with base change**:
let `g ≅ go` and `G ≅ Go` with adjunctions `go ⊣ gs` and `Go ⊣ Gs` (monoidal right adjoints),
and let the projection morphisms `pfg`, `pfG` be inverse to the projection comparisons of these
adjunctions (`hpfg`, `hpfG`). If the base change `BC` is, through `g ≅ go` and `G ≅ Go`, inverse
to the exchange morphism of `θ⁻¹` (`hBC`) and `θ` is monoidal (`hθ`), then `PFBaseChange` holds.
This applies to open immersions, `go` and `Go` being the extensions by zero. -/
lemma pfBaseChange_of_projectionComparison {g go : 𝒵 ⥤ 𝒴} {gs : 𝒴 ⥤ 𝒵} [gs.Monoidal]
    (ag : go ⊣ gs) {G Go : 𝒱 ⥤ 𝒲} {Gs : 𝒲 ⥤ 𝒱} [Gs.Monoidal] (aG : Go ⊣ Gs)
    (lg : g ≅ go) (lG : G ≅ Go) (q : 𝒴 ⥤ 𝒲) [q.Monoidal] (qZ : 𝒵 ⥤ 𝒱) [qZ.Monoidal]
    (BC : g ⋙ q ⟶ qZ ⋙ G) [IsIso BC] (θ : q ⋙ Gs ≅ gs ⋙ qZ)
    (pfg : curriedTensorInsertFunctor₁ g ⟶
      curriedTensorPost g ⋙ (Functor.whiskeringLeft 𝒴 𝒵 𝒴).obj gs)
    (pfG : curriedTensorInsertFunctor₁ G ⟶
      curriedTensorPost G ⋙ (Functor.whiskeringLeft 𝒲 𝒱 𝒲).obj Gs)
    [∀ A B, IsIso ((pfG.app A).app B)]
    (hpfg : ∀ A B, (pfg.app A).app B ≫ lg.hom.app (A ⊗ gs.obj B) ≫
      ag.projectionComparison A B = lg.hom.app A ▷ B)
    (hpfG : ∀ A B, (pfG.app A).app B ≫ lG.hom.app (A ⊗ Gs.obj B) ≫
      aG.projectionComparison A B = lG.hom.app A ▷ B)
    (hBC : ∀ K, BC.app K ≫ lG.hom.app (qZ.obj K) ≫
      (Adjunction.exchangeLeft ag aG θ.symm).app K = q.map (lg.hom.app K))
    (hθ : ∀ A B, θ.hom.app (A ⊗ B) ≫ qZ.map (δ gs A B) ≫ δ qZ (gs.obj A) (gs.obj B) =
      Gs.map (δ q A B) ≫ δ Gs (q.obj A) (q.obj B) ≫ (θ.hom.app A ⊗ₘ θ.hom.app B)) :
    PFBaseChange q qZ BC θ pfg pfG := by
  intro A B
  have hE : IsIso ((Adjunction.exchangeLeft ag aG θ.symm).app A) := by
    have : IsIso ((BC.app A ≫ lG.hom.app (qZ.obj A)) ≫
        (Adjunction.exchangeLeft ag aG θ.symm).app A) := by
      rw [Category.assoc, hBC]
      infer_instance
    exact IsIso.of_isIso_comp_left (BC.app A ≫ lG.hom.app (qZ.obj A)) _
  have hPC : IsIso (aG.projectionComparison (qZ.obj A) (q.obj B)) := by
    have : IsIso (((pfG.app (qZ.obj A)).app (q.obj B) ≫
        lG.hom.app (qZ.obj A ⊗ Gs.obj (q.obj B))) ≫
        aG.projectionComparison (qZ.obj A) (q.obj B)) := by
      rw [Category.assoc, hpfG]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((pfG.app (qZ.obj A)).app (q.obj B) ≫ lG.hom.app (qZ.obj A ⊗ Gs.obj (q.obj B))) _
  rw [← cancel_mono (lG.hom.app (qZ.obj A ⊗ Gs.obj (q.obj B)) ≫
    aG.projectionComparison (qZ.obj A) (q.obj B) ≫
    ((Adjunction.exchangeLeft ag aG θ.symm).app A ▷ q.obj B) ≫ μ q (go.obj A) B)]
  have hR : δ q (g.obj A) B ≫ (BC.app A ▷ q.obj B) ≫ (pfG.app (qZ.obj A)).app (q.obj B) ≫
      lG.hom.app (qZ.obj A ⊗ Gs.obj (q.obj B)) ≫ aG.projectionComparison (qZ.obj A) (q.obj B) ≫
      ((Adjunction.exchangeLeft ag aG θ.symm).app A ▷ q.obj B) ≫ μ q (go.obj A) B =
      q.map (lg.hom.app A ▷ B) := by
    rw [reassoc_of% (hpfG (qZ.obj A) (q.obj B)), ← comp_whiskerRight_assoc,
      ← comp_whiskerRight_assoc, Category.assoc, hBC, μ_natural_left, Functor.Monoidal.δ_μ_assoc]
  have hL := lG.hom.naturality (δ qZ A (gs.obj B) ≫ qZ.obj A ◁ θ.inv.app B)
  have hk := projectionComparison_exchangeLeft ag aG q qZ θ hθ A B
  dsimp at hL
  simp only [Category.assoc]
  rw [hR, ← G.map_comp_assoc, reassoc_of% hL, ← hk, ← Go.map_comp_assoc]
  have hid : (δ qZ A (gs.obj B) ≫ qZ.obj A ◁ θ.inv.app B) ≫ qZ.obj A ◁ θ.hom.app B ≫
      μ qZ A (gs.obj B) = 𝟙 _ := by
    simp only [Category.assoc]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id_app]
    simp
  rw [hid, Go.map_id, Category.id_comp, reassoc_of% (hBC (A ⊗ gs.obj B)), ← q.map_comp,
    ← q.map_comp, hpfg]

end ProjectionComparison

end CategoryTheory.ProjectionBaseChange
