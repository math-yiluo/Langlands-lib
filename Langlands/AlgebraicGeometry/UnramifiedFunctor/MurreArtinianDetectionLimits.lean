import Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingLocus
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsAffine
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Spreading and affine limits for Murre's Lemma 1 -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.UnramifiedFunctor.BaseChange
open Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing
open Langlands.AlgebraicGeometry.UnramifiedFunctor.Charts (ovR)

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianDetection

section Spreading

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v} {T U : Over S}
  {ξ : F.obj (op U)}

/-- Two maps equal on the source stalk agree on an open neighbourhood of the point. -/
theorem exists_open_agreement (t : T.left) [T.left.IsGermInjectiveAt t] {g₁ g₂ : T ⟶ U}
    (h : stalkPt T t ≫ g₁ = stalkPt T t ≫ g₂) :
    ∃ V : T.left.Opens, t ∈ V ∧ ιOver T V ≫ g₁ = ιOver T V ≫ g₂ := by
  obtain ⟨V, htV, heq⟩ := spread_out_unique_of_isGermInjective' g₁.left g₂.left
    (congrArg (fun g ↦ g.left) h)
  exact ⟨V, htV, Over.OverMorphism.ext heq⟩

set_option backward.isDefEq.respectTransparency false in
/-- A factorization of the germ of a section spreads to an open neighbourhood. -/
theorem exists_open_factorization (hZ : ZariskiSheaf F) (h2 : FilteredColimits F)
    [LocallyOfFiniteType U.hom] (η : F.obj (op T)) (t : T.left)
    [T.left.IsGermInjectiveAt t] (h : Fac ξ η (stalkPt T t)) :
    ∃ V : T.left.Opens, t ∈ V ∧ Fac ξ η (ιOver T V) := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨V, htV, f, hfk, hfw⟩ := spread_out_of_isGermInjective' T.hom U.hom k.left (Over.w k)
  let TV : Over S := Over.mk (V.ι ≫ T.hom)
  let f' : TV ⟶ U := Over.homMk f hfw
  let σ : Over.mk (T.left.fromSpecStalk t ≫ T.hom) ⟶ TV :=
    Over.homMk (V.fromSpecStalkOfMem t htV) (by
      change V.fromSpecStalkOfMem t htV ≫ V.ι ≫ T.hom = T.left.fromSpecStalk t ≫ T.hom
      rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι])
  have hσf : σ ≫ f' = k := Over.OverMorphism.ext hfk.symm
  have hσι : σ ≫ ιOver T V = stalkPt T t :=
    Over.OverMorphism.ext (Scheme.Opens.fromSpecStalkOfMem_ι V t htV)
  have hσ : F.map σ.op (F.map f'.op ξ) = F.map σ.op (F.map (ιOver T V).op η) := by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hσf, hσι, hk]
  let ε : Over.mk (TV.left.fromSpecStalk ⟨t, htV⟩ ≫ TV.hom) ⟶
      Over.mk (T.left.fromSpecStalk t ≫ T.hom) :=
    Over.homMk (Spec.map (V.ι.stalkMap ⟨t, htV⟩)) (by
      have hι := Scheme.SpecMap_stalkMap_fromSpecStalk V.ι (x := ⟨t, htV⟩) =≫ T.hom
      simp only [Category.assoc] at hι
      exact hι)
  have hεσ : ε ≫ σ = stalkPt TV ⟨t, htV⟩ := by
    apply Over.OverMorphism.ext
    change Spec.map (V.ι.stalkMap ⟨t, htV⟩) ≫ V.fromSpecStalkOfMem t htV =
      V.toScheme.fromSpecStalk ⟨t, htV⟩
    rw [Scheme.Opens.fromSpecStalkOfMem, ← Category.assoc, ← Spec.map_comp, IsIso.inv_hom_id,
      Spec.map_id, Category.id_comp]
  have hstalk : F.map (stalkPt TV ⟨t, htV⟩).op (F.map f'.op ξ) =
      F.map (stalkPt TV ⟨t, htV⟩).op (F.map (ιOver T V).op η) := by
    rw [← hεσ, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hσ]
  obtain ⟨V', hV', heq⟩ := exists_opens_eq_of_stalkPt hZ h2 (T := TV) ⟨t, htV⟩ _ _ hstalk
  have hloc : LocFac (T := TV) ξ (F.map (ιOver T V).op η) (⟨t, htV⟩ : V) :=
    ⟨V', hV', (⟨ιOver TV V' ≫ f', by rw [op_comp, Functor.map_comp_apply, heq]⟩ :
      Fac ξ _ _)⟩
  have : IsOpenImmersion (ιOver T V).left := by
    change IsOpenImmersion V.ι
    infer_instance
  exact LocFac.of_map (ιOver T V) hloc

end Spreading

section Affine

variable {A : CommRingCat.{u}} {F : (Over (Spec A))ᵒᵖ ⥤ Type v}
  {U : Over (Spec A)} {ξ : F.obj (op U)}

private def affineIso (A : CommRingCat.{u}) (B : Type u) [CommRing B] [Algebra A B] :
    algebraOver (𝟙 (Spec A)) B ≅ ovR A B :=
  Over.isoMk (Iso.refl _) (by simp)

private abbrev adjoinProjection (A : CommRingCat.{u}) (B : Type u) [CommRing B] [Algebra A B]
    (s : Finset B) :
    algebraOver (𝟙 (Spec A)) B ⟶ algebraOver (𝟙 (Spec A)) (Algebra.adjoin A (s : Set B)) :=
  ((specOver (𝟙 (Spec A))).map ((adjoinCocone A B).ι.app s)).unop

private abbrev adjoinTransition (A : CommRingCat.{u}) (B : Type u) [CommRing B] [Algebra A B]
    {s t : Finset B} (i : s ⟶ t) :
    algebraOver (𝟙 (Spec A)) (Algebra.adjoin A (t : Set B)) ⟶
      algebraOver (𝟙 (Spec A)) (Algebra.adjoin A (s : Set B)) :=
  ((specOver (𝟙 (Spec A))).map ((adjoinDiagram A B).map i)).unop

private theorem adjoinProjection_comp (A : CommRingCat.{u}) (B : Type u)
    [CommRing B] [Algebra A B] {s t : Finset B} (i : s ⟶ t) :
    adjoinProjection A B t ≫ adjoinTransition A B i = adjoinProjection A B s := by
  let E := specOver (𝟙 (Spec A))
  let c := adjoinCocone A B
  change (E.map (c.ι.app t)).unop ≫ (E.map ((adjoinDiagram A B).map i)).unop =
    (E.map (c.ι.app s)).unop
  rw [← unop_comp, ← Functor.map_comp, c.w]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_affine_factorization [LocallyOfFinitePresentation U.hom]
    {B : Type u} [CommRing B] [Algebra A B] (g : algebraOver (𝟙 (Spec A)) B ⟶ U) :
    ∃ (s : Finset B) (g' : algebraOver (𝟙 (Spec A)) (Algebra.adjoin A (s : Set B)) ⟶ U),
      adjoinProjection A B s ≫ g' = g := by
  classical
  let E := specOver (𝟙 (Spec A))
  let D := (adjoinDiagram A B ⋙ E).leftOp
  let c := (Over.forget (Spec A)).mapCone (coneLeftOpOfCocone (E.mapCocone (adjoinCocone A B)))
  have : IsConnected (Finset B) := IsFiltered.isConnected _
  have hcR := isColimitOfPreserves (Under.forget A) (isColimitAdjoinCocone A B)
  have hc : IsLimit c :=
    isLimitConeLeftOpOfCocone _ (isColimitOfPreserves Scheme.Spec.rightOp hcR)
  let t : D ⋙ Over.forget (Spec A) ⟶ (Functor.const (Finset B)ᵒᵖ).obj (Spec A) :=
    { app s := (D.obj s).hom
      naturality i j f := by
        change (D.map f).left ≫ (D.obj j).hom = (D.obj i).hom ≫ 𝟙 (Spec A)
        rw [Category.comp_id, Over.w] }
  have (s : (Finset B)ᵒᵖ) : CompactSpace ((D ⋙ Over.forget (Spec A)).obj s) := by
    change CompactSpace (Spec (CommRingCat.of (Algebra.adjoin A (s.unop : Set B))))
    infer_instance
  have (s : (Finset B)ᵒᵖ) : QuasiSeparatedSpace ((D ⋙ Over.forget (Spec A)).obj s) := by
    change QuasiSeparatedSpace (Spec (CommRingCat.of (Algebra.adjoin A (s.unop : Set B))))
    infer_instance
  have {i j : (Finset B)ᵒᵖ} (f : i ⟶ j) : IsAffineHom ((D ⋙ Over.forget (Spec A)).map f) := by
    change IsAffineHom (Spec.map _)
    infer_instance
  have hg : c.π ≫ t = (Functor.const (Finset B)ᵒᵖ).map (g.left ≫ U.hom) := by
    ext s
    change (c.π.app s) ≫ (D.obj s).hom = g.left ≫ U.hom
    exact (Over.w (adjoinProjection A B s.unop)).trans (Over.w g).symm
  obtain ⟨s, g', hfactor, hbase⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation _ t U.hom c hc g.left hg
  exact ⟨s.unop, Over.homMk g' hbase, Over.OverMorphism.ext hfactor⟩

set_option backward.isDefEq.respectTransparency false in
/-- Injectivity of the comparison on finite-type algebras implies injectivity on every affine. -/
theorem affineInjective (h2 : FilteredColimits F) [LocallyOfFinitePresentation U.hom]
    (hFinite : ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B],
      Function.Injective (fun g : ovR A B ⟶ U ↦ F.map g.op ξ))
    (B : Type u) [CommRing B] [Algebra A B] :
    Function.Injective (fun g : ovR A B ⟶ U ↦ F.map g.op ξ) := by
  intro g₁ g₂ heq
  let e := affineIso A B
  apply (cancel_epi e.hom).mp
  let E := specOver (𝟙 (Spec A))
  let c := adjoinCocone A B
  obtain ⟨s₁, g₁', h₁⟩ := exists_affine_factorization (e.hom ≫ g₁)
  obtain ⟨s₂, g₂', h₂⟩ := exists_affine_factorization (e.hom ≫ g₂)
  have hEq :
      (E ⋙ F).map (c.ι.app s₁) (F.map g₁'.op ξ) =
      (E ⋙ F).map (c.ι.app s₂) (F.map g₂'.op ξ) := by
    change F.map (adjoinProjection A B s₁).op (F.map g₁'.op ξ) =
      F.map (adjoinProjection A B s₂).op (F.map g₂'.op ξ)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, h₁, h₂]
    simp only [op_comp, Functor.map_comp_apply, heq]
  have hGood := good_of_isOpenImmersion h2 (𝟙 (Spec A))
  have := hGood.preserves_filtered_colimits (Finset B)
  obtain ⟨s, i₁, i₂, hi⟩ := (Types.FilteredColimit.isColimit_eq_iff _
    (isColimitOfPreserves (E ⋙ F) (isColimitAdjoinCocone A B))).mp hEq
  let g₁s := adjoinTransition A B i₁ ≫ g₁'
  let g₂s := adjoinTransition A B i₂ ≫ g₂'
  let es := affineIso A (Algebra.adjoin A (s : Set B))
  have : Algebra.FiniteType A (Algebra.adjoin A (s : Set B)) :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset s)
  have hstage : g₁s = g₂s := by
    apply (cancel_epi es.inv).mp
    apply hFinite (Algebra.adjoin A (s : Set B))
    simp only [g₁s, g₂s, op_comp, Functor.map_comp_apply]
    exact congrArg (F.map es.inv.op) hi
  calc
    e.hom ≫ g₁ = adjoinProjection A B s ≫ g₁s := by
      simp only [g₁s, ← Category.assoc, adjoinProjection_comp, h₁]
    _ = adjoinProjection A B s ≫ g₂s := by rw [hstage]
    _ = e.hom ≫ g₂ := by
      simp only [g₂s, ← Category.assoc, adjoinProjection_comp, h₂]

set_option backward.isDefEq.respectTransparency false in
/-- Surjectivity of the comparison on finite-type algebras implies surjectivity on every affine. -/
theorem affineSurjective (h2 : FilteredColimits F)
    (hFinite : ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B],
      Function.Surjective (fun g : ovR A B ⟶ U ↦ F.map g.op ξ))
    (B : Type u) [CommRing B] [Algebra A B] :
    Function.Surjective (fun g : ovR A B ⟶ U ↦ F.map g.op ξ) := by
  intro η
  let e := affineIso A B
  obtain ⟨s, x, hx⟩ := exists_of_isColimit (good_of_isOpenImmersion h2 (𝟙 (Spec A)))
    (isColimitAdjoinCocone A B) (F.map e.hom.op η)
  change F.obj (op (algebraOver (𝟙 (Spec A)) (Algebra.adjoin A (s : Set B)))) at x
  let es := affineIso A (Algebra.adjoin A (s : Set B))
  have : Algebra.FiniteType A (Algebra.adjoin A (s : Set B)) :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset s)
  obtain ⟨g, hg⟩ := hFinite (Algebra.adjoin A (s : Set B)) (F.map es.inv.op x)
  let π := adjoinProjection A B s
  have hπ : F.map π.op x = F.map e.hom.op η := hx
  change F.map g.op ξ = F.map es.inv.op x at hg
  have hs : F.map es.hom.op (F.map g.op ξ) = x := by
    rw [hg, ← Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id, op_id, F.map_id, types_id_apply]
  refine ⟨e.inv ≫ π ≫ es.hom ≫ g, ?_⟩
  change F.map (e.inv ≫ π ≫ es.hom ≫ g).op ξ = η
  simp only [op_comp, Functor.map_comp_apply, hs, hπ]
  rw [← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id, F.map_id, types_id_apply]

end Affine

end Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianDetection
