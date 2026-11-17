import Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.ChartProperties
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability
import Langlands.AlgebraicGeometry.FaithfullyFlatQuasiAffineDescent

/-! # Fppf descent of quasi-affine representability -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.UnramifiedFunctor
open Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent

noncomputable section

namespace Langlands.AlgebraicGeometry.FppfQuasiAffineRepresentabilityDescent

variable {S S' : Scheme.{u}} {π : S' ⟶ S} {F : (Over S)ᵒᵖ ⥤ Type v}

/-- A genuine fppf sheaf satisfies descent along each singleton fppf cover. -/
theorem isSheafFor_singleton
    (hF : Presheaf.IsSheaf (AlgebraicSpace.fppfTopology S) F)
    {U V : Over S} (f : U ⟶ V)
    [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left] :
    Presieve.IsSheafFor F (Presieve.singleton f) := by
  have h := (isSheaf_iff_isSheaf_of_type _ _).mp hF
  exact (Presieve.isSheafFor_iff_generate _).mpr
    (h _ (AlgebraicSpace.generate_singleton_mem_fppfTopology f))

lemma locallyOfFinitePresentation_pullHom [LocallyOfFinitePresentation π] (T : Over S) :
    LocallyOfFinitePresentation (pullHom π T).left :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
    (IsPullback.of_hasPullback T.hom π).flip inferInstance

/-- Pullback to an fppf cover of the base detects equality in an fppf sheaf. -/
lemma injective_map_pullHom
    (hF : Presheaf.IsSheaf (AlgebraicSpace.fppfTopology S) F)
    [Flat π] [Surjective π] [LocallyOfFinitePresentation π] (T : Over S) :
    Function.Injective (F.map (pullHom π T).op) := by
  have := flat_pullHom π T
  have := surjective_pullHom π T
  have := locallyOfFinitePresentation_pullHom (π := π) T
  exact Presieve.isSeparatedFor_singleton.1 (isSheafFor_singleton hF (pullHom π T)).isSeparatedFor

variable {X' : Scheme.{u}} {q' : X' ⟶ S'}
  (e : (baseChange π F).RepresentableBy (Over.mk q'))
  {σ : pullback (q' ≫ π) π ⟶ X'} (hσ : σ ≫ q' = pullback.snd _ _)
  (hσpt : pt e (prodOver q' π) σ (sigma_comp_eq hσ) =
    pt e (prodOver q' π) (pullback.fst _ _) (fst_comp_eq q' π))
  {W : Scheme.{u}} (j : W ⟶ X') [IsOpenImmersion j]
  (hsat : ∀ z, pullback.fst (q' ≫ π) π z ∈ Set.range j → σ z ∈ Set.range j)
  {V : Scheme.{u}} {w : V ⟶ S} {p : W ⟶ V} (hpb : IsPullback p (j ≫ q') w π)
  (hfst : pullback.fst ((j ≫ q') ≫ π) π ≫ p = chartSigma j hsat ≫ p)

include hσ hσpt hfst in
/-- The element `pt j ∈ F(W)` descends along `p`. -/
theorem exists_isChartElement (hF : Presheaf.IsSheaf (AlgebraicSpace.fppfTopology S) F) [Flat π] [Surjective π]
    [LocallyOfFinitePresentation π] : ∃ ξ : F.obj (op (Over.mk w)), IsChartElement e j hpb ξ := by
  have hflat : Flat (chartHom j hpb).left :=
    MorphismProperty.of_isPullback (P := @Flat) hpb.flip inferInstance
  have hsurj : Surjective (chartHom j hpb).left :=
    MorphismProperty.of_isPullback (P := @Surjective) hpb.flip inferInstance
  have hlfp : LocallyOfFinitePresentation (chartHom j hpb).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb.flip inferInstance
  obtain ⟨ξ, hξ, -⟩ := Presieve.isSheafFor_singleton.1 (isSheafFor_singleton hF (chartHom j hpb))
    (pt e (chartOver j q' π) j (Category.assoc _ _ _).symm) (by
      intro Z p₁ p₂ hp
      rw [pt_comp, pt_comp]
      have h₁ : p₁.left ≫ j ≫ q' ≫ π = Z.hom := by
        rw [← Over.w p₁]
        simp only [Over.mk_hom, Category.assoc]
      have h₂ : p₂.left ≫ j ≫ q' ≫ π = Z.hom := by
        rw [← Over.w p₂]
        simp only [Over.mk_hom, Category.assoc]
      exact pt_eq_of_comp_p_eq e hσ hσpt j hsat hpb hfst h₁ h₂
        (congrArg CommaMorphism.left hp))
  exact ⟨ξ, hξ⟩

include hσ hσpt hfst in
/-- An element `v ∈ F(T)` factors through `ξ` if the morphism `T ×_S S' ⟶ X'` defined by `v`
lands in `W`. -/
theorem exists_map_eq_of_range_subset (hF : Presheaf.IsSheaf (AlgebraicSpace.fppfTopology S) F) [Flat π] [Surjective π]
    [QuasiCompact π] [LocallyOfFinitePresentation π] {ξ : F.obj (op (Over.mk w))} (hξ : IsChartElement e j hpb ξ) (T : Over S)
    (v : F.obj (op T)) (v' : pullback T.hom π ⟶ X') (hv'q : v' ≫ q' = pullback.snd _ _)
    (hv' : pt e (pullOver π T) v' (by rw [← Category.assoc, hv'q]; rfl) =
      F.map (pullHom π T).op v)
    (hr : Set.range v' ⊆ Set.range j) : ∃ h : T ⟶ Over.mk w, F.map h.op ξ = v := by
  have hfl : Flat (pullback.fst T.hom π) := flat_pullHom π T
  have hsu : Surjective (pullback.fst T.hom π) := surjective_pullHom π T
  have hqc : QuasiCompact (pullback.fst T.hom π) := quasiCompact_pullHom π T
  have : Epi (pullback.fst T.hom π) := Flat.epi_of_flat_of_surjective _
  obtain ⟨v'', hv''⟩ : ∃ v'' : pullback T.hom π ⟶ W, v'' ≫ j = v' :=
    ⟨_, IsOpenImmersion.lift_fac j v' hr⟩
  have hv''q : v'' ≫ j ≫ q' ≫ π = (pullOver π T).hom := by
    rw [reassoc_of% hv'', reassoc_of% hv'q]
    rfl
  have hcompat : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ pullback T.hom π),
      g₁ ≫ pullback.fst T.hom π = g₂ ≫ pullback.fst T.hom π → g₁ ≫ v'' ≫ p = g₂ ≫ v'' ≫ p := by
    intro Z g₁ g₂ hg
    let TZ : Over S := Over.mk (g₁ ≫ pullback.fst T.hom π ≫ T.hom)
    have hg₁ : g₁ ≫ (pullOver π T).hom = TZ.hom := by
      show g₁ ≫ pullback.snd T.hom π ≫ π = g₁ ≫ pullback.fst T.hom π ≫ T.hom
      rw [pullback.condition]
    have hg₂ : g₂ ≫ (pullOver π T).hom = TZ.hom := by
      show g₂ ≫ pullback.snd T.hom π ≫ π = g₁ ≫ pullback.fst T.hom π ≫ T.hom
      have h := congrArg (· ≫ T.hom) hg
      simp only [Category.assoc] at h
      rw [h, pullback.condition]
    have h₁ : (g₁ ≫ v'') ≫ j ≫ q' ≫ π = TZ.hom := by rw [Category.assoc, hv''q]; exact hg₁
    have h₂ : (g₂ ≫ v'') ≫ j ≫ q' ≫ π = TZ.hom := by rw [Category.assoc, hv''q]; exact hg₂
    have key : ∀ (g : Z ⟶ pullback T.hom π) (hg' : g ≫ (pullOver π T).hom = TZ.hom)
        (hgv : (g ≫ v'') ≫ j ≫ q' ≫ π = TZ.hom),
        pt e TZ ((g ≫ v'') ≫ j) (by rw [Category.assoc]; exact hgv) =
          F.map (Over.homMk g hg' ≫ pullHom π T).op v := by
      intro g hg' hgv
      rw [← map_map, ← hv', pt_comp]
      exact pt_congr e (by rw [Category.assoc, hv'']; rfl) _ _
    have hO : (Over.homMk g₁ hg₁ : TZ ⟶ pullOver π T) ≫ pullHom π T =
        (Over.homMk g₂ hg₂ : TZ ⟶ pullOver π T) ≫ pullHom π T := by
      ext
      simp only [Over.comp_left, Over.homMk_left, pullHom_left]
      exact hg
    have hpt := (key g₁ hg₁ h₁).trans ((congrArg (fun f ↦ F.map f.op v) hO).trans
      (key g₂ hg₂ h₂).symm)
    simpa only [Category.assoc] using comp_p_eq_of_pt_eq e hσ hσpt j hsat hfst h₁ h₂ hpt
  obtain ⟨u₀, hu₀fac⟩ : ∃ u₀ : T.left ⟶ V, pullback.fst T.hom π ≫ u₀ = v'' ≫ p :=
    ⟨_, EffectiveEpi.fac _ _ hcompat⟩
  have hu₀ : u₀ ≫ w = T.hom := by
    rw [← cancel_epi (pullback.fst T.hom π), ← Category.assoc, hu₀fac, Category.assoc, hpb.w,
      pullback.condition]
    simp only [Category.assoc]
    exact hv''q
  refine ⟨Over.homMk u₀ hu₀, ?_⟩
  apply injective_map_pullHom (π := π) hF T
  have hh : pullHom π T ≫ (Over.homMk u₀ hu₀ : T ⟶ Over.mk w) =
      (Over.homMk (v'' ≫ p) (comp_p_w (T := pullOver π T) j hpb v'' hv''q) :
        pullOver π T ⟶ Over.mk w) := by
    ext
    simp only [Over.comp_left, Over.homMk_left, pullHom_left]
    exact hu₀fac
  rw [map_map, hh, ← pt_comp_chart e j hpb hξ (T := pullOver π T) v'' hv''q]
  refine Eq.trans ?_ hv'
  exact pt_congr e hv'' _ _

include e in
/-- An fppf sheaf whose restriction to an affine fppf cover has a quasi-affine
representing scheme is itself represented by a quasi-affine scheme. -/
theorem exists_representableBy_of_baseChange
    [IsAffine S] [IsAffine S'] [Flat π] [Surjective π]
    [LocallyOfFinitePresentation π] [X'.IsQuasiAffine]
    (hF : Presheaf.IsSheaf (AlgebraicSpace.fppfTopology S) F) :
    ∃ (V : Scheme.{u}) (w : V ⟶ S) (_ : F.RepresentableBy (Over.mk w)), V.IsQuasiAffine := by
  obtain ⟨σ, hσ, hσpt⟩ := exists_sigma e
  let hsat : ∀ z, pullback.fst (q' ≫ π) π z ∈ Set.range (𝟙 X') →
      σ z ∈ Set.range (𝟙 X') := by
    intro z _
    exact ⟨σ z, rfl⟩
  obtain ⟨V, w, p, hpb, hfst⟩ := exists_chart_isPullback e hσ (𝟙 X') hsat hσpt
  obtain ⟨ξ, hξ⟩ := exists_isChartElement e hσ hσpt (𝟙 X') hsat hpb hfst hF
  have hbij (T : Over S) : Function.Bijective (fun h : T ⟶ Over.mk w => F.map h.op ξ) := by
    refine ⟨fun h₁ h₂ hh => isMonoElement_of_isChartElement e (𝟙 X') hpb hξ h₁ h₂ hh, ?_⟩
    intro v
    obtain ⟨v', hv'q, hv'⟩ := exists_pt e (pullOver π T) (pullback.snd T.hom π) rfl
      (F.map (pullHom π T).op v)
    exact exists_map_eq_of_range_subset e hσ hσpt (𝟙 X') hsat hpb hfst hF hξ T v v'
      hv'q hv' (by intro x _; exact ⟨x, rfl⟩)
  let r : F.RepresentableBy (Over.mk w) :=
    { homEquiv := fun {T} => Equiv.ofBijective _ (hbij T)
      homEquiv_comp := by
        intro T T' f g
        change F.map (f ≫ g).op ξ = F.map f.op (F.map g.op ξ)
        rw [op_comp, Functor.map_comp_apply] }
  exact ⟨V, w, r, FaithfullyFlatQuasiAffineDescent.isQuasiAffine_of_isPullback hpb⟩

include e in
/-- Choose the quasi-affine representing scheme supplied by fppf descent. -/
def quasiAffineModel
    [IsAffine S] [IsAffine S'] [Flat π] [Surjective π]
    [LocallyOfFinitePresentation π] [X'.IsQuasiAffine]
    (hF : Presheaf.IsSheaf (AlgebraicSpace.fppfTopology S) F) :
    {V : Over S // V.left.IsQuasiAffine ∧ Nonempty (F.RepresentableBy V)} := by
  classical
  have h : ∃ V : Over S, V.left.IsQuasiAffine ∧ Nonempty (F.RepresentableBy V) := by
    obtain ⟨V, w, r, hV⟩ := exists_representableBy_of_baseChange e hF
    exact ⟨Over.mk w, hV, ⟨r⟩⟩
  exact ⟨h.choose, h.choose_spec⟩

end Langlands.AlgebraicGeometry.FppfQuasiAffineRepresentabilityDescent
