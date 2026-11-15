import Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.ChartDatum
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalSteps
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # The element of `F` carried by a descended chart

Keep the notation of `ChartDatum`, and let `p : W ⟶ V` exhibit the saturated open
`j : W ⟶ X'` as the base change along `π` of a scheme `w : V ⟶ S`, with
`(first projection) ≫ p = σW ≫ p`. If `π` is flat, surjective and quasi-compact and `F` is a
sheaf for such morphisms, the element `pt j ∈ F(W)` descends to an element `ξ ∈ F(V)`. This
file shows that `ξ : V → F` is a monomorphism, is infinitesimally étale at every point, and
that `v ∈ F(T)` factors through `ξ` as soon as the morphism `T ×_S S' ⟶ X'` defined by `v`
lands in `W`. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent

section Base

variable {S S' : Scheme.{u}} (π : S' ⟶ S)

/-- The base change `T ×_S S'` of a test object `T`, as an object of `Over S`. -/
abbrev pullOver (T : Over S) : Over S := Over.mk (pullback.snd T.hom π ≫ π)

/-- The first projection `T ×_S S' ⟶ T` as a morphism of `Over S`. -/
def pullHom (T : Over S) : pullOver π T ⟶ T :=
  Over.homMk (pullback.fst T.hom π) pullback.condition

@[simp]
lemma pullHom_left (T : Over S) : (pullHom π T).left = pullback.fst T.hom π := rfl

lemma flat_pullHom [Flat π] (T : Over S) : Flat (pullHom π T).left :=
  MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback T.hom π).flip
    inferInstance

lemma surjective_pullHom [Surjective π] (T : Over S) : Surjective (pullHom π T).left :=
  MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback T.hom π).flip
    inferInstance

lemma quasiCompact_pullHom [QuasiCompact π] (T : Over S) : QuasiCompact (pullHom π T).left :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback T.hom π).flip
    inferInstance

/-- For a sheaf for flat surjective quasi-compact morphisms, restriction along
`T ×_S S' ⟶ T` is injective. -/
lemma injective_map_pullHom {F : (Over S)ᵒᵖ ⥤ Type v} (hF : FaithfullyFlatSheaf F) [Flat π]
    [Surjective π] [QuasiCompact π] (T : Over S) : Function.Injective (F.map (pullHom π T).op) :=
  Presieve.isSeparatedFor_singleton.1
    (hF _ (flat_pullHom π T) (surjective_pullHom π T) (quasiCompact_pullHom π T)).isSeparatedFor

end Base

lemma map_map {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v} {T₁ T₂ T₃ : Over S} (f : T₁ ⟶ T₂)
    (g : T₂ ⟶ T₃) (x : F.obj (op T₃)) : F.map f.op (F.map g.op x) = F.map (f ≫ g).op x := by
  rw [op_comp, Functor.map_comp_apply]

variable {S S' : Scheme.{u}} {π : S' ⟶ S} {F : (Over S)ᵒᵖ ⥤ Type v} {X' : Scheme.{u}}
  {q' : X' ⟶ S'} (e : (baseChange π F).RepresentableBy (Over.mk q'))
  {σ : pullback (q' ≫ π) π ⟶ X'} (hσ : σ ≫ q' = pullback.snd _ _)
  (hσpt : pt e (prodOver q' π) σ (sigma_comp_eq hσ) =
    pt e (prodOver q' π) (pullback.fst _ _) (fst_comp_eq q' π))
  {W : Scheme.{u}} (j : W ⟶ X') [IsOpenImmersion j]
  (hsat : ∀ z, pullback.fst (q' ≫ π) π z ∈ Set.range j → σ z ∈ Set.range j)
  {V : Scheme.{u}} {w : V ⟶ S} {p : W ⟶ V} (hpb : IsPullback p (j ≫ q') w π)
  (hfst : pullback.fst ((j ≫ q') ≫ π) π ≫ p = chartSigma j hsat ≫ p)

/-- The chart `W`, as an object of `Over S`. -/
abbrev chartOver (j : W ⟶ X') (q' : X' ⟶ S') (π : S' ⟶ S) : Over S := Over.mk ((j ≫ q') ≫ π)

/-- The morphism `p : W ⟶ V` of `Over S`. -/
def chartHom (hpb : IsPullback p (j ≫ q') w π) : chartOver j q' π ⟶ Over.mk w :=
  Over.homMk p hpb.w

/-- The condition on `ξ ∈ F(V)`: its pullback along `p` is the element `pt j` of `F(W)`. -/
def IsChartElement (hpb : IsPullback p (j ≫ q') w π) (ξ : F.obj (op (Over.mk w))) : Prop :=
  F.map (chartHom j hpb).op ξ = pt e (chartOver j q' π) j (Category.assoc _ _ _).symm

omit [IsOpenImmersion j] in
include hpb in
lemma comp_p_w {T : Over S} (k : T.left ⟶ W) (hk : k ≫ j ≫ q' ≫ π = T.hom) :
    (k ≫ p) ≫ w = T.hom := by
  rw [Category.assoc, hpb.w, Category.assoc]
  exact hk

omit [IsOpenImmersion j] in
/-- Pulling `ξ` back along `k ≫ p` gives `pt (k ≫ j)`. -/
lemma pt_comp_chart {ξ : F.obj (op (Over.mk w))} (hξ : IsChartElement e j hpb ξ) {T : Over S}
    (k : T.left ⟶ W) (hk : k ≫ j ≫ q' ≫ π = T.hom) :
    pt e T (k ≫ j) (by rw [Category.assoc]; exact hk) =
      F.map (Over.homMk (k ≫ p) (comp_p_w j hpb k hk) : T ⟶ Over.mk w).op ξ := by
  have hk' : k ≫ (chartOver j q' π).hom = T.hom := by
    simp only [Over.mk_hom, Category.assoc]
    exact hk
  have hfac : (Over.homMk (k ≫ p) (comp_p_w j hpb k hk) : T ⟶ Over.mk w) =
      (Over.homMk k hk' : T ⟶ chartOver j q' π) ≫ chartHom j hpb := by
    ext
    rfl
  unfold IsChartElement at hξ
  rw [hfac, ← map_map, hξ, pt_comp]
  rfl

include hσ hσpt hfst in
/-- Two morphisms to `W` with the same image in `F` agree after `p`. -/
lemma comp_p_eq_of_pt_eq {T : Over S} {a b : T.left ⟶ W} (ha : a ≫ j ≫ q' ≫ π = T.hom)
    (hb : b ≫ j ≫ q' ≫ π = T.hom)
    (h : pt e T (a ≫ j) (by rw [Category.assoc]; exact ha) =
      pt e T (b ≫ j) (by rw [Category.assoc]; exact hb)) :
    a ≫ p = b ≫ p := by
  have hab : a ≫ (j ≫ q') ≫ π = (b ≫ j ≫ q') ≫ π := by
    simp only [Category.assoc]
    exact ha.trans hb.symm
  let κ : T.left ⟶ pullback ((j ≫ q') ≫ π) π := pullback.lift a (b ≫ j ≫ q') hab
  have hκ : κ ≫ pullback.snd _ _ ≫ π = T.hom := by
    simp only [κ, pullback.lift_snd_assoc, Category.assoc]
    exact hb
  have key : κ ≫ chartSigma j hsat = b := by
    rw [← cancel_mono j]
    have h₁ := pt_chartSigma e hσ j hsat hσpt T κ hκ
    have h₂ := h₁.trans ((pt_congr e (by simp only [κ, pullback.lift_fst_assoc]) _ _).trans h)
    refine pt_inj e _ _ ?_ h₂
    simp only [Category.assoc, chartSigma_comp hσ j hsat, κ, pullback.lift_snd]
  calc a ≫ p = κ ≫ pullback.fst _ _ ≫ p := by simp only [κ, pullback.lift_fst_assoc]
    _ = κ ≫ chartSigma j hsat ≫ p := by rw [hfst]
    _ = b ≫ p := by rw [← Category.assoc, key]

include hσ hσpt hpb hfst in
/-- Two morphisms to `W` which agree after `p` have the same image in `F`. -/
lemma pt_eq_of_comp_p_eq {T : Over S} {a b : T.left ⟶ W} (ha : a ≫ j ≫ q' ≫ π = T.hom)
    (hb : b ≫ j ≫ q' ≫ π = T.hom) (h : a ≫ p = b ≫ p) :
    pt e T (a ≫ j) (by rw [Category.assoc]; exact ha) =
      pt e T (b ≫ j) (by rw [Category.assoc]; exact hb) := by
  have hab : a ≫ (j ≫ q') ≫ π = (b ≫ j ≫ q') ≫ π := by
    simp only [Category.assoc]
    exact ha.trans hb.symm
  let κ : T.left ⟶ pullback ((j ≫ q') ≫ π) π := pullback.lift a (b ≫ j ≫ q') hab
  have hκ : κ ≫ pullback.snd _ _ ≫ π = T.hom := by
    simp only [κ, pullback.lift_snd_assoc, Category.assoc]
    exact hb
  have key : κ ≫ chartSigma j hsat = b := by
    apply hpb.hom_ext
    · rw [Category.assoc, ← hfst]
      simp only [κ, pullback.lift_fst_assoc]
      exact h
    · rw [Category.assoc, chartSigma_comp hσ j hsat]
      simp only [κ, pullback.lift_snd]
  have h₁ := pt_chartSigma e hσ j hsat hσpt T κ hκ
  refine ((pt_congr e (by simp only [κ, pullback.lift_fst_assoc]) _ _).trans h₁.symm).trans
    (pt_congr e (by rw [← Category.assoc, key]) _ _)

include hσ hσpt hfst in
/-- The element `pt j ∈ F(W)` descends along `p`. -/
theorem exists_isChartElement (hF : FaithfullyFlatSheaf F) [Flat π] [Surjective π]
    [QuasiCompact π] : ∃ ξ : F.obj (op (Over.mk w)), IsChartElement e j hpb ξ := by
  have hflat : Flat (chartHom j hpb).left :=
    MorphismProperty.of_isPullback (P := @Flat) hpb.flip inferInstance
  have hsurj : Surjective (chartHom j hpb).left :=
    MorphismProperty.of_isPullback (P := @Surjective) hpb.flip inferInstance
  have hqc : QuasiCompact (chartHom j hpb).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hpb.flip inferInstance
  obtain ⟨ξ, hξ, -⟩ := Presieve.isSheafFor_singleton.1 (hF _ hflat hsurj hqc)
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

/-- The morphism `T ×_S S' ⟶ W` defined by `h : T ⟶ V`. -/
def chartLift {T : Over S} (h : T ⟶ Over.mk w) : pullback T.hom π ⟶ W :=
  hpb.lift (pullback.fst T.hom π ≫ h.left) (pullback.snd T.hom π) (by
    rw [Category.assoc, show h.left ≫ w = T.hom from Over.w h]
    exact pullback.condition)

omit [IsOpenImmersion j] in
@[reassoc (attr := simp)]
lemma chartLift_p {T : Over S} (h : T ⟶ Over.mk w) :
    chartLift j hpb h ≫ p = pullback.fst T.hom π ≫ h.left :=
  hpb.lift_fst _ _ _

omit [IsOpenImmersion j] in
@[reassoc (attr := simp)]
lemma chartLift_q {T : Over S} (h : T ⟶ Over.mk w) :
    chartLift j hpb h ≫ j ≫ q' = pullback.snd T.hom π :=
  hpb.lift_snd _ _ _

omit [IsOpenImmersion j] in
lemma chartLift_comp {T : Over S} (h : T ⟶ Over.mk w) :
    chartLift j hpb h ≫ j ≫ q' ≫ π = (pullOver π T).hom := by
  rw [chartLift_q_assoc]
  rfl

omit [IsOpenImmersion j] in
lemma pt_chartLift {ξ : F.obj (op (Over.mk w))} (hξ : IsChartElement e j hpb ξ) {T : Over S}
    (h : T ⟶ Over.mk w) :
    pt e (pullOver π T) (chartLift j hpb h ≫ j) (by
      rw [Category.assoc]; exact chartLift_comp j hpb h) =
      F.map (pullHom π T).op (F.map h.op ξ) := by
  have hh : (Over.homMk (chartLift j hpb h ≫ p) (comp_p_w j hpb _ (chartLift_comp j hpb h)) :
      pullOver π T ⟶ Over.mk w) = pullHom π T ≫ h := by
    ext
    simp [pullHom]
  rw [pt_comp_chart e j hpb hξ _ (chartLift_comp j hpb h), hh, map_map]

/-- `ξ : V → F` is a monomorphism. -/
theorem isMonoElement_of_isChartElement [Flat π] [Surjective π] {ξ : F.obj (op (Over.mk w))}
    (hξ : IsChartElement e j hpb ξ) : IsMonoElement F ξ := by
  intro T h₁ h₂ hh
  have k := (pt_chartLift e j hpb hξ h₁).trans ((congrArg _ hh).trans
    (pt_chartLift e j hpb hξ h₂).symm)
  have k' := pt_inj e _ _ (by rw [Category.assoc, Category.assoc, chartLift_q,
    chartLift_q]) k
  rw [cancel_mono] at k'
  have hfl : Flat (pullback.fst T.hom π) := flat_pullHom π T
  have hsu : Surjective (pullback.fst T.hom π) := surjective_pullHom π T
  have : Epi (pullback.fst T.hom π) := Flat.epi_of_flat_of_surjective _
  ext
  rw [← cancel_epi (pullback.fst T.hom π), ← chartLift_p j hpb h₁, ← chartLift_p j hpb h₂, k']

include hσ hσpt hfst in
/-- An element `v ∈ F(T)` factors through `ξ` if the morphism `T ×_S S' ⟶ X'` defined by `v`
lands in `W`. -/
theorem exists_map_eq_of_range_subset (hF : FaithfullyFlatSheaf F) [Flat π] [Surjective π]
    [QuasiCompact π] {ξ : F.obj (op (Over.mk w))} (hξ : IsChartElement e j hpb ξ) (T : Over S)
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
  apply injective_map_pullHom π hF T
  have hh : pullHom π T ≫ (Over.homMk u₀ hu₀ : T ⟶ Over.mk w) =
      (Over.homMk (v'' ≫ p) (comp_p_w (T := pullOver π T) j hpb v'' hv''q) :
        pullOver π T ⟶ Over.mk w) := by
    ext
    simp only [Over.comp_left, Over.homMk_left, pullHom_left]
    exact hu₀fac
  rw [map_map, hh, ← pt_comp_chart e j hpb hξ (T := pullOver π T) v'' hv''q]
  refine Eq.trans ?_ hv'
  exact pt_congr e hv'' _ _


omit [IsOpenImmersion j] in
/-- If `v ∈ F(T)` becomes, along a morphism `b : T₀ ⟶ T` that is surjective on points, an
element factoring through `ξ`, then the morphism `T ×_S S' ⟶ X'` defined by `v` lands in `W`. -/
lemma range_subset_of_map_eq {ξ : F.obj (op (Over.mk w))} (hξ : IsChartElement e j hpb ξ)
    {T₀ T : Over S} (b : T₀ ⟶ T) (hb : Function.Surjective b.left) (u₀ : T₀ ⟶ Over.mk w)
    (v : F.obj (op T)) (hv : F.map u₀.op ξ = F.map b.op v) (v' : pullback T.hom π ⟶ X')
    (hv'q : v' ≫ q' = pullback.snd _ _)
    (hv' : pt e (pullOver π T) v' (by rw [← Category.assoc, hv'q]; rfl) =
      F.map (pullHom π T).op v) :
    Set.range v' ⊆ Set.range j := by
  have hsurj : Surjective (pullback.snd b.left (pullback.fst T.hom π)) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback b.left (pullback.fst T.hom π)) ⟨hb⟩
  have hk : (pullback.fst b.left (pullback.fst T.hom π) ≫ u₀.left) ≫ w =
      (pullback.snd b.left (pullback.fst T.hom π) ≫ pullback.snd T.hom π) ≫ π := by
    have h₁ : u₀.left ≫ w = T₀.hom := Over.w u₀
    have h₂ : b.left ≫ T.hom = T₀.hom := Over.w b
    rw [Category.assoc, h₁, ← h₂, pullback.condition_assoc, Category.assoc, pullback.condition]
  let QO : Over S :=
    Over.mk (pullback.snd b.left (pullback.fst T.hom π) ≫ pullback.snd T.hom π ≫ π)
  obtain ⟨k₀, hk₀p, hk₀q⟩ : ∃ k₀ : pullback b.left (pullback.fst T.hom π) ⟶ W,
      k₀ ≫ p = pullback.fst b.left (pullback.fst T.hom π) ≫ u₀.left ∧
        k₀ ≫ j ≫ q' = pullback.snd b.left (pullback.fst T.hom π) ≫ pullback.snd T.hom π :=
    ⟨hpb.lift _ _ hk, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  have hk₀ : k₀ ≫ j ≫ q' ≫ π = QO.hom := by
    rw [reassoc_of% hk₀q]
    rfl
  have hfO : pullback.fst b.left (pullback.fst T.hom π) ≫ T₀.hom = QO.hom := by
    rw [← Over.w b, pullback.condition_assoc, pullback.condition]
    rfl
  let fO : QO ⟶ T₀ := Over.homMk (pullback.fst b.left (pullback.fst T.hom π)) hfO
  let iO : QO ⟶ pullOver π T := Over.homMk (pullback.snd b.left (pullback.fst T.hom π)) rfl
  have hfi : fO ≫ b = iO ≫ pullHom π T := by
    ext
    simp only [fO, iO, Over.comp_left, Over.homMk_left, pullHom_left]
    exact pullback.condition
  have hpt : pt e QO (k₀ ≫ j) (by rw [Category.assoc]; exact hk₀) =
      pt e QO (pullback.snd b.left (pullback.fst T.hom π) ≫ v')
        (by rw [Category.assoc, ← Category.assoc v', hv'q]; rfl) := by
    have hfac : (Over.homMk (k₀ ≫ p) (comp_p_w (T := QO) j hpb k₀ hk₀) : QO ⟶ Over.mk w) =
        fO ≫ u₀ := by
      ext
      simp only [fO, Over.comp_left, Over.homMk_left]
      exact hk₀p
    rw [pt_comp_chart e j hpb hξ (T := QO) k₀ hk₀, hfac, ← map_map, hv, map_map, hfi,
      ← map_map, ← hv', pt_comp]
    rfl
  have hji : k₀ ≫ j = pullback.snd b.left (pullback.fst T.hom π) ≫ v' :=
    pt_inj e (T := QO) _ _ (by rw [Category.assoc, hk₀q, Category.assoc, hv'q]) hpt
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, rfl⟩ := hsurj.surj x
  exact ⟨k₀ y, by rw [← Scheme.Hom.comp_apply, hji, Scheme.Hom.comp_apply]⟩

include hσ hσpt hfst in
/-- `ξ : V → F` is infinitesimally étale at every point. -/
theorem infinitesimallyEtaleAt_of_isChartElement (hF : FaithfullyFlatSheaf F) [Flat π]
    [Surjective π] [QuasiCompact π] {ξ : F.obj (op (Over.mk w))} (hξ : IsChartElement e j hpb ξ)
    (y : V) : InfinitesimallyEtaleAt F ξ y := by
  intro A _ _ _ f J hJ u₀ _ v hv
  refine existsUnique_of_exists_of_unique ?_ ?_
  · have hb : Function.Surjective (algebraOverBase f (A ⧸ J)).left := by
      have hle : J ≤ nilradical A := by
        obtain ⟨n, hn⟩ := hJ
        intro x hx
        exact mem_nilradical.2 ⟨n, by simpa [hn] using Ideal.pow_mem_pow hx n⟩
      exact (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hle).2
    obtain ⟨v', hv'q, hv'⟩ := exists_pt e (pullOver π (Over.mk f)) (pullback.snd _ _) rfl
      (F.map (pullHom π (Over.mk f)).op v)
    have hr := range_subset_of_map_eq e j hpb hξ (algebraOverBase f (A ⧸ J)) hb u₀ v hv v'
      hv'q hv'
    obtain ⟨h, hh⟩ := exists_map_eq_of_range_subset e hσ hσpt j hsat hpb hfst hF hξ
      (Over.mk f) v v' hv'q hv' hr
    refine ⟨h, isMonoElement_of_isChartElement e j hpb hξ _ _ ?_, hh⟩
    rw [← map_map, hh, hv]
  · rintro h₁ h₂ ⟨-, hh₁⟩ ⟨-, hh₂⟩
    exact isMonoElement_of_isChartElement e j hpb hξ _ _ (hh₁.trans hh₂.symm)

include hpb in
/-- The descended scheme `V` is locally of finite type over `S`. -/
lemma locallyOfFiniteType_w [LocallyOfFiniteType q'] [Flat π] [Surjective π]
    [QuasiCompact π] : LocallyOfFiniteType w :=
  MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpb.flip ⟨⟨inferInstance, inferInstance⟩,
      inferInstance⟩ inferInstance

end Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent
