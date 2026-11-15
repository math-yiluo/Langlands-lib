import Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.Points
import Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.QuasiAffine

/-! # The descent datum on a saturated open of `X'`

Let `π : S' ⟶ S` and let `q' : X' ⟶ S'` represent the base change of `F` along `π`. Let
`σ : X' ×_S S' ⟶ X'` be a morphism over the second projection whose element of `F` is that
of the first projection (`exists_sigma`). An open immersion `j : W ⟶ X'` whose image is
saturated for `σ` (it contains `σ(z)` whenever it contains the first projection of `z`)
inherits a descent datum `σW : W ×_S S' ⟶ W`: it has the diagonal as a section and
satisfies the cocycle identity. When `π` is a flat surjective morphism of affine schemes and
`W` is quasi-affine, `W` is therefore the base change of a scheme over `S`. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent

variable {S S' : Scheme.{u}} {π : S' ⟶ S} {F : (Over S)ᵒᵖ ⥤ Type v} {X' : Scheme.{u}}
  {q' : X' ⟶ S'} (e : (baseChange π F).RepresentableBy (Over.mk q'))
  {σ : pullback (q' ≫ π) π ⟶ X'} (hσ : σ ≫ q' = pullback.snd _ _)


lemma sigma_comp_eq (hσ : σ ≫ q' = pullback.snd _ _) : σ ≫ q' ≫ π = (prodOver q' π).hom := by
  rw [← Category.assoc, hσ]
  rfl

/-- `σ` and the first projection define the same element of `F` after any base change. -/
lemma pt_sigma
    (hσpt : pt e (prodOver q' π) σ (sigma_comp_eq hσ) =
      pt e (prodOver q' π) (pullback.fst _ _) (fst_comp_eq q' π))
    (T : Over S) (κ : T.left ⟶ pullback (q' ≫ π) π) (hκ : κ ≫ pullback.snd _ _ ≫ π = T.hom) :
    pt e T (κ ≫ σ) (by rw [Category.assoc, sigma_comp_eq hσ]; exact hκ) =
      pt e T (κ ≫ pullback.fst _ _) (by rw [Category.assoc, fst_comp_eq]; exact hκ) := by
  let f : T ⟶ prodOver q' π := Over.homMk κ hκ
  exact (pt_comp e f σ _).symm.trans ((congrArg (F.map f.op) hσpt).trans (pt_comp e f _ _))

variable {W : Scheme.{u}} (j : W ⟶ X')

/-- The morphism `W ×_S S' ⟶ X' ×_S S'` induced by `j`. -/
def chartPullMap : pullback ((j ≫ q') ≫ π) π ⟶ pullback (q' ≫ π) π :=
  pullback.lift (pullback.fst _ _ ≫ j) (pullback.snd _ _) (by
    simpa using pullback.condition (f := (j ≫ q') ≫ π) (g := π))

@[reassoc (attr := simp)]
lemma chartPullMap_fst : chartPullMap j ≫ pullback.fst (q' ≫ π) π = pullback.fst _ _ ≫ j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma chartPullMap_snd : chartPullMap j ≫ pullback.snd (q' ≫ π) π = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

variable [IsOpenImmersion j]
  (hsat : ∀ z, pullback.fst (q' ≫ π) π z ∈ Set.range j → σ z ∈ Set.range j)

omit [IsOpenImmersion j] in
lemma range_chartPullMap_sigma
    (hsat : ∀ z, pullback.fst (q' ≫ π) π z ∈ Set.range j → σ z ∈ Set.range j) :
    Set.range (chartPullMap j ≫ σ) ⊆ Set.range j := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Hom.comp_apply]
  apply hsat
  rw [← Scheme.Hom.comp_apply, chartPullMap_fst, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

/-- The descent datum `σW : W ×_S S' ⟶ W` on a saturated open `W` of `X'`. -/
def chartSigma : pullback ((j ≫ q') ≫ π) π ⟶ W :=
  IsOpenImmersion.lift j (chartPullMap j ≫ σ) (range_chartPullMap_sigma j hsat)

@[reassoc (attr := simp)]
lemma chartSigma_j : chartSigma j hsat ≫ j = chartPullMap j ≫ σ :=
  IsOpenImmersion.lift_fac _ _ _

include hσ in
lemma chartSigma_comp : chartSigma j hsat ≫ (j ≫ q') = pullback.snd _ _ := by
  rw [← Category.assoc, chartSigma_j, Category.assoc (chartPullMap j), hσ, chartPullMap_snd]

omit [IsOpenImmersion j] in
lemma chart_fst_comp :
    pullback.fst ((j ≫ q') ≫ π) π ≫ j ≫ q' ≫ π = pullback.snd ((j ≫ q') ≫ π) π ≫ π := by
  simpa using pullback.condition (f := (j ≫ q') ≫ π) (g := π)

include hσ in
/-- The element of `F` defined by `σW` is the one defined by the first projection. -/
lemma pt_chartSigma
    (hσpt : pt e (prodOver q' π) σ (sigma_comp_eq hσ) =
      pt e (prodOver q' π) (pullback.fst _ _) (fst_comp_eq q' π))
    (T : Over S) (κ : T.left ⟶ pullback ((j ≫ q') ≫ π) π)
    (hκ : κ ≫ pullback.snd _ _ ≫ π = T.hom) :
    pt e T (κ ≫ chartSigma j hsat ≫ j) (by
      simp only [Category.assoc, chartSigma_j_assoc, reassoc_of% hσ, chartPullMap_snd_assoc]
      exact hκ) =
      pt e T (κ ≫ pullback.fst _ _ ≫ j) (by
        simp only [Category.assoc, chart_fst_comp]
        exact hκ) := by
  have h₁ := pt_sigma e hσ hσpt T (κ ≫ chartPullMap j) (by simpa using hκ)
  refine (pt_congr e (by simp) _ _).trans (h₁.trans (pt_congr e (by simp) _ _))

include hσ in
lemma chartSigma_section
    (hσpt : pt e (prodOver q' π) σ (sigma_comp_eq hσ) =
      pt e (prodOver q' π) (pullback.fst _ _) (fst_comp_eq q' π)) :
    pullback.lift (𝟙 W) (j ≫ q') (by simp) ≫ chartSigma j hsat = 𝟙 W := by
  rw [← cancel_mono j, Category.assoc, Category.id_comp j]
  let T : Over S := Over.mk (j ≫ q' ≫ π)
  let δ : W ⟶ pullback ((j ≫ q') ≫ π) π := pullback.lift (𝟙 W) (j ≫ q') (by simp)
  have hδ : δ ≫ pullback.snd _ _ ≫ π = T.hom := by
    simp only [δ, T, pullback.lift_snd_assoc, Over.mk_hom, Category.assoc]
  have hk := (pt_chartSigma e hσ j hsat hσpt T δ hδ).trans
    (pt_congr e (b := j) (by simp only [δ, pullback.lift_fst_assoc]; exact Category.id_comp j) _ rfl)
  exact pt_inj e _ _ (by simp only [δ, Category.assoc, chartSigma_j_assoc, hσ,
    chartPullMap_snd, pullback.lift_snd]) hk

include hσ in
lemma chartSigma_cocycle
    (hσpt : pt e (prodOver q' π) σ (sigma_comp_eq hσ) =
      pt e (prodOver q' π) (pullback.fst _ _) (fst_comp_eq q' π)) :
    firstLift π (j ≫ q') ≫ chartSigma j hsat =
      secondLift π (j ≫ q') (chartSigma j hsat) (chartSigma_comp hσ j hsat) ≫
        chartSigma j hsat := by
  rw [← cancel_mono j]
  simp only [Category.assoc]
  let T : Over S :=
    Over.mk (pullback.snd (pullback.snd ((j ≫ q') ≫ π) π ≫ π) π ≫ π)
  have h₁ : firstLift π (j ≫ q') ≫ pullback.snd ((j ≫ q') ≫ π) π ≫ π = T.hom := by
    simp only [firstLift_snd_assoc, T, Over.mk_hom]
  have h₂ : secondLift π (j ≫ q') (chartSigma j hsat) (chartSigma_comp hσ j hsat) ≫
      pullback.snd ((j ≫ q') ≫ π) π ≫ π = T.hom := by
    simp only [secondLift_snd_assoc, T, Over.mk_hom]
  have h₃ : pullback.fst (pullback.snd ((j ≫ q') ≫ π) π ≫ π) π ≫
      pullback.snd ((j ≫ q') ≫ π) π ≫ π = T.hom := by
    simp only [T, Over.mk_hom]
    exact pullback.condition
  have k₁ := pt_chartSigma e hσ j hsat hσpt T (firstLift π (j ≫ q')) h₁
  have k₂ := pt_chartSigma e hσ j hsat hσpt T
    (secondLift π (j ≫ q') (chartSigma j hsat) (chartSigma_comp hσ j hsat)) h₂
  have k₃ := pt_chartSigma e hσ j hsat hσpt T
    (pullback.fst (pullback.snd ((j ≫ q') ≫ π) π ≫ π) π) h₃
  have hk := k₁.trans ((pt_congr e (by rw [firstLift_fst_assoc]) _ _).trans
    (k₃.symm.trans ((pt_congr e (by rw [secondLift_fst_assoc]) _ _).trans k₂.symm)))
  exact pt_inj e _ _ (by simp only [Category.assoc, chartSigma_comp hσ j hsat, firstLift_snd,
    secondLift_snd]) hk

/-- A saturated quasi-affine open `W` of `X'` is the base change of a scheme `V` over `S`, by a
morphism `p : W ⟶ V` which identifies the first projection with `σW`. -/
theorem exists_chart_isPullback [IsAffine S] [IsAffine S'] [Flat π] [Surjective π]
    [W.IsQuasiAffine]
    (hσpt : pt e (prodOver q' π) σ (sigma_comp_eq hσ) =
      pt e (prodOver q' π) (pullback.fst _ _) (fst_comp_eq q' π)) :
    ∃ (V : Scheme.{u}) (w : V ⟶ S) (p : W ⟶ V), IsPullback p (j ≫ q') w π ∧
      pullback.fst ((j ≫ q') ≫ π) π ≫ p = chartSigma j hsat ≫ p :=
  exists_isPullback_of_isQuasiAffine π (j ≫ q') (chartSigma j hsat)
    (chartSigma_comp hσ j hsat) (chartSigma_section e hσ j hsat hσpt)
    (chartSigma_cocycle e hσ j hsat hσpt)

end Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent
