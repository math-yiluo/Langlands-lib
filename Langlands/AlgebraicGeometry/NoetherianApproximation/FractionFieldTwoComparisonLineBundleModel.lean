import Langlands.AlgebraicGeometry.NoetherianApproximation.TwoComparisonLineBundleDescent
import Langlands.AlgebraicGeometry.NoetherianApproximation.GenericLineBundleFractionFieldModel

/-! # Fraction-field models preserving two trivial restrictions -/

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules TwoComparisonDescent

/-- An actual bundle over a normal stage's fraction field, with two trivial
restrictions and comparison to the original chosen-field bundle. -/
structure FractionFieldTwoComparisonLineBundleModel
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (C : Subalgebra ℤ R)
    {X₀ Y₀ : Scheme.{u}} (fX₀ : X₀ ⟶ Spec (CommRingCat.of C))
    (fY₀ : Y₀ ⟶ Spec (CommRingCat.of C)) (g₁ g₂ : Y₀ ⟶ X₀)
    (w₁ : g₁ ≫ fX₀ = fY₀) (w₂ : g₂ ≫ fX₀ = fY₀)
    {X : Scheme.{u}} (aX : X ⟶ X₀) (fX : X ⟶ Spec (CommRingCat.of K))
    (M : LineBundle X) where
  T : Subalgebra ℤ R
  contains : C ≤ T
  fg : T.FG
  normal : IsIntegrallyClosed ↥T
  noetherian : IsNoetherianRing ↥T
  bundle : LineBundle (pullback fX₀
    (Spec.map (CommRingCat.ofHom (fractionFieldStageBaseMap R C T contains))))
  first : Nonempty ((Scheme.Modules.pullback (overMap fX₀ fY₀ g₁ w₁
    (Spec.map (CommRingCat.ofHom (fractionFieldStageBaseMap R C T contains))))).obj
      bundle.obj ≅ structureSheaf _)
  second : Nonempty ((Scheme.Modules.pullback (overMap fX₀ fY₀ g₂ w₂
    (Spec.map (CommRingCat.ofHom (fractionFieldStageBaseMap R C T contains))))).obj
      bundle.obj ≅ structureSheaf _)
  map : X ⟶ pullback fX₀
    (Spec.map (CommRingCat.ofHom (fractionFieldStageBaseMap R C T contains)))
  fst : map ≫ pullback.fst _ _ = aX
  snd : map ≫ pullback.snd _ _ =
    fX ≫ Spec.map (CommRingCat.ofHom (stageFractionFieldMap R K T))
  isPullback : IsPullback map fX (pullback.snd _ _)
    (Spec.map (CommRingCat.ofHom (stageFractionFieldMap R K T)))
  comparison : Nonempty ((Scheme.Modules.pullback map).obj bundle.obj ≅ M.obj)

/-- Two trivial restrictions of an actual generic bundle can be modeled over the
fraction field of a normal finite ring stage. Normal-stage existence is explicit. -/
theorem exists_fractionFieldTwoComparisonLineBundleModel
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsIntegrallyClosed R]
    (hNormal : NormalFiniteTypeSubalgebraStatement.{u})
    (C : Subalgebra ℤ R) (hC : C.FG) [Algebra C K]
    (hCK : algebraMap C K = (algebraMap R K).comp C.val.toRingHom)
    {X₀ Y₀ : Scheme.{u}} (fX₀ : X₀ ⟶ Spec (CommRingCat.of C))
    (fY₀ : Y₀ ⟶ Spec (CommRingCat.of C))
    [QuasiCompact fX₀] [QuasiSeparated fX₀]
    [QuasiCompact fY₀] [QuasiSeparated fY₀]
    (g₁ g₂ : Y₀ ⟶ X₀) (w₁ : g₁ ≫ fX₀ = fY₀) (w₂ : g₂ ≫ fX₀ = fY₀)
    {X Y : Scheme.{u}} (aX : X ⟶ X₀) (fX : X ⟶ Spec (CommRingCat.of K))
    (aY : Y ⟶ Y₀) (fY : Y ⟶ Spec (CommRingCat.of K))
    (hX : IsPullback aX fX fX₀ (Spec.map (CommRingCat.ofHom (algebraMap C K))))
    (hY : IsPullback aY fY fY₀ (Spec.map (CommRingCat.ofHom (algebraMap C K))))
    (t₁ t₂ : Y ⟶ X)
    (ht₁ : t₁ ≫ aX = aY ≫ g₁) (ht₂ : t₂ ≫ aX = aY ≫ g₂)
    (hf₁ : t₁ ≫ fX = fY) (hf₂ : t₂ ≫ fX = fY)
    (M : LineBundle X)
    (e₁ : Nonempty ((Scheme.Modules.pullback t₁).obj M.obj ≅ structureSheaf Y))
    (e₂ : Nonempty ((Scheme.Modules.pullback t₂).obj M.obj ≅ structureSheaf Y))
    (sR : Finset R) :
    ∃ S : FractionFieldTwoComparisonLineBundleModel C fX₀ fY₀ g₁ g₂ w₁ w₂ aX fX M,
      (↑sR : Set R) ⊆ S.T := by
  obtain ⟨B, _⟩ := exists_twoComparisonLineBundleModel fX₀ fY₀ g₁ g₂ w₁ w₂
    aX fX aY fY hX hY t₁ t₂ ht₁ ht₂ hf₁ hf₂ M e₁ e₂ ∅
  obtain ⟨T, hCT, hT, hsR, hn, hnoeth, j, _, hj, hjC⟩ :=
    exists_normal_fractionFieldFactor_over hNormal C hC hCK sR B.T B.fg
  let βB := Spec.map (CommRingCat.ofHom (algebraMap C B.T))
  let βT := Spec.map (CommRingCat.ofHom (fractionFieldStageBaseMap R C T hCT))
  let θ := Spec.map (CommRingCat.ofHom j)
  let κ := Spec.map (CommRingCat.ofHom (stageFractionFieldMap R K T))
  have hθ : θ ≫ βB = βT := by
    dsimp only [θ, βB, βT]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hjC]
  have hκ : κ ≫ βT = Spec.map (CommRingCat.ofHom (algebraMap C K)) := by
    dsimp only [κ, βT]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      stageFractionFieldMap_comp_baseMap, ← hCK]
  have hκθ : κ ≫ θ = Spec.map (CommRingCat.ofHom (algebraMap B.T K)) := by
    dsimp only [κ, θ]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hj]
    rfl
  let pX := transition fX₀ βB βT θ hθ
  let pY := transition fY₀ βB βT θ hθ
  let N : LineBundle (pullback fX₀ βT) :=
    ⟨(Scheme.Modules.pullback pX).obj B.bundle.obj, B.bundle.property.pullback pX⟩
  have htriv (g : Y₀ ⟶ X₀) (wg : g ≫ fX₀ = fY₀)
      (e : Nonempty ((Scheme.Modules.pullback (overMap fX₀ fY₀ g wg βB)).obj
        B.bundle.obj ≅ structureSheaf _)) :
      Nonempty ((Scheme.Modules.pullback (overMap fX₀ fY₀ g wg βT)).obj
        N.obj ≅ structureSheaf _) := by
    obtain ⟨e⟩ := e
    exact ⟨(Scheme.Modules.pullbackComp (overMap fX₀ fY₀ g wg βT) pX).app B.bundle.obj ≪≫
      (Scheme.Modules.pullbackCongr (overMap_transition fX₀ fY₀ g wg βB βT θ hθ)).app
        B.bundle.obj ≪≫
      ((Scheme.Modules.pullbackComp pY (overMap fX₀ fY₀ g wg βB)).app B.bundle.obj).symm ≪≫
      (Scheme.Modules.pullback pY).mapIso e ≪≫ pullbackUnitIso pY⟩
  have hw : aX ≫ fX₀ = fX ≫ κ ≫ βT := by rw [hκ]; exact hX.w
  let c := comparison aX fX fX₀ βT κ hw
  have hc₁ : c ≫ pullback.fst fX₀ βT = aX := comparison_fst ..
  have hc₂ : c ≫ pullback.snd fX₀ βT = fX ≫ κ := comparison_snd ..
  have hcPullback : IsPullback c fX (pullback.snd fX₀ βT) κ := by
    apply comparison_isPullback
    rw [hκ]
    exact hX
  have hcp₁ : (c ≫ pX) ≫ pullback.fst fX₀ βB = aX := by
    rw [Category.assoc, show pX ≫ pullback.fst fX₀ βB =
      pullback.fst fX₀ βT from transition_fst fX₀ βB βT θ hθ, hc₁]
  have hcp₂ : (c ≫ pX) ≫ pullback.snd fX₀ βB =
      fX ≫ Spec.map (CommRingCat.ofHom (algebraMap B.T K)) := by
    rw [Category.assoc, show pX ≫ pullback.snd fX₀ βB =
      pullback.snd fX₀ βT ≫ θ from transition_snd fX₀ βB βT θ hθ,
      ← Category.assoc, hc₂, Category.assoc, hκθ]
  obtain ⟨e⟩ := B.comparison (c ≫ pX) hcp₁ hcp₂
  exact ⟨⟨T, hCT, hT, hn, hnoeth, N, htriv g₁ w₁ B.first, htriv g₂ w₂ B.second,
    c, hc₁, hc₂, hcPullback, ⟨(Scheme.Modules.pullbackComp c pX).app B.bundle.obj ≪≫ e⟩⟩,
    hsR⟩

end Langlands.AlgebraicGeometry.NoetherianApproximation
