import Langlands.AlgebraicGeometry.NoetherianApproximation.FractionFieldTwoComparisonLineBundleModel
import Langlands.AlgebraicGeometry.Picard.CartesianSelfProduct
import Langlands.AlgebraicGeometry.Picard.AbelianSchemeNoetherianModelProof
import Langlands.AbelianScheme.SubalgebraDescentProof

/-! # Normal finite-ring models of actual two-axis-trivial generic bundles -/

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.NoetherianApproximation
open Langlands.Scheme.Modules TwoComparisonDescent

/-- Both actual unit axes are morphisms over the ground scheme. -/
theorem twoAxisFirst_over {S : Scheme.{u}} (A : AbelianScheme S) :
    mumfordSection A ≫ (mumfordProduct A).hom = A.X.hom := by
  change mumfordSection A ≫ (pullback.fst A.X.hom A.X.hom ≫ A.X.hom) = A.X.hom
  simp only [mumfordSection, relativeSection,
    pullback.lift_fst_assoc, Category.id_comp]

theorem twoAxisSecond_over {S : Scheme.{u}} (A : AbelianScheme S) :
    twoAxisSecond A ≫ (mumfordProduct A).hom = A.X.hom := by
  change twoAxisSecond A ≫ (pullback.fst A.X.hom A.X.hom ≫ A.X.hom) = A.X.hom
  simp only [twoAxisSecond, pullback.lift_fst_assoc]
  rw [Category.assoc, unitSection_comp, Category.comp_id]

/-- A normal finite ring model includes the actual generic bundle and its
chosen-field comparison, with triviality on both actual unit axes. -/
structure TwoAxisNormalModel
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (A : AbelianScheme (Spec (CommRingCat.of R)))
    (D : LineBundle (mumfordProduct ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A)).left) where
  T : Subalgebra ℤ R
  fg : T.FG
  normal : IsIntegrallyClosed ↥T
  noetherian : IsNoetherianRing ↥T
  model : AbelianScheme (Spec (CommRingCat.of T))
  totalMap : A.X.left ⟶ model.X.left
  totalPullback : IsPullback totalMap A.X.hom model.X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap T R)))
  totalUnit : unitSection A ≫ totalMap =
    Spec.map (CommRingCat.ofHom (algebraMap T R)) ≫ unitSection model
  genericMap : ((baseChange (Spec.map (CommRingCat.ofHom
      (algebraMap R K)))).obj A).X.left ⟶
    ((baseChange (Spec.map (CommRingCat.ofHom
      (algebraMap T (FractionRing T))))).obj model).X.left
  genericFst : genericMap ≫ pullback.fst model.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T)))) =
    pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ totalMap
  genericSnd : genericMap ≫
      ((baseChange (Spec.map (CommRingCat.ofHom
        (algebraMap T (FractionRing T))))).obj model).X.hom =
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A).X.hom ≫
      Spec.map (CommRingCat.ofHom (stageFractionFieldMap R K T))
  genericPullback : IsPullback genericMap
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A).X.hom
    ((baseChange (Spec.map (CommRingCat.ofHom
      (algebraMap T (FractionRing T))))).obj model).X.hom
    (Spec.map (CommRingCat.ofHom (stageFractionFieldMap R K T)))
  genericUnit : unitSection ((baseChange (Spec.map (CommRingCat.ofHom
      (algebraMap R K)))).obj A) ≫ genericMap =
    Spec.map (CommRingCat.ofHom (stageFractionFieldMap R K T)) ≫
      unitSection ((baseChange (Spec.map (CommRingCat.ofHom
        (algebraMap T (FractionRing T))))).obj model)
  bundle : LineBundle (mumfordProduct ((baseChange (Spec.map (CommRingCat.ofHom
    (algebraMap T (FractionRing T))))).obj model)).left
  first : Nonempty ((Scheme.Modules.pullback (mumfordSection ((baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T))))).obj model))).obj
      bundle.obj ≅ structureSheaf _)
  second : Nonempty ((Scheme.Modules.pullback (twoAxisSecond ((baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T))))).obj model))).obj
      bundle.obj ≅ structureSheaf _)
  comparison : Nonempty ((Scheme.Modules.pullback (cartesianMumfordProductMap
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A)
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T))))).obj model)
    genericMap (Spec.map (CommRingCat.ofHom (stageFractionFieldMap R K T)))
    genericSnd)).obj bundle.obj ≅ D.obj)

/-- Under explicit normal-stage existence, actual two-axis-trivial generic
bundles admit normal finite ring models. -/
theorem exists_twoAxisNormalModel
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsIntegrallyClosed R]
    (hNormal : NormalFiniteTypeSubalgebraStatement.{u})
    (A : AbelianScheme (Spec (CommRingCat.of R)))
    (D : LineBundle (mumfordProduct ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A)).left)
    (e₁ : Nonempty ((Scheme.Modules.pullback (mumfordSection ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A))).obj D.obj ≅
        structureSheaf _))
    (e₂ : Nonempty ((Scheme.Modules.pullback (twoAxisSecond ((baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A))).obj D.obj ≅
        structureSheaf _)) (s : Finset R) :
    ∃ M : TwoAxisNormalModel A D, (↑s : Set R) ⊆ M.T := by
  obtain ⟨C, hC, A₀, ⟨eA⟩⟩ := subalgebraDescent (CommRingCat.of R) A
  let S := NoetherianModelProof.stage₀ C hC A₀ eA
  have hSunit : unitSection A ≫ S.a =
      Spec.map (CommRingCat.ofHom (algebraMap C R)) ≫ unitSection A₀ := S.unit
  let bR := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let G := (baseChange bR).obj A
  let : Algebra C K := ((algebraMap R K).comp C.val.toRingHom).toAlgebra
  have hCK : algebraMap C K = (algebraMap R K).comp C.val.toRingHom := rfl
  let βK := Spec.map (CommRingCat.ofHom (algebraMap C K))
  let aK := pullback.fst A.X.hom bR ≫ S.a
  have hbR : bR ≫ Spec.map (CommRingCat.ofHom (algebraMap C R)) = βK := by
    dsimp only [bR, βK]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hK : IsPullback aK G.X.hom A₀.X.hom βK := by
    have h := (IsPullback.of_hasPullback A.X.hom bR).paste_horiz S.isPullback
    change IsPullback aK G.X.hom A₀.X.hom
      (bR ≫ Spec.map (CommRingCat.ofHom (algebraMap C R))) at h
    rw [hbR] at h
    exact h
  have huK : unitSection G ≫ aK = βK ≫ unitSection A₀ := by
    dsimp only [aK]
    rw [← Category.assoc, unitSection_baseChange_fst, Category.assoc, hSunit,
      ← Category.assoc, hbR]
  let aP := cartesianMumfordProductMap G A₀ aK βK hK.w
  have hP : IsPullback aP (mumfordProduct G).hom (mumfordProduct A₀).hom βK :=
    cartesianSelfProductMap_isPullback G.X.hom A₀.X.hom aK βK hK.w hK
  have : IsProper (mumfordProduct A₀).hom := by
    change IsProper (pullback.fst A₀.X.hom A₀.X.hom ≫ A₀.X.hom)
    infer_instance
  obtain ⟨F, hs⟩ := exists_fractionFieldTwoComparisonLineBundleModel hNormal C hC hCK
    (mumfordProduct A₀).hom A₀.X.hom (mumfordSection A₀) (twoAxisSecond A₀)
    (twoAxisFirst_over A₀) (twoAxisSecond_over A₀)
    aP (mumfordProduct G).hom aK G.X.hom hP hK
    (mumfordSection G) (twoAxisSecond G)
    (mumfordSection_cartesianMumfordProductMap G A₀ aK βK hK.w huK)
    (twoAxisSecond_cartesianMumfordProductMap G A₀ aK βK hK.w huK)
    (twoAxisFirst_over G) (twoAxisSecond_over G) D e₁ e₂ s
  let T := F.T
  let βT := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion F.contains).toRingHom)
  let bT := Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T)))
  let δR := Spec.map (CommRingCat.ofHom (algebraMap T R))
  let βF := Spec.map (CommRingCat.ofHom (fractionFieldStageBaseMap R C T F.contains))
  let κ := Spec.map (CommRingCat.ofHom (stageFractionFieldMap R K T))
  have hbT : bT ≫ βT = βF := by
    dsimp only [bT, βT, βF, fractionFieldStageBaseMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hδR : δR ≫ βT = Spec.map (CommRingCat.ofHom (algebraMap C R)) := by
    dsimp only [δR, βT]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hκ : κ ≫ βF = βK := by
    dsimp only [κ, βF, βK]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      stageFractionFieldMap_comp_baseMap, ← hCK]
  have hκT : κ ≫ bT = bR ≫ δR := by
    dsimp only [κ, bT, bR, δR]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext t
    exact stageFractionFieldMap_algebraMap R K T t
  let B := (baseChange βT).obj A₀
  let H := (baseChange bT).obj B
  have hwR : S.a ≫ A₀.X.hom = A.X.hom ≫ δR ≫ βT := by
    rw [hδR]
    exact S.isPullback.w
  let aR := comparison S.a A.X.hom A₀.X.hom βT δR hwR
  have haR₁ : aR ≫ pullback.fst A₀.X.hom βT = S.a := comparison_fst ..
  have haR₂ : aR ≫ B.X.hom = A.X.hom ≫ δR := comparison_snd ..
  have haR : IsPullback aR A.X.hom B.X.hom δR := by
    apply comparison_isPullback
    rw [hδR]
    exact S.isPullback
  have huR : unitSection A ≫ aR = δR ≫ unitSection B := by
    apply pullback.hom_ext
    · rw [Category.assoc, haR₁, hSunit, Category.assoc,
        unitSection_baseChange_fst, ← Category.assoc, hδR]
    · change (unitSection A ≫ aR) ≫ B.X.hom =
        (δR ≫ unitSection B) ≫ B.X.hom
      rw [Category.assoc, haR₂, ← Category.assoc, unitSection_comp,
        Category.id_comp, Category.assoc, unitSection_comp, Category.comp_id]
  let aF := pullback.fst B.X.hom bT ≫ pullback.fst A₀.X.hom βT
  have hF : IsPullback aF H.X.hom A₀.X.hom βF := by
    have h := (IsPullback.of_hasPullback B.X.hom bT).paste_horiz
      (IsPullback.of_hasPullback A₀.X.hom βT)
    rw [hbT] at h
    exact h
  have huF : unitSection H ≫ aF = βF ≫ unitSection A₀ := by
    dsimp only [aF]
    rw [← Category.assoc, unitSection_baseChange_fst, Category.assoc,
      unitSection_baseChange_fst, ← Category.assoc, hbT]
  have hwK : aK ≫ A₀.X.hom = (G.X.hom ≫ κ) ≫ βF := by
    calc
      aK ≫ A₀.X.hom = G.X.hom ≫ βK := hK.w
      _ = (G.X.hom ≫ κ) ≫ βF := by rw [Category.assoc, hκ]
  let c := hF.lift aK (G.X.hom ≫ κ) hwK
  have hc₁ : c ≫ aF = aK := hF.lift_fst ..
  have hc₂ : c ≫ H.X.hom = G.X.hom ≫ κ := hF.lift_snd ..
  have hc : IsPullback c G.X.hom H.X.hom κ := by
    refine IsPullback.of_right (h₁₂ := aF) (v₁₃ := A₀.X.hom)
      (h₂₂ := βF) ?_ hc₂ hF
    rw [hc₁, hκ]
    exact hK
  have huc : unitSection G ≫ c = κ ≫ unitSection H := by
    apply hF.hom_ext
    · rw [Category.assoc, hc₁, huK, Category.assoc, huF,
        ← Category.assoc, hκ]
    · rw [Category.assoc, hc₂, ← Category.assoc, unitSection_comp,
        Category.id_comp, Category.assoc, unitSection_comp, Category.comp_id]
  have hcR : c ≫ pullback.fst B.X.hom bT = pullback.fst A.X.hom bR ≫ aR := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      change c ≫ aF = _
      rw [hc₁, Category.assoc, haR₁]
    · change (c ≫ pullback.fst B.X.hom bT) ≫ B.X.hom =
        (pullback.fst A.X.hom bR ≫ aR) ≫ B.X.hom
      calc
        (c ≫ pullback.fst B.X.hom bT) ≫ B.X.hom =
            (c ≫ H.X.hom) ≫ bT := by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
          rfl
        _ = (G.X.hom ≫ κ) ≫ bT := congrArg (fun k => k ≫ bT) hc₂
        _ = (pullback.fst A.X.hom bR ≫ A.X.hom) ≫ δR := by
          change (pullback.snd A.X.hom bR ≫ κ) ≫ bT = _
          rw [Category.assoc, hκT, ← Category.assoc, ← pullback.condition]
        _ = (pullback.fst A.X.hom bR ≫ aR) ≫ B.X.hom := by
          simp only [Category.assoc, haR₂]
  let qF := cartesianMumfordProductMap H A₀ aF βF hF.w
  have hPF : IsPullback qF (mumfordProduct H).hom (mumfordProduct A₀).hom βF :=
    cartesianSelfProductMap_isPullback H.X.hom A₀.X.hom aF βF hF.w hF
  let φ := hPF.isoPullback
  let ψ := hF.isoPullback
  let N : LineBundle (mumfordProduct H).left :=
    (LineBundle.pullback φ.hom).obj F.bundle
  have haxis (g₀ : A₀.X.left ⟶ (mumfordProduct A₀).left)
      (wg₀ : g₀ ≫ (mumfordProduct A₀).hom = A₀.X.hom)
      (g : H.X.left ⟶ (mumfordProduct H).left)
      (wg : g ≫ (mumfordProduct H).hom = H.X.hom)
      (hg : g ≫ qF = aF ≫ g₀) :
      g ≫ φ.hom = ψ.hom ≫ overMap (mumfordProduct A₀).hom A₀.X.hom g₀ wg₀ βF := by
    apply pullback.hom_ext
    · simp only [Category.assoc, φ, ψ, IsPullback.isoPullback_hom_fst,
        overMap_fst, IsPullback.isoPullback_hom_fst_assoc]
      exact hg
    · simp only [Category.assoc, φ, ψ, IsPullback.isoPullback_hom_snd, overMap_snd]
      exact wg
  have htriv (g₀ : A₀.X.left ⟶ (mumfordProduct A₀).left)
      (wg₀ : g₀ ≫ (mumfordProduct A₀).hom = A₀.X.hom)
      (g : H.X.left ⟶ (mumfordProduct H).left)
      (wg : g ≫ (mumfordProduct H).hom = H.X.hom)
      (hg : g ≫ qF = aF ≫ g₀)
      (e : Nonempty ((Scheme.Modules.pullback (overMap
        (mumfordProduct A₀).hom A₀.X.hom g₀ wg₀ βF)).obj F.bundle.obj ≅
          structureSheaf _)) :
      Nonempty ((Scheme.Modules.pullback g).obj N.obj ≅ structureSheaf _) := by
    obtain ⟨e⟩ := e
    exact ⟨(Scheme.Modules.pullbackComp g φ.hom).app F.bundle.obj ≪≫
      (Scheme.Modules.pullbackCongr (haxis g₀ wg₀ g wg hg)).app F.bundle.obj ≪≫
      ((Scheme.Modules.pullbackComp ψ.hom (overMap
        (mumfordProduct A₀).hom A₀.X.hom g₀ wg₀ βF)).app F.bundle.obj).symm ≪≫
      (Scheme.Modules.pullback ψ.hom).mapIso e ≪≫ pullbackUnitIso ψ.hom⟩
  have hfirst := htriv (mumfordSection A₀) (twoAxisFirst_over A₀)
    (mumfordSection H) (twoAxisFirst_over H)
    (mumfordSection_cartesianMumfordProductMap H A₀ aF βF hF.w huF) F.first
  have hsecond := htriv (twoAxisSecond A₀) (twoAxisSecond_over A₀)
    (twoAxisSecond H) (twoAxisSecond_over H)
    (twoAxisSecond_cartesianMumfordProductMap H A₀ aF βF hF.w huF) F.second
  let q := cartesianMumfordProductMap G H c κ hc₂
  have hqφ : q ≫ φ.hom = F.map := by
    apply pullback.hom_ext
    · rw [Category.assoc, show φ.hom ≫ pullback.fst _ _ = qF from hPF.isoPullback_hom_fst,
        F.fst]
      apply pullback.hom_ext <;>
        simp only [q, qF, aP, cartesianMumfordProductMap, Category.assoc,
          cartesianSelfProductMap_fst, cartesianSelfProductMap_snd,
          cartesianSelfProductMap_fst_assoc, cartesianSelfProductMap_snd_assoc, hc₁]
    · rw [Category.assoc, show φ.hom ≫ pullback.snd _ _ =
        (mumfordProduct H).hom from hPF.isoPullback_hom_snd, F.snd]
      change q ≫ (pullback.fst H.X.hom H.X.hom ≫ H.X.hom) = _
      rw [← Category.assoc, show q ≫ pullback.fst H.X.hom H.X.hom =
        pullback.fst G.X.hom G.X.hom ≫ c from
        cartesianSelfProductMap_fst G.X.hom H.X.hom c κ hc₂,
        Category.assoc, hc₂, ← Category.assoc]
      rfl
  obtain ⟨e⟩ := F.comparison
  have hcomp : Nonempty ((Scheme.Modules.pullback q).obj N.obj ≅ D.obj) :=
    ⟨(Scheme.Modules.pullbackComp q φ.hom).app F.bundle.obj ≪≫
      (Scheme.Modules.pullbackCongr hqφ).app F.bundle.obj ≪≫ e⟩
  exact ⟨⟨T, F.fg, F.normal, F.noetherian, B, aR, haR, huR,
    c, hcR, hc₂, hc, huc, N, hfirst, hsecond, hcomp⟩, hs⟩

end Langlands.AbelianScheme
