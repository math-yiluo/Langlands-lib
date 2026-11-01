import Langlands.AlgebraicGeometry.NoetherianApproximation.FiniteFractionFieldStages
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleSubalgebraDescentProof
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback

/-! # Actual generic line bundles over normal finite fraction-field stages -/

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

open Langlands.AlgebraicGeometry.Picard

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The base map from a contained integer subalgebra to a stage's fraction field. -/
def fractionFieldStageBaseMap (C T : Subalgebra ℤ R) (hCT : C ≤ T) :
    C →+* FractionRing T :=
  (algebraMap T (FractionRing T)).comp (Subalgebra.inclusion hCT).toRingHom

variable {R K}

/-- Finite field data can be placed over a prescribed finitely generated ring stage.
The factor map respects that base, as an equality of actual ring maps. -/
theorem exists_normal_fractionFieldFactor_over
    [IsIntegrallyClosed R]
    (hNormal : NormalFiniteTypeSubalgebraStatement.{u})
    (C : Subalgebra ℤ R) (hC : C.FG) [Algebra C K]
    (hCK : algebraMap C K = (algebraMap R K).comp C.val.toRingHom)
    (sR : Finset R) (B : Subalgebra C K) (hB : B.FG) :
    ∃ (T : Subalgebra ℤ R) (hCT : C ≤ T),
      T.FG ∧ (↑sR : Set R) ⊆ T ∧ IsIntegrallyClosed ↥T ∧ IsNoetherianRing ↥T ∧
      ∃ f : B →+* FractionRing T, Function.Injective f ∧
        (stageFractionFieldMap R K T).comp f = B.val.toRingHom ∧
        f.comp (algebraMap C B) = fractionFieldStageBaseMap R C T hCT := by
  classical
  let : SMul C K := (inferInstance : Algebra C K).toSMul
  have : IsScalarTower ℤ C K :=
    IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := C) (A := K) (Subsingleton.elim _ _)
  have hCft : Algebra.FiniteType ℤ C := (Subalgebra.fg_iff_finiteType _).1 hC
  have hBft : Algebra.FiniteType C B := (Subalgebra.fg_iff_finiteType _).1 hB
  have hBft' : Algebra.FiniteType ℤ B := Algebra.FiniteType.trans hCft hBft
  have hBfg : (B.restrictScalars ℤ).FG :=
    (Subalgebra.fg_iff_finiteType _).2 hBft'
  obtain ⟨sC, hsC⟩ := hC
  obtain ⟨T, hT, hs, hn, hnoeth, f, hf, hcomp⟩ :=
    exists_normal_fractionFieldFactor R K hNormal (sR ∪ sC) (B.restrictScalars ℤ) hBfg
  have hCT : C ≤ T := by
    rw [← hsC]
    exact Algebra.adjoin_le fun x hx => hs (Finset.mem_union_right sR hx)
  refine ⟨T, hCT, hT, fun x hx => hs (Finset.mem_union_left sC hx), hn, hnoeth,
    f, hf, hcomp, ?_⟩
  ext x
  apply stageFractionFieldMap_injective R K T
  have hx := RingHom.congr_fun hcomp (algebraMap C B x)
  change stageFractionFieldMap R K T (f (algebraMap C B x)) = algebraMap C K x at hx
  change stageFractionFieldMap R K T (f (algebraMap C B x)) =
    stageFractionFieldMap R K T
      (algebraMap T (FractionRing T) (Subalgebra.inclusion hCT x))
  rw [stageFractionFieldMap_algebraMap]
  exact hx.trans (RingHom.congr_fun hCK x)

/-- The fraction-field stage base map composes to the original chosen-field base map. -/
theorem stageFractionFieldMap_comp_baseMap
    (C T : Subalgebra ℤ R) (hCT : C ≤ T) :
    (stageFractionFieldMap R K T).comp (fractionFieldStageBaseMap R C T hCT) =
      (algebraMap R K).comp C.val.toRingHom := by
  ext x
  exact stageFractionFieldMap_algebraMap R K T (Subalgebra.inclusion hCT x)

/-- An actual generic line bundle has a model over the fraction field of a normal
finite ring stage. Normal-stage existence remains an explicit hypothesis. -/
theorem exists_normal_fractionField_lineBundle_model
    [IsIntegrallyClosed R]
    (hNormal : NormalFiniteTypeSubalgebraStatement.{u})
    (C : Subalgebra ℤ R) (hC : C.FG) [Algebra C K]
    (hCK : algebraMap C K = (algebraMap R K).comp C.val.toRingHom)
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of C))
    [QuasiCompact f₀] [QuasiSeparated f₀]
    {X : Scheme.{u}} (a : X ⟶ X₀) (f : X ⟶ Spec (CommRingCat.of K))
    (hpb : IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap C K))))
    (M : LineBundle X) (sR : Finset R) :
    ∃ (T : Subalgebra ℤ R) (hCT : C ≤ T),
      T.FG ∧ (↑sR : Set R) ⊆ T ∧ IsIntegrallyClosed ↥T ∧ IsNoetherianRing ↥T ∧
      ∃ (N : LineBundle (pullback f₀
          (Spec.map (CommRingCat.ofHom (fractionFieldStageBaseMap R C T hCT)))))
        (c : X ⟶ pullback f₀
          (Spec.map (CommRingCat.ofHom (fractionFieldStageBaseMap R C T hCT)))),
        c ≫ pullback.fst _ _ = a ∧
        c ≫ pullback.snd _ _ = f ≫ Spec.map (CommRingCat.ofHom (stageFractionFieldMap R K T)) ∧
        IsPullback c f (pullback.snd _ _)
          (Spec.map (CommRingCat.ofHom (stageFractionFieldMap R K T))) ∧
        Nonempty ((Scheme.Modules.pullback c).obj N.obj ≅ M.obj) := by
  obtain ⟨B, hB, _, NB, hNB, hmodel⟩ :=
    lineBundleSubalgebraDescent f₀ a f hpb M.obj M.property ∅
  obtain ⟨T, hCT, hT, hsR, hn, hnoeth, j, _, hj, hjC⟩ :=
    exists_normal_fractionFieldFactor_over hNormal C hC hCK sR B hB
  let βT := Spec.map (CommRingCat.ofHom (fractionFieldStageBaseMap R C T hCT))
  let βB := Spec.map (CommRingCat.ofHom (algebraMap C B))
  let κ := Spec.map (CommRingCat.ofHom (stageFractionFieldMap R K T))
  let b := Spec.map (CommRingCat.ofHom j)
  have hb : b ≫ βB = βT := by
    dsimp only [b, βB, βT]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hjC]
  have hκ : κ ≫ βT = Spec.map (CommRingCat.ofHom (algebraMap C K)) := by
    dsimp only [κ, βT]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      stageFractionFieldMap_comp_baseMap, ← hCK]
  have hκb : κ ≫ b = Spec.map (CommRingCat.ofHom (algebraMap B K)) := by
    dsimp only [κ, b]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hj]
    rfl
  have hp : pullback.fst f₀ βT ≫ f₀ =
      (pullback.snd f₀ βT ≫ b) ≫ βB := by
    rw [Category.assoc, hb, pullback.condition]
  let p : pullback f₀ βT ⟶ pullback f₀ βB :=
    pullback.lift (pullback.fst f₀ βT) (pullback.snd f₀ βT ≫ b) hp
  have hc : a ≫ f₀ = (f ≫ κ) ≫ βT := by
    rw [Category.assoc, hκ]
    exact hpb.w
  let c : X ⟶ pullback f₀ βT := pullback.lift a (f ≫ κ) hc
  have hc₁ : c ≫ pullback.fst f₀ βT = a := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd f₀ βT = f ≫ κ := pullback.lift_snd _ _ _
  have hcp₁ : (c ≫ p) ≫ pullback.fst f₀ βB = a := by
    rw [Category.assoc, show p ≫ pullback.fst f₀ βB = pullback.fst f₀ βT from
      pullback.lift_fst _ _ _, hc₁]
  have hcp₂ : (c ≫ p) ≫ pullback.snd f₀ βB =
      f ≫ Spec.map (CommRingCat.ofHom (algebraMap B K)) := by
    rw [Category.assoc, show p ≫ pullback.snd f₀ βB = pullback.snd f₀ βT ≫ b from
      pullback.lift_snd _ _ _, ← Category.assoc, hc₂, Category.assoc, hκb]
  have hcPullback : IsPullback c f (pullback.snd f₀ βT) κ := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f₀ βT) (v₁₃ := f₀)
      (h₂₂ := βT) ?_ hc₂ (IsPullback.of_hasPullback f₀ βT)
    rw [hc₁, hκ]
    exact hpb
  let N : LineBundle (pullback f₀ βT) :=
    ⟨(Scheme.Modules.pullback p).obj NB, hNB.pullback p⟩
  obtain ⟨e⟩ := hmodel (c ≫ p) hcp₁ hcp₂
  exact ⟨T, hCT, hT, hsR, hn, hnoeth, N, c, hc₁, hc₂, hcPullback,
    ⟨(Scheme.Modules.pullbackComp c p).app NB ≪≫ e⟩⟩

end Langlands.AlgebraicGeometry.NoetherianApproximation
