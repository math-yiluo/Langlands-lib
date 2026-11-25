/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorCoherence
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearCartesianProjection
import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Cartesian internal Hom evaluation

## References

* Zheng, Construction 4.1 and Proposition 4.17
* Stacks Tags 06YY, 07A4, 07A6 and 08J9
* Zheng Proposition 4.17
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096

universe c v r

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

private theorem evaluation_isRightAdjoint (n : ℕ) :
    (e.{c, v, max c v r} J B τ n).IsRightAdjoint := by
  let R := rings.{c, v, max c v r} J B τ
  let E := SheafOfModules.strictSystemSequenceEquivalence R
  have : E.functor.Additive := SheafOfModules.strictSystemToSequenceAdditive R
  have : E.inverse.Additive := SheafOfModules.sequenceToStrictSystemAdditive R
  let S : SheafOfModules.SystemScalarAssignment.{c, v, max c v r} (J := J) :=
    fun φ ↦ Classical.choice (SheafOfModules.nonempty_systemScalarModel φ)
  let T := SheafOfModules.systemTensorCoherence S
  let d := SheafOfModules.systemSingleDerivedExtension R n S T
  have := evaluationAdditive.{c, v, max c v r} J B τ n
  have := evaluationLimits.{c, v, max c v r} J B τ n
  have := evaluationColimits.{c, v, max c v r} J B τ n
  let η : E.inverse ⋙ SheafOfModules.systemEvaluation R n ≅
      evaluation.{c, v, max c v r} J B τ n :=
    SheafOfModules.pushforwardCongr (by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      change 𝟙 _ = (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom.app U
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl)
  let β := (Functor.mapDerivedCategoryCompIso E.inverse
      (SheafOfModules.systemEvaluation R n)) ≪≫
    Functor.mapDerivedCategoryNatIso η
  exact ((d.adjunction.comp E.mapDerivedCategory.toAdjunction).ofNatIsoRight β).isRightAdjoint

private theorem closed_evaluation_of_projection
    {A : Type*} [Category A] {D : Type*} [Category D]
    {H : Aᵒᵖ × A ⥤ A} {I : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
    (E : A ⥤ D) (L : D ⥤ A) (adj : L ⊣ E)
    (μ : S.tensor ⋙ E ≅ (E.prod E) ⋙ T.tensor) (M : A)
    (hp : ∀ P : D, IsIso ((adj.homEquiv _ _).symm
      (T.tensor.map (Prod.mkHom (adj.unit.app P) (𝟙 (E.obj M))) ≫
        μ.inv.app (L.obj P, M)))) :
    ∃ γ : Prod.sectR (op M) A ⋙ H ⋙ E ≅
        E ⋙ Prod.sectR (op (E.obj M)) D ⋙ I,
      ∀ N : A,
        T.tensor.map (Prod.mkHom (γ.hom.app N) (𝟙 (E.obj M))) ≫
          T.evaluation (E.obj M) (E.obj N) =
        μ.inv.app (H.obj (op M, N), M) ≫ E.map (S.evaluation M N) := by
  let θ : E ⋙ @MonoidalCategory.tensorRight D _ T.monoidal (E.obj M) ≅
      @MonoidalCategory.tensorRight A _ S.monoidal M ⋙ E :=
    NatIso.ofComponents (fun X ↦ (μ.app (X, M)).symm) (by
      intro X Y f
      simpa [CoefficientClosedStructure.tensor, MonoidalCategory.tensorRight] using
        μ.inv.naturality (Prod.mkHom f (𝟙 M)))
  let p := ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ θ.hom))
  have hcomponent (P : D) : p.app P = (adj.homEquiv _ _).symm
      (T.tensor.map (Prod.mkHom (adj.unit.app P) (𝟙 (E.obj M))) ≫
        μ.inv.app (L.obj P, M)) := by
    simp [p, θ, Adjunction.homEquiv_counit, Functor.map_comp,
      CoefficientClosedStructure.tensor, MonoidalCategory.tensorRight]
  have (P : D) : IsIso (p.app P) := by
    rw [hcomponent]
    exact hp P
  have : IsIso p := NatIso.isIso_of_isIso_app p
  let β := (mateEquiv (S.adjunction M) (T.adjunction (E.obj M))
    (TwoSquare.mk _ _ _ _ θ.hom))
  have hβ : β = conjugateEquiv (adj.comp (S.adjunction M))
      ((T.adjunction (E.obj M)).comp adj) p := by
    have h := iterated_mateEquiv_conjugateEquiv adj adj
      (T.adjunction (E.obj M)) (S.adjunction M)
      ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ θ.hom))
    rw [Equiv.apply_symm_apply] at h
    exact h
  have : IsIso β := by
    rw [hβ]
    infer_instance
  refine ⟨asIso β, ?_⟩
  intro N
  simpa [β, θ, CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
    MonoidalCategory.tensorRight, Prod.sectR] using
    mateEquiv_counit (S.adjunction M) (T.adjunction (E.obj M))
      (TwoSquare.mk _ _ _ _ θ.hom) N

variable (S : SystemScalarCoherence.{c, v, r} J B τ)
  (T : SystemTensorCoherence.{c, v, r} J B τ S)

/-- The cartesian comparison with its evaluation normalization, without a transition law. -/
structure SystemCartesianHomEvaluation where
  /-- The cartesian-input internal-Hom comparison, natural in the second input. -/
  homEvaluation : ∀ (M : DS.{c, v, max c v r} J B τ)
    (_hM : Normalized.{c, v, max c v r} J B τ S.scalar M) (n : ℕ),
    Prod.sectR (op M) (DS.{c, v, max c v r} J B τ) ⋙
      internalHom.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) ⋙
        e.{c, v, max c v r} J B τ n ≅
      e.{c, v, max c v r} J B τ n ⋙
        Prod.sectR (op ((e.{c, v, max c v r} J B τ n).obj M)) (D.{c, v, max c v r} J (B n)) ⋙
          internalHom.{c, v, r} J (B n)
  /-- The comparison carries the actual system evaluation to the level evaluation. -/
  homEvaluation_evaluation : ∀ (M N : DS.{c, v, max c v r} J B τ)
    (hM : Normalized.{c, v, max c v r} J B τ S.scalar M) (n : ℕ),
    (T.levelClosed n).tensor.map
        (Prod.mkHom ((homEvaluation M hM n).hom.app N)
          (𝟙 ((e.{c, v, max c v r} J B τ n).obj M))) ≫
        (T.levelClosed n).evaluation ((e.{c, v, max c v r} J B τ n).obj M)
          ((e.{c, v, max c v r} J B τ n).obj N) =
      (T.tensorEvaluation n).inv.app
        ((internalHom.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ)).obj (op M, N), M) ≫
        (e.{c, v, max c v r} J B τ n).map (T.closed.evaluation M N)

/-- Internal Hom evaluates on a cartesian first input, preserving its actual evaluation. -/
theorem systemCartesianHomEvaluation_nonempty :
    Nonempty (SystemCartesianHomEvaluation.{c, v, r} J B τ S T) := by
  classical
  have h (M : DS.{c, v, max c v r} J B τ)
      (hM : Normalized.{c, v, max c v r} J B τ S.scalar M) (n : ℕ) := by
    have := evaluation_isRightAdjoint.{c, v, r} J B τ n
    let E := e.{c, v, max c v r} J B τ n
    exact closed_evaluation_of_projection T.closed (T.levelClosed n) E E.leftAdjoint
      (Adjunction.ofIsRightAdjoint E) (T.tensorEvaluation n) M
      (semilinearCartesianProjection.{c, v, r} J B τ S.scalar T.closed T.tensorModels
        T.levelClosed T.levelTensorModels T.tensorEvaluation T.tensorEvaluationModel
        T.tensorEvaluationModel_ordinary M hM n E.leftAdjoint
        (Adjunction.ofIsRightAdjoint E))
  choose γ hγ using h
  exact ⟨{ homEvaluation := γ
           homEvaluation_evaluation := fun M N hM n ↦ hγ M hM n N }⟩

end WeilConjectures.SemilinearSections
