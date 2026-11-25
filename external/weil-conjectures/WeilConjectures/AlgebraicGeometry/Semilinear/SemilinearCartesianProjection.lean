/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearProjectionBelowFactorization
import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedEvaluation
import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos

/-! # Projection formula for cartesian semilinear systems

## References

* Zheng Construction 4.1 and Lemma 4.10
* Stacks 06YS, 07A4 and 08J9
* Zheng Construction 4.1, printed p.21, and Proposition 4.17(a), printed pp.25-26
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
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

private theorem evaluation_detects
    {M N : DS.{c, v, max c v r} J B τ} (f : M ⟶ N)
    (hf : ∀ q, IsIso ((e.{c, v, max c v r} J B τ q).map f)) : IsIso f := by
  let R := rings.{c, v, max c v r} J B τ
  let E := SheafOfModules.strictSystemSequenceEquivalence R
  have : E.functor.Additive := SheafOfModules.strictSystemToSequenceAdditive R
  have : E.inverse.Additive := SheafOfModules.sequenceToStrictSystemAdditive R
  have (m : ℕ) : (evaluation.{c, v, max c v r} J B τ m).Additive :=
    evaluationAdditive.{c, v, max c v r} J B τ m
  have (m : ℕ) : PreservesFiniteLimits (evaluation.{c, v, max c v r} J B τ m) :=
    evaluationLimits.{c, v, max c v r} J B τ m
  have (m : ℕ) : PreservesFiniteColimits (evaluation.{c, v, max c v r} J B τ m) :=
    evaluationColimits.{c, v, max c v r} J B τ m
  have h (q : ℕ) : E.inverse ⋙ SheafOfModules.systemEvaluation R q ≅
      evaluation.{c, v, max c v r} J B τ q :=
    SheafOfModules.pushforwardCongr (by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      change 𝟙 _ = (eqToHom (evaluation_ring.{c, v, max c v r} J B τ q).symm).hom.app U
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl)
  have hh (q : ℕ) : E.mapDerivedCategory.inverse ⋙
      SheafOfModules.derivedSystemEvaluation R q ≅ e.{c, v, max c v r} J B τ q :=
    Functor.mapDerivedCategoryCompIso E.inverse
      (SheafOfModules.systemEvaluation R q) ≪≫
      Functor.mapDerivedCategoryNatIso (h q)
  have : IsIso (E.mapDerivedCategory.inverse.map f) := by
    apply (SheafOfModules.systemDerivedEvaluation_isIso_iff R _).2
    intro q
    have := hf q
    exact (NatIso.isIso_map_iff (hh q) f).2 inferInstance
  exact isIso_of_reflects_iso f E.mapDerivedCategory.inverse

private theorem singleton_above
    (n q : ℕ) (hq : n < q)
    (L : D.{c, v, max c v r} J (B n) ⥤ DS.{c, v, max c v r} J B τ)
    (adj : L ⊣ e.{c, v, max c v r} J B τ n)
    (P : D.{c, v, max c v r} J (B n)) :
    IsZero ((e.{c, v, max c v r} J B τ q).obj (L.obj P)) := by
  let R := rings.{c, v, max c v r} J B τ
  let E := SheafOfModules.strictSystemSequenceEquivalence R
  have : E.functor.Additive := SheafOfModules.strictSystemToSequenceAdditive R
  have : E.inverse.Additive := SheafOfModules.sequenceToStrictSystemAdditive R
  let S : SheafOfModules.SystemScalarAssignment.{c, v, max c v r} (J := J) :=
    fun φ ↦ Classical.choice (SheafOfModules.nonempty_systemScalarModel φ)
  let T := SheafOfModules.systemTensorCoherence S
  let d := SheafOfModules.systemSingleDerivedExtension R n S T
  have (m : ℕ) : (evaluation.{c, v, max c v r} J B τ m).Additive :=
    evaluationAdditive.{c, v, max c v r} J B τ m
  have (m : ℕ) : PreservesFiniteLimits (evaluation.{c, v, max c v r} J B τ m) :=
    evaluationLimits.{c, v, max c v r} J B τ m
  have (m : ℕ) : PreservesFiniteColimits (evaluation.{c, v, max c v r} J B τ m) :=
    evaluationColimits.{c, v, max c v r} J B τ m
  have h (m : ℕ) : E.inverse ⋙ SheafOfModules.systemEvaluation R m ≅
      evaluation.{c, v, max c v r} J B τ m :=
    SheafOfModules.pushforwardCongr (by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      change 𝟙 _ = (eqToHom (evaluation_ring.{c, v, max c v r} J B τ m).symm).hom.app U
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl)
  let β (m : ℕ) : E.mapDerivedCategory.inverse ⋙
      SheafOfModules.derivedSystemEvaluation R m ≅ e.{c, v, max c v r} J B τ m :=
    Functor.mapDerivedCategoryCompIso E.inverse
      (SheafOfModules.systemEvaluation R m) ≪≫
      Functor.mapDerivedCategoryNatIso (h m)
  let a := (d.adjunction.comp E.mapDerivedCategory.toAdjunction).ofNatIsoRight (β n)
  let γ := adj.leftAdjointUniq a
  let i : (e.{c, v, max c v r} J B τ q).obj (L.obj P) ≅
      (SheafOfModules.derivedSystemEvaluation R q).obj (d.derived.obj P) :=
    (e.{c, v, max c v r} J B τ q).mapIso (γ.app P) ≪≫
      (β q).symm.app _ ≪≫
      (SheafOfModules.derivedSystemEvaluation R q).mapIso
        (E.mapDerivedCategory.unitIso.symm.app (d.derived.obj P))
  exact (SheafOfModules.systemSingleDerivedAbove S T R q n hq P).of_iso i

/-- The unit-defined projection for derived extension from one coefficient level is
invertible for a cartesian system. No internal-Hom comparison is assumed. -/
theorem semilinearCartesianProjection
    (scalar : ∀ {m n : ℕ} (h : n ≤ m),
      ScalarData.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h))
    (closed : Closed.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ))
    (models : Models.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) closed)
    (level : ∀ n : ℕ, Closed.{c, v, r} J (B n))
    (levelModels : ∀ n : ℕ, Models.{c, v, r} J (B n) (level n))
    (tensorEvaluation : ∀ n : ℕ,
      closed.tensor ⋙ e.{c, v, max c v r} J B τ n ≅
        ((e.{c, v, max c v r} J B τ n).prod
          (e.{c, v, max c v r} J B τ n)) ⋙ (level n).tensor)
    (tensorModel : ∀ n : ℕ,
      TensorComparisonModel.{c, v, r} (coefficientSequenceTopology J) J
        (systemRing.{c, v, max c v r} J B τ) (B n)
        (evaluation.{c, v, max c v r} J B τ n) closed (level n) models
        (levelModels n) (tensorEvaluation n))
    (ordinary : ∀ (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ),
      (tensorModel n).ordinary M N = ordinaryEvaluationTensor.{c, v, r} J B τ n M N)
    (M : DS.{c, v, max c v r} J B τ)
    (hM : Normalized.{c, v, max c v r} J B τ scalar M) (n : ℕ) :
    ∀ (L : D.{c, v, max c v r} J (B n) ⥤ DS.{c, v, max c v r} J B τ)
      (adj : L ⊣ e.{c, v, max c v r} J B τ n)
      (P : D.{c, v, max c v r} J (B n)),
      IsIso ((adj.homEquiv _ _).symm
        ((level n).tensor.map
            (Prod.mkHom (adj.unit.app P)
              (𝟙 ((e.{c, v, max c v r} J B τ n).obj M))) ≫
          (tensorEvaluation n).inv.app (L.obj P, M))) := by
  intro L adj P
  let f := (adj.homEquiv _ _).symm
    ((level n).tensor.map
        (Prod.mkHom (adj.unit.app P)
          (𝟙 ((e.{c, v, max c v r} J B τ n).obj M))) ≫
      (tensorEvaluation n).inv.app (L.obj P, M))
  apply evaluation_detects.{c, v, r} J B τ f
  intro q
  by_cases h : q ≤ n
  · obtain ⟨α, hα⟩ := semilinearProjectionBelowFactorization.{c, v, r} J B τ
      closed models level levelModels tensorEvaluation tensorModel ordinary
      M n q h (scalar h) L adj P
    have : IsIso (reduction.{c, v, max c v r} J B τ h (scalar h) M) := hM h
    have : IsIso (Prod.mkHom
        (𝟙 ((e.{c, v, max c v r} J B τ q).obj (L.obj P)))
        (reduction.{c, v, max c v r} J B τ h (scalar h) M)) :=
      (CategoryTheory.isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    have : IsIso ((e.{c, v, max c v r} J B τ q).map f ≫
        (tensorEvaluation q).hom.app (L.obj P, M)) := by
      rw [show (e.{c, v, max c v r} J B τ q).map f ≫
          (tensorEvaluation q).hom.app (L.obj P, M) = _ from hα]
      infer_instance
    exact (isIso_comp_right_iff _ ((tensorEvaluation q).hom.app (L.obj P, M))).1
      inferInstance
  · have hs := singleton_above.{c, v, r} J B τ n q (Nat.lt_of_not_ge h) L adj
      ((level n).tensor.obj (P, (e.{c, v, max c v r} J B τ n).obj M))
    have hp := singleton_above.{c, v, r} J B τ n q (Nat.lt_of_not_ge h) L adj P
    let F := @MonoidalCategory.tensorRight _ _ (level q).monoidal
      ((e.{c, v, max c v r} J B τ q).obj M)
    have : F.IsLeftAdjoint := ((level q).adjunction _).isLeftAdjoint
    have ht : IsZero ((level q).tensor.obj
        ((e.{c, v, max c v r} J B τ q).obj (L.obj P),
          (e.{c, v, max c v r} J B τ q).obj M)) :=
      F.map_isZero hp
    have hz := ht.of_iso ((tensorEvaluation q).app (L.obj P, M))
    exact hs.isIso hz _

end WeilConjectures.SemilinearSections
