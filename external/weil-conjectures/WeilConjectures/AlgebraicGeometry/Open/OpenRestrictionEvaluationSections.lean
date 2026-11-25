/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement

/-! # Evaluation of restriction to an open slice

## References

* Stacks Project, Tags 03DI and 03DJ
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c v r c₁ v₁ r₁
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections

-- Keep the coefficient sheaves abstract when checking the identity section maps.
-- This avoids unfolding the concrete sequence-ring construction in the kernel.
private theorem openEvaluationPushforwardComparison
    {D : Type c₁} [Category.{v₁} D] (K : GrothendieckTopology D) (U : D) (n : ℕ)
    (L : GrothendieckTopology (ℕ × D))
    (P : GrothendieckTopology (ℕ × Over U))
    [(openSite U).IsContinuous P L]
    [(Prod.sectR n D).IsContinuous K L]
    [(Prod.sectR n (Over U)).IsContinuous (K.over U) P]
    (R : Sheaf L RingCat.{r₁}) (S : Sheaf P RingCat.{r₁})
    (T : Sheaf K RingCat.{r₁})
    (a : S ⟶ ((openSite U).sheafPushforwardContinuous RingCat.{r₁} P L).obj R)
    (b : T.over U ⟶ ((Prod.sectR n (Over U)).sheafPushforwardContinuous
      RingCat.{r₁} (K.over U) P).obj S)
    (d : T ⟶ ((Prod.sectR n D).sheafPushforwardContinuous RingCat.{r₁} K L).obj R)
    (h : b ≫ ((Prod.sectR n (Over U)).sheafPushforwardContinuous
        RingCat.{r₁} (K.over U) P).map a =
      (𝟙 _) ≫ ((Over.forget U).sheafPushforwardContinuous
        RingCat.{r₁} (K.over U) K).map d) :
    ∃ δ : SheafOfModules.pushforward.{r₁} a ⋙ SheafOfModules.pushforward.{r₁} b ≅
        SheafOfModules.pushforward.{r₁} d ⋙ SheafOfModules.overFunctor.{r₁} T U,
      ∀ (M : SheafOfModules.{r₁} R) (W : Over U)
        (x : ((SheafOfModules.pushforward.{r₁} a ⋙
          SheafOfModules.pushforward.{r₁} b).obj M).val.obj (op W)),
        HEq ((δ.hom.app M).val.app (op W) x) x := by
  let i := SheafOfModules.pushforwardComp.{r₁}
    (F := Prod.sectR n (Over U)) (G := openSite U) b a
  let j := SheafOfModules.pushforwardComp.{r₁}
    (J := K.over U) (F := Over.forget U) (G := Prod.sectR n D) (𝟙 _) d
  have := Functor.isContinuous_comp (Prod.sectR n (Over U)) (openSite U)
    (K.over U) P L
  refine ⟨i ≪≫ SheafOfModules.pushforwardCongr.{r₁}
    (F := Prod.sectR n (Over U) ⋙ openSite U) h ≪≫ j.symm, ?_⟩
  intro M W x
  exact HEq.rfl

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
attribute [local irreducible] systemRing ringPresheaf rings

/-- Evaluation commutes with open restriction by the identity on sections. -/
theorem openRestrictionEvaluationSections (U : C) (n : ℕ) :
    ∃ δ : openRestriction.{c, v, r} J B τ U ⋙
      evaluation.{max c v, v, max c v r} (J.over U)
        (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n ≅
      evaluation.{c, v, max c v r} J B τ n ⋙
        SheafOfModules.localizedSystemRestriction.{c, v, r} (B n) U,
      ∀ (N : Systems.{c, v, max c v r} J B τ) (W : Over U)
        (x : ((openRestriction.{c,v,r} J B τ U ⋙
          evaluation.{max c v, v, max c v r} (J.over U)
            (openRings.{c,v,r} J B U) (openTransitions.{c,v,r} J B τ U) n).obj N).val.obj
          (op W)),
        HEq ((δ.hom.app N).val.app (op W) x) x := by
  let a := eqToHom (openRing.{c, v, r} J B τ U).symm
  let b := eqToHom (evaluation_ring.{max c v, v, max c v r} (J.over U)
    (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n).symm
  let d := eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm
  have h : b ≫ ((Prod.sectR n (Over U)).sheafPushforwardContinuous
        RingCat.{max c v r} (J.over U) (coefficientSequenceTopology (J.over U))).map a =
      (𝟙 _) ≫ ((Over.forget U).sheafPushforwardContinuous RingCat.{max c v r}
        (J.over U) J).map d := by
    dsimp only [a, b, d]
    simp only [eqToHom_map, eqToHom_trans, Category.id_comp]
  exact openEvaluationPushforwardComparison J U n (coefficientSequenceTopology J)
    (coefficientSequenceTopology (J.over U))
    (ring.{c, v, max c v r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ))
    (ring.{max c v, v, max c v r} (coefficientSequenceTopology (J.over U))
      (systemRing.{max c v, v, max c v r} (J.over U)
        (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U)))
    (ring.{c, v, max c v r} J (B n)) a b d h

end WeilConjectures.SemilinearSections
