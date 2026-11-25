/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Connecting
public import WeilConjectures.CategoryTheory.Abelian.CokernelNSMul
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# The first right derived functor as a cokernel

Let `F : C ⥤ D` be a left exact additive functor between abelian categories and
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` a short exact sequence in `C` with `R¹F B = 0`. Then the long exact
sequence of right derived functors identifies `R¹F A` with the cokernel of `F B ⟶ F C`, the
quotient map being the connecting morphism `F C = R⁰F C ⟶ R¹F A`
(`CategoryTheory.ShortComplex.ShortExact.isColimitCokernelCoforkRightDerivedδ`).

Applied to an embedding `A ⟶ I` into an injective object, this recovers the classical
description `R¹F A = coker(F I ⟶ F(I/A))`; in particular `R¹F A = 0` as soon as `F` maps
`I ⟶ I/A` to an epimorphism (`CategoryTheory.Functor.isZero_rightDerived_one_of_epi_map`).
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [EnoughInjectives C] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

namespace ShortComplex.ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact)

/-- The connecting morphism `F C = R⁰F C ⟶ R¹F A` of a short exact sequence
`0 ⟶ A ⟶ B ⟶ C ⟶ 0`, for a left exact functor `F`. -/
def rightDerivedZeroδ : F.obj S.X₃ ⟶ (F.rightDerived 1).obj S.X₁ :=
  F.rightDerivedZeroIsoSelf.inv.app S.X₃ ≫ hS.rightDerivedδ F 0

@[reassoc (attr := simp)]
lemma map_g_comp_rightDerivedZeroδ : F.map S.g ≫ hS.rightDerivedZeroδ F = 0 := by
  rw [rightDerivedZeroδ, NatTrans.naturality_assoc, comp_rightDerivedδ, Limits.comp_zero]

/-- **`R¹F A` as a cokernel.** For a left exact functor `F` and a short exact sequence
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` with `R¹F B = 0`, the connecting morphism `F C ⟶ R¹F A` is a cokernel
of `F B ⟶ F C`. -/
def isColimitCokernelCoforkRightDerivedZeroδ (h : IsZero ((F.rightDerived 1).obj S.X₂)) :
    IsColimit (CokernelCofork.ofπ _ (hS.map_g_comp_rightDerivedZeroδ F)) := by
  have hT := hS.rightDerivedδ_exact₂ F 0
  have : Epi (hS.rightDerivedδ F 0) :=
    (hS.rightDerivedδ_exact₃ F 0).epi_f (h.eq_of_tgt _ _)
  exact CokernelCofork.isColimitOfArrowIso (F.rightDerivedZeroIsoSelf.app S.X₂).symm
    (F.rightDerivedZeroIsoSelf.app S.X₃).symm
    (F.rightDerivedZeroIsoSelf.inv.naturality S.g) hT.gIsCokernel

end ShortComplex.ShortExact

/-- **Vanishing of `R¹F A` from an injective embedding.** For a left exact functor `F` and a
monomorphism `ι : A ⟶ I` into an injective object, `R¹F A = 0` as soon as `F` maps the
quotient map `I ⟶ I / A` to an epimorphism. -/
lemma Functor.isZero_rightDerived_one_of_epi_map {A I : C} (ι : A ⟶ I) [Mono ι] [Injective I]
    [Epi (F.map (cokernel.π ι))] : IsZero ((F.rightDerived 1).obj A) := by
  let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel ι) inferInstance inferInstance
  have h := hS.isColimitCokernelCoforkRightDerivedZeroδ F
    (F.isZero_rightDerived_obj_injective_succ 0 I)
  have : Epi (hS.rightDerivedZeroδ F) := epi_of_isColimit_cofork h
  have hz : hS.rightDerivedZeroδ F = 0 := by
    rw [← cancel_epi (F.map S.g), hS.map_g_comp_rightDerivedZeroδ F, Limits.comp_zero]
  exact IsZero.of_epi_eq_zero _ hz

end CategoryTheory

end
