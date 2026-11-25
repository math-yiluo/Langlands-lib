/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FormalFunctionsFinitePullback
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
namespace AlgebraicGeometry
/-- The finite pullback maps are linear and factor through a quotient-system isomorphism.
Source: Stacks Project, Tag 02OD and Tags 01F7, 01FB.
(blueprint: lem-weil-pbc-formal-functions-finite-quotient-iso-r)
Proof: Compose the linear map underlying each component of b with the linear
cohomology map induced by the quotient projection. The first component formula is
definitional; the supplied quotient-unit equation gives the finite pullback formula. -/
theorem formalFunctions_finite_quotient_iso_r {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (y : Y) (p : ℕ) :
    let X' := pullback (Y.fromSpecStalk y) f
    let f' := pullback.fst (Y.fromSpecStalk y) f
    let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
    let J := (Scheme.IdealSheafData.ofIdealTop
      ((maximalIdeal (Y.presheaf.stalk y)).map
        (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap f'
    let C := RingedSpace.moduleCohomology X'.toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫ f'.appTop).hom
    ∀ (b : formalCompletionSystem J F' ⋙ C ≅
      formalFibreCohomologySystem f y F p ⋙ ModuleCat.restrictScalars
        (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))),
      (∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p),
        (b.hom.app (op n)) ((C.map (formalModuleQuotientπ J (n + 1) F')) z) =
          formalFunctionsFinitePullback f y F p n z) →
      ∃ r : ∀ n : ℕ, formalFunctionsLocalCohomology f y F p →ₗ[Y.presheaf.stalk y]
        formalFibreCohomologyLocal f y F p n,
        (∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p),
          r n z = (b.hom.app (op n)) ((C.map (formalModuleQuotientπ J (n + 1) F')) z)) ∧
        ∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p),
          r n z = formalFunctionsFinitePullback f y F p n z := by
  have _hF := hF
  intro X' f' F' J C b hb
  refine ⟨fun n ↦ (b.hom.app (op n)).hom.comp
    (C.map (formalModuleQuotientπ J (n + 1) F')).hom, ?_, ?_⟩
  · intro n z
    rfl
  · intro n z
    exact hb n z
end AlgebraicGeometry
