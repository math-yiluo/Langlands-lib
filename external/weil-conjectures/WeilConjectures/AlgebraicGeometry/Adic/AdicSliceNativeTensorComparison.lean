/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleSectionComparison

/-! # Native balanced tensor pullback on a site object -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.ProEtale

/-- The native tensor comparison induced on the balanced coequalizer by pullback.
Source: Stacks 03EL and the native module coequalizer
(blueprint: lem-sf-adic-slice-native-tensor). -/
noncomputable def adicSliceNativeTensorIso {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (U : X.ProEt) (M N : AdicSheaf l X) :
    (Mod.tensorLeft ((adicUpperStar l U.hom).obj N)).obj ((adicUpperStar l U.hom).obj M) ≅
      (adicUpperStar l U.hom).obj ((Mod.tensorLeft N).obj M) :=
  by
    have : PreservesColimitsOfShape WalkingParallelPair
        (Mod.mapModComap (adicUpperStarRingIso (l := l) (V := U.left) (X := X) U.hom)) :=
      inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (adicUpperStar l U.hom))
    exact ((Mod.tensorLeftCompMapModComapIso
      (adicUpperStarRingIso (l := l) (V := U.left) (X := X) U.hom)
      (fun _ _ ↦ Functor.LaxBraided.braided _ _) N).app M).symm

/-- The native balanced tensor comparison is normalized before taking the quotient.
Source: Stacks 03EL and `Mod.map_tensorπ_comp_tensorLeftCompMapModComapIso_hom`
(blueprint: lem-sf-adic-slice-native-tensor).

Proof: apply the general coequalizer comparison formula. Compose by the invertible
monoidal tensor map on the source and by the inverse module comparison on the
 target, then cancel the two isomorphism pairs. -/
theorem adicSliceNativeTensorIso_quotient {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (U : X.ProEt) (M N : AdicSheaf l X) :
    Mod.tensorπ ((adicUpperStar l U.hom).obj M) ((adicUpperStar l U.hom).obj N) ≫
        (adicSliceNativeTensorIso U M N).hom.hom =
      Functor.LaxMonoidal.μ (upperStar (WeilCoefficients.{u} l) U.hom) M.X N.X ≫
        (upperStar (WeilCoefficients.{u} l) U.hom).map (Mod.tensorπ M N) := by
  let rho := adicUpperStarRingIso (l := l) (V := U.left) (X := X) U.hom
  have : PreservesColimitsOfShape WalkingParallelPair (Mod.mapModComap rho) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (adicUpperStar l U.hom))
  let e := Mod.tensorLeftCompMapModComapIso rho
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) N
  have h := Mod.map_tensorπ_comp_tensorLeftCompMapModComapIso_hom rho
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) M N
  have h' : Mod.tensorπ ((adicUpperStar l U.hom).obj M) ((adicUpperStar l U.hom).obj N) =
      Functor.LaxMonoidal.μ (upperStar (WeilCoefficients.{u} l) U.hom) M.X N.X ≫
        (upperStar (WeilCoefficients.{u} l) U.hom).map (Mod.tensorπ M N) ≫
          (e.hom.app M).hom := by
    erw [h, IsIso.hom_inv_id_assoc]
    rfl
  change _ ≫ (e.inv.app M).hom = _
  erw [h', Category.assoc, Category.assoc, ← Mod.comp_hom', Iso.hom_inv_id_app,
    Mod.id_hom', Category.comp_id]

end AlgebraicGeometry.ProEtale
