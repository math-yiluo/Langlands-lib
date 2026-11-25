/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentOrdinaryEdges
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal

set_option linter.privateModule false

/-! # Coefficient-normalized ordinary component square coherence

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

@[reassoc]
private theorem square_unit
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    {cx : Corner Λ X} {cy : Corner Λ Y} {sh : Slice Λ (affineComponentMap f)}
    (sq : Square Λ f cx cy sh)
    (M : Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      Ab.{u + 1}) (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))) :
    CondensedRing.upperStarUnitHom Λ.X f ((cx.modules Λ X).obj M) ≫
        (sq.ordinary.hom.app M).hom = sq.abelian.hom.app M.X := by
  rw [sq.ordinary_underlying, ← Category.assoc]
  let N := ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ.X X)).obj
    ((cx.modules Λ X).obj M)
  change (Mod.extendUnitHom (condensedPullbackHom Λ.X f) N ≫
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ.X f)).hom.app N).hom) ≫
        sq.abelian.hom.app M.X = _
  rw [Mod.extendUnitHom_extendScalarsIsoComapInv_hom_app
    (condensedPullbackHom Λ.X f) N]
  exact Category.id_comp _

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
