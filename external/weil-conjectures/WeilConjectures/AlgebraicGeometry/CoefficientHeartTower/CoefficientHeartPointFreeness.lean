/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift

/-! # Finite freeness at the chosen geometric point

Source: coefficient-heart proof (1), lifting the geometric point to a free chart.
(blueprint: lem-sfb-coefficient-heart-point-freeness)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower

/-- A lisse native coefficient module becomes finite free at a geometric point.
Source: coefficient-heart proof (1), compatible free charts above the chosen point;
Bhatt--Scholze, Example 4.1.10.
(blueprint: lem-sfb-coefficient-heart-point-freeness)
Proof: lift the algebraically closed point to a member of the pro-etale covering in the
lisse condition. Pull its finite-free presentation back along that lift. The additive
inverse-image functor preserves finite sums and the regular module. Finally transport
along the composition isomorphism for native module inverse images. No field or rank
hypothesis on the coefficient ring is needed. -/
theorem point_freeness
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLisseCoefficientModule Λ M)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ X) :
    Mod.IsFree (condensedRingObj Λ (Spec (.of Ω)))
      ((CondensedRing.upperStar Λ v).obj M) := by
  obtain ⟨U, hU⟩ := hM
  obtain ⟨i, g, hg⟩ := U.exists_comp_eq_of_isSepClosed_of_proetale v
  subst v
  have hfree := (hU i).map (CondensedRing.upperStar Λ g)
    (CondensedRing.upperStarObjRegularIso Λ g)
  exact hfree.of_iso ((CondensedRing.upperStarComp Λ g (U.f i)).app M).symm

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
