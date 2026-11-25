/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition

/-! # Canonical base-change stalk transitions

The targets and restriction maps used in the continuity step of Stacks Tag 0F07.
(blueprint: def-sbc-canonical-base-change-stalk-transitions)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X S T : Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S) (q : ℤ)
variable (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)

/-- Source stalk of the canonical square over an object of `Over T`. -/
noncomputable abbrev baseChangeSourceStalk (U : Over T) : ModuleCat.{u + 1} Λ :=
  (X.uliftPointSmallEtale x).sheafFiber.obj
    ((baseChangeSourceFunctor Λ p (U.hom ≫ g) q).obj
      (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F))

/-- Target stalk of the canonical square over an object of `Over T`. -/
noncomputable abbrev baseChangeTargetStalk (U : Over T) : ModuleCat.{u + 1} Λ :=
  (X.uliftPointSmallEtale x).sheafFiber.obj
    ((baseChangeTargetFunctor Λ (pullback.fst (U.hom ≫ g) p)
      (pullback.snd (U.hom ≫ g) p) q).obj
        (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F))

/-- The base-change linear map on a geometric stalk. -/
noncomputable def baseChangeStalkMap (U : Over T) :
    baseChangeSourceStalk Λ p g q F x U ⟶ baseChangeTargetStalk Λ p g q F x U :=
  (X.uliftPointSmallEtale x).sheafFiber.map
    (baseChangeHomologyMap Λ (IsPullback.of_hasPullback (U.hom ≫ g) p) q
      (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F))

/-- Restriction of a target stalk along a morphism over `T`, with its coefficient comparison.
The pullback lift is canonical, so this is the same map used in the limit theorem. 
(blueprint: def-sbc-canonical-base-change-stalk-transitions)
-/
noncomputable def baseChangeTargetStalkMap {U V : Over T} (φ : U ⟶ V) :
    baseChangeTargetStalk Λ p g q F x V ⟶ baseChangeTargetStalk Λ p g q F x U :=
  (X.uliftPointSmallEtale x).sheafFiber.map
    (baseChangeTargetTransition Λ (pullback.fst (V.hom ≫ g) p)
        (pullback.snd (V.hom ≫ g) p) q φ.left
        (pullback.lift (pullback.fst (U.hom ≫ g) p ≫ φ.left)
          (pullback.snd (U.hom ≫ g) p)
          (by rw [Category.assoc, ← Category.assoc φ.left, Over.w];
              exact pullback.condition))
        (pullback.fst (U.hom ≫ g) p) (pullback.snd (U.hom ≫ g) p)
        (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
        (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj F) ≫
      (baseChangeTargetFunctor Λ (pullback.fst (U.hom ≫ g) p)
        (pullback.snd (U.hom ≫ g) p) q).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) φ.left V.hom U.hom
            (Over.w φ).symm).inv.app F))

variable {Y : Scheme.{u}} {e : Y ⟶ T} {h : Y ⟶ X}

/-- Transport from the original square to a canonical square over `T`. -/
noncomputable def baseChangeStalkTransport (sq : IsPullback e h g p) (U : Over T) :
    (X.uliftPointSmallEtale x).sheafFiber.obj
      ((baseChangeTargetFunctor Λ e h q).obj F) ⟶
        baseChangeTargetStalk Λ p g q F x U :=
  (X.uliftPointSmallEtale x).sheafFiber.map
    (baseChangeTargetTransition Λ e h q U.hom
      (sq.lift (pullback.fst (U.hom ≫ g) p ≫ U.hom) (pullback.snd (U.hom ≫ g) p)
        (by rw [Category.assoc]; exact pullback.condition))
      (pullback.fst (U.hom ≫ g) p) (pullback.snd (U.hom ≫ g) p)
      (sq.lift_fst _ _ _) (sq.lift_snd _ _ _) F)

end AlgebraicGeometry.Etale
