/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.DerivedMatePastedUnit

/-! # Compatibility of right derivation with exact-adjoint mate squares

Source: Mathlib's derived adjunction factorization equations; Stacks Project, Tag 079W.
(blueprint: lem-pc-exact-left-adjoint-derived-mate-compatibility).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u₁ u₂ u₃ u₄ w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor
variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
  [Category.{v} C] [Category.{v} D] [Category.{v} C'] [Category.{v} D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  [HasDerivedCategory.{w} C'] [HasDerivedCategory.{w} D']
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  [HasKInjectiveResolutions C'] [HasKInjectiveResolutions D']
  (F : C ⥤ D) (K : C' ⥤ D') (G : D ⥤ D') (H : C ⥤ C')
  (P : C' ⥤ C) (Q : D' ⥤ D)
  [F.Additive] [K.Additive] [G.Additive] [H.Additive] [P.Additive] [Q.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [H.PreservesKInjectiveComplexes]
  (ah : H ⊣ P) (ag : G ⊣ Q)
  (e : P ⋙ F ≅ K ⋙ Q) (m : F ⋙ G ≅ H ⋙ K)
  (hm : m.hom = ((mateEquiv ah ag).symm (TwoSquare.mk _ _ _ _ e.hom)))
  (ed : P.rightDerivedFunctor ⋙ F.rightDerivedFunctor ≅
    K.rightDerivedFunctor ⋙ Q.rightDerivedFunctor)
  (hed : rightDerivedFunctorCompUnit P F ≫ whiskerLeft DerivedCategory.Qh ed.hom =
    whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ)) DerivedCategory.Qh ≫
      rightDerivedFunctorCompUnit K Q)

/-- The explicit right-derived comparison, assembled from the two composition
comparisons and the derivation of the ordinary isomorphism.
Source: Stacks Project, Tags 079W and 08FE
(blueprint: lem-pc-exact-left-adjoint-derived-mate-compatibility). -/
noncomputable def exactMateComparison :
    F.rightDerivedFunctor ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ K.rightDerivedFunctor :=
  (rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived F G).symm ≪≫
    rightDerivedFunctorNatIso m ≪≫ rightDerivedFunctorCompIso H K ≪≫
      isoWhiskerRight (rightDerivedFunctorIsoMapDerivedCategory H) K.rightDerivedFunctor

include hm hed in
/-- Right derivation preserves an ordinary mate square when its two left adjoints
are exact. The right-adjoint square is fixed by its composite right-derived unit.
Source: Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean,
`derivedη_fac_app` and `derivedε_fac_app`; Stacks Project, Tag 079W.
(blueprint: lem-pc-exact-left-adjoint-derived-mate-compatibility).

Proof: Apply the mates equivalence to the required equality. The right adjoint P
of exact H preserves K-injective complexes, so RP followed by RF is a right
derived functor with the pasted unit. Its universal property reduces equality
of the two squares to equality after this unit. Expand the mate into the derived
G-unit, the explicitly derived ordinary comparison, and the derived H-counit.
Use naturality to move the pasted units through the G-unit and the comparison.
The factorization equation for rightDerivedUnique and rightDerivedFunctorNatTrans
identifies the comparison with the localized ordinary comparison. The determining
unit and counit equations of the derived adjunctions then replace the remaining
derived unit and counit by their ordinary counterparts. The resulting composite
is the ordinary mate of m, hence e by hm and the inverse law for mateEquiv.
The assumed unit equation hed identifies its localization with ed. Uniqueness
out of the right derived functor gives the square equality, and applying the
inverse mates equivalence gives the assertion. The argument uses no faithful
localization, no nonzero objects and no invertibility of individual units away
from K-injectives; zero categories and identity squares satisfy the same equations. -/
theorem exactMateComparison_eq :
    (exactMateComparison F K G H m).hom =
      ((mateEquiv ah.mapDerivedCategoryRightDerivedAdjunction
        ag.mapDerivedCategoryRightDerivedAdjunction).symm
          (TwoSquare.mk _ _ _ _ ed.hom)) := by
  have comparison_unit :
      rightDerivedFunctorCompUnit F G ≫
        whiskerLeft DerivedCategory.Qh
          (isoWhiskerLeft F.rightDerivedFunctor
            G.rightDerivedFunctorIsoMapDerivedCategory).hom ≫
        whiskerLeft DerivedCategory.Qh (exactMateComparison F K G H m).hom =
      whiskerRight (NatTrans.mapHomotopyCategory m.hom (.up ℤ)) DerivedCategory.Qh ≫
        rightDerivedFunctorCompUnit H K ≫
        whiskerLeft DerivedCategory.Qh
          (isoWhiskerRight H.rightDerivedFunctorIsoMapDerivedCategory
            K.rightDerivedFunctor).hom := by
    ext X
    simp [exactMateComparison, rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived,
      rightDerivedFunctorCompIso, rightDerivedFunctorNatIso,
      rightDerivedFunctorNatTrans, Category.assoc]
  have : P.PreservesKInjectiveComplexes := ah.preservesKInjectiveComplexes
  let sq := TwoSquare.mk _ _ _ _ (exactMateComparison F K G H m).hom
  let md := mateEquiv ah.mapDerivedCategoryRightDerivedAdjunction
    ag.mapDerivedCategoryRightDerivedAdjunction sq
  have hunit := derivedMate_pastedUnit F K G H P Q ah ag m.hom
    (exactMateComparison F K G H m).hom comparison_unit
  have he : (mateEquiv ah ag (TwoSquare.mk _ _ _ _ m.hom)) = e.hom := by
    have hs : TwoSquare.mk _ _ _ _ m.hom =
        (mateEquiv ah ag).symm (TwoSquare.mk _ _ _ _ e.hom) := by
      refine NatTrans.ext (funext fun X ↦ ?_)
      exact congrArg (fun t => t.app X) hm
    rw [hs, Equiv.apply_symm_apply]
  rw [he] at hunit
  have hmd : md = ed.hom := by
    apply (P.rightDerivedFunctor ⋙ F.rightDerivedFunctor).rightDerived_ext
      (rightDerivedFunctorCompUnit P F) (HomotopyCategory.quasiIso C' (.up ℤ))
    exact hunit.trans hed.symm
  have hs : md = TwoSquare.mk _ _ _ _ ed.hom := by
    refine NatTrans.ext (funext fun X ↦ ?_)
    exact congrArg (fun t => t.app X) hmd
  have h := (mateEquiv ah.mapDerivedCategoryRightDerivedAdjunction
    ag.mapDerivedCategoryRightDerivedAdjunction).symm_apply_apply sq
  change (mateEquiv ah.mapDerivedCategoryRightDerivedAdjunction
    ag.mapDerivedCategoryRightDerivedAdjunction).symm md = sq at h
  rw [hs] at h
  exact (h).symm

end CategoryTheory.Functor
