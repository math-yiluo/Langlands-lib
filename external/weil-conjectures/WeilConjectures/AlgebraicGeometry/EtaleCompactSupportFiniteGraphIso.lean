/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportNormalizationData
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization

/-! # The specified compact-support graph map for a finite etale morphism

Source: Stacks Project Tags 0F4L and 015F
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The fixed derived graph comparison is invertible for a finite etale morphism.
Source: Stacks Project Tags 0F4L and 015F
(auxiliary; not a blueprint node).

Proof: Properness makes the compactification's open immersion clopen, so its extension
by zero equals its direct image and preserves K-injective complexes. The sheaf graph
normalization identifies the composite of the graph map into direct image with the
finite-etale sum-to-product isomorphism. Hence the sheaf graph map is an isomorphism,
and the composite j!r_* is exact. Its right-derived unit is invertible. The canonical
right-derived composition isomorphism and exactness of j! imply that the r_* unit on
j! applied to any complex is invertible. The component formula for the derived graph
map then consists entirely of invertible factors. Localization full faithfulness
reflects invertibility. No Noetherianity or finiteness of the coefficient ring is used. -/
theorem isIso_compactSupportGraphDerivedComparison_of_isFinite
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}}
    (f : U ⟶ X) [Etale f] [IsFinite f] (c : Compactification f) :
    IsIso (compactSupportDerivedComparison A f c
      (etaleCompactificationGraphMap A f c)) := by
  let F := openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i
  let G := lowerStar (ModuleCat.{u + 1} A) c.g
  let a := etaleCompactificationGraphMap A f c
  have hi : IsIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i) :=
    isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
      (ModuleCat.{u + 1} A) c.i (c.isClopen_range_openImmersion inferInstance).isClosed
  have : IsIso (compactificationSheafToDirectImage A c) := by
    dsimp [compactificationSheafToDirectImage]
    infer_instance
  have ha_app : ∀ M, IsIso (a.app M) := by
    intro M
    have : IsIso (a.app M ≫ (compactificationSheafToDirectImage A c).app M) := by
      change IsIso ((etaleCompactificationGraphMap A f c).app M ≫ _)
      rw [compactSupportGraphSheafComparison_normalization A f c M]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((compactificationSheafToDirectImage A c).app M)
  have ha : IsIso a := NatIso.isIso_of_isIso_app a
  change IsIso (compactSupportDerivedComparison A f c a)
  have : G.Additive := inferInstance
  have : F.Additive := inferInstance
  have : PreservesFiniteLimits (F ⋙ G) :=
    preservesFiniteLimits_of_natIso (asIso a)
  have : PreservesFiniteColimits (F ⋙ G) :=
    preservesFiniteColimits_of_natIso (asIso a)
  have : (lowerStar (ModuleCat.{u + 1} A) c.i).PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.i).preservesKInjectiveComplexes
  have : F.PreservesKInjectiveComplexes :=
    Functor.preservesKInjectiveComplexes_of_iso
      (asIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i)).symm
  have hfac : (F ⋙ G).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedFunctorCompIso F G).hom =
        Functor.rightDerivedFunctorCompUnit F G := by
    simp [Functor.rightDerivedFunctorCompIso]
  have : IsIso (Functor.rightDerivedFunctorCompUnit F G) := by
    rw [← hfac]
    infer_instance
  have hunit (K : HomotopyCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (ComplexShape.up ℤ)) :
      IsIso (G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K)) := by
    have h : IsIso ((Functor.rightDerivedFunctorCompUnit F G).app K) := inferInstance
    simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id] at h
    have := h
    have : IsIso (G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K)) :=
      IsIso.of_isIso_comp_left
        (DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K)) _
    exact IsIso.of_isIso_comp_right _
      (G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K))
  have haH : IsIso (NatTrans.mapHomotopyCategory a (.up ℤ)) :=
    ⟨NatTrans.mapHomotopyCategory (inv a) (.up ℤ),
      by rw [← NatTrans.mapHomotopyCategory_comp, IsIso.hom_inv_id,
        NatTrans.mapHomotopyCategory_id],
      by rw [← NatTrans.mapHomotopyCategory_comp, IsIso.inv_hom_id,
        NatTrans.mapHomotopyCategory_id]⟩
  have hcomp_app : ∀ K, IsIso ((Functor.whiskerLeft DerivedCategory.Qh
      (compactSupportDerivedComparison A f c a)).app K) := by
    intro K
    change IsIso ((compactSupportDerivedComparison A f c a).app (DerivedCategory.Qh.obj K))
    rw [compactSupportDerivedComparison_app]
    have hG : IsIso ((lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctorUnit.app
        (((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapHomotopyCategory
          (.up ℤ)).obj K)) := hunit K
    dsimp only [compactSupportComparisonOnHomotopy, normalizationHomotopyComponent]
    infer_instance
  have hwhisk : IsIso (Functor.whiskerLeft DerivedCategory.Qh
      (compactSupportDerivedComparison A f c a)) := NatIso.isIso_of_isIso_app _
  have : IsIso (((Functor.whiskeringLeft
      (HomotopyCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ))
      (DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))).obj
        DerivedCategory.Qh).map (compactSupportDerivedComparison A f c a)) := hwhisk
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (.up ℤ)) _).isIso_of_isIso_map _

end AlgebraicGeometry.Etale
