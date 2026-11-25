/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Independence of a right-derived mate from exact left-adjoint choices

The canonical right-derived unit identifies a derived mate from its ordinary mate.
(blueprint: lem-weil-right-derived-mate-independence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
  {L Q : B ⥤ A} {R : A ⥤ B} {L' Q' : D ⥤ C} {R' : C ⥤ D}
  (G : B ⥤ D) (H : A ⥤ C)
  [L.Additive] [Q.Additive] [R.Additive]
  [L'.Additive] [Q'.Additive] [R'.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits Q'] [PreservesFiniteColimits Q']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
/-- Invertibility of a canonical derived right mate is independent of the exact
left-adjoint models, provided both ordinary right mates are invertible.
Source: Stacks, Tags 070I, 070K and 07A7
(blueprint: lem-weil-right-derived-mate-independence).

On a K-injective source complex the source derived unit is invertible. Apply the
cochain normalization to the reference mate: its derived invertibility and the
ordinary mate's invertibility show that the target derived unit is invertible.
The same normalization for the desired mate then expresses it using isomorphisms.
Every derived object is isomorphic to a K-injective representative, so naturality
transfers this conclusion to all objects. -/
theorem rightDerivedMate_isIso_of_ordinaryMate_isIso
    (a : L ⊣ R) (b : L' ⊣ R') (c : Q ⊣ R) (d : Q' ⊣ R')
    (θ : G ⋙ L' ≅ L ⋙ H) (ψ : G ⋙ Q' ≅ Q ⋙ H)
    (ha : IsIso (mateEquiv a b θ.hom))
    (hb : IsIso (mateEquiv c d ψ.hom))
    (hd : IsIso (mateEquiv c.mapDerivedCategoryRightDerivedAdjunction
      d.mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategorySquareIso ψ).hom)) :
    IsIso (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategorySquareIso θ).hom) := by
  let α := (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
    b.mapDerivedCategoryRightDerivedAdjunction
    (Functor.mapDerivedCategorySquareIso θ).hom)
  have := ha
  have := hb
  have := hd
  have hI (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
      IsIso (α.app (DerivedCategory.Q.obj I)) := by
    have := hI
    have h₁ := UnboundedExactTower.localized_mate_cochain_normalization a b θ I
    have h₂ := UnboundedExactTower.localized_mate_cochain_normalization c d ψ I
    dsimp only [UnboundedExactTower.localizedSquare] at h₁ h₂
    have hu : IsIso (UnboundedExactTower.cochainUnit R I) := by
      unfold UnboundedExactTower.cochainUnit
      infer_instance
    have hca : IsIso ((NatTrans.mapHomologicalComplex
        (mateEquiv a b θ.hom) (.up ℤ)).app I) := by
      change IsIso ((NatIso.mapHomologicalComplex
        (asIso (mateEquiv a b θ.hom)) (.up ℤ)).hom.app I)
      infer_instance
    have hcb : IsIso ((NatTrans.mapHomologicalComplex
        (mateEquiv c d ψ.hom) (.up ℤ)).app I) := by
      change IsIso ((NatIso.mapHomologicalComplex
        (asIso (mateEquiv c d ψ.hom)) (.up ℤ)).hom.app I)
      infer_instance
    have hs : IsIso (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (mateEquiv c d ψ.hom) (.up ℤ)).app I) ≫
        UnboundedExactTower.cochainUnit R' ((H.mapHomologicalComplex (.up ℤ)).obj I)) := by
      rw [← h₂]
      infer_instance
    have hv : IsIso (UnboundedExactTower.cochainUnit R'
        ((H.mapHomologicalComplex (.up ℤ)).obj I)) :=
      IsIso.of_isIso_comp_left
        (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (mateEquiv c d ψ.hom) (.up ℤ)).app I))
        (UnboundedExactTower.cochainUnit R' ((H.mapHomologicalComplex (.up ℤ)).obj I))
    have ht : IsIso (G.mapDerivedCategoryFactors.inv.app
        ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
        G.mapDerivedCategory.map (UnboundedExactTower.cochainUnit R I) ≫
        α.app (DerivedCategory.Q.obj I) ≫
        R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I)) := by
      change IsIso (G.mapDerivedCategoryFactors.inv.app
        ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
        G.mapDerivedCategory.map (UnboundedExactTower.cochainUnit R I) ≫
        (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
          b.mapDerivedCategoryRightDerivedAdjunction
          (Functor.mapDerivedCategorySquareIso θ).hom).app
            (DerivedCategory.Q.obj I) ≫
        R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I))
      rw [h₁]
      infer_instance
    simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using ht
  change IsIso α
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ α ?_
  intro N
  obtain ⟨I, hIi, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
  have := hI I hIi
  have hs : IsIso ((R.rightDerivedFunctor ⋙ G.mapDerivedCategory).map e.hom ≫
      α.app (DerivedCategory.Q.obj I)) := inferInstance
  rw [α.naturality e.hom] at hs
  exact IsIso.of_isIso_comp_right (α.app N)
    ((H.mapDerivedCategory ⋙ R'.rightDerivedFunctor).map e.hom)

end CategoryTheory
