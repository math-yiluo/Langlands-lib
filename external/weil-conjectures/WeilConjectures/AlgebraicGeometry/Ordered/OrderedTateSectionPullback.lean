/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

import all WeilConjectures.AlgebraicGeometry.Ordered.OrderedTateExactOpenComposition

/-! # Section coherence of the ordered Tate coefficient -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private lemma identity_comparison
    {C : Type*} [Category C] (F : C ⥤ C) (i : F ≅ 𝟭 C) (K : C)
    (a : F.obj K ≅ K) (c : F.obj K ⟶ F.obj (F.obj K)) [Epi c]
    (hu : c ≫ i.hom.app (F.obj K) = 𝟙 _)
    (hc : c ≫ F.map a.hom ≫ a.hom = a.hom) :
    a.hom = i.hom.app K := by
  have hm : F.map a.hom = i.hom.app (F.obj K) := by
    apply (cancel_epi c).mp
    calc
      c ≫ F.map a.hom = 𝟙 _ := by
        apply (cancel_mono a.hom).mp
        simpa only [Category.assoc, Category.id_comp] using hc
      _ = c ≫ i.hom.app (F.obj K) := hu.symm
  have hn := i.hom.naturality a.hom
  change F.map a.hom ≫ i.hom.app K = i.hom.app (F.obj K) ≫ a.hom at hn
  rw [hm] at hn
  exact ((cancel_epi (i.hom.app (F.obj K))).mp hn).symm

private lemma coefficient_identity (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) :
    (vectorIntegrationBaseCoefficientPullback A N hA t (𝟙 X) hX d).hom =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app
        (affineLinearBaseCoefficient A N hA X d) := by
  exact identity_comparison (ordinaryFinitePullback A (𝟙 X))
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X)
    (affineLinearBaseCoefficient A N hA X d)
    (vectorIntegrationBaseCoefficientPullback A N hA t (𝟙 X) hX d)
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.id_comp _).symm).hom.app _)
    (leftDerivedUpperStarComp_id_left_hom_app (ModuleCat.{u + 1} A) (𝟙 X) _)
    (coefficient_comp A N hA t
      (𝟙 X) (𝟙 X) (𝟙 X) (Category.id_comp _).symm hX hX d)

/-- Restricting the canonical ordered Tate pullback along a section gives the
canonical section compositor, with no residual automorphism of the coefficient. -/
theorem orderedTateSectionPullback (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Z : Scheme.{u}} (p : Z ⟶ X) (s : X ⟶ Z) (hs : s ≫ p = 𝟙 X)
    (hX : IsUnit (N : Γ(X, ⊤))) (hZ : IsUnit (N : Γ(Z, ⊤))) (d : ℕ) :
    (vectorIntegrationBaseCoefficientPullback A N hA t s hZ d).inv ≫
      (ordinaryFinitePullback A s).map
        (vectorIntegrationBaseCoefficientPullback A N hA t p hX d).inv ≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p hs).hom.app
        (affineLinearBaseCoefficient A N hA X d) = 𝟙 _ := by
  have hc := coefficient_comp A N hA t
    s p (𝟙 X) hs.symm hX hZ d
  rw [coefficient_identity] at hc
  simp only [leftDerivedUpperStarCompSectionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  rw [← hc]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id]
  rw [(ordinaryFinitePullback A s).map_id, Category.id_comp, Iso.inv_hom_id]

end AlgebraicGeometry.Etale
