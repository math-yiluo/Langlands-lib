/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.InverseMateEquivalence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# The affine closed-site counit at specializing objects

## References

* Stacks Project, Tag 09AC, with the fully faithful adjunction of Tag 09BK
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.AffineProEt

set_option backward.isDefEq.respectTransparency false in
/-- The affine closed-site counit is invertible at a weakly contractible object
whose points specialize into the closed fibre. -/
theorem isIso_closedSiteCounit_of_specialization
    (A : Type u) [CommRing A] (I : Ideal A)
    (adj : closedSiteLift A I ⊣ closedSiteBaseChange A I)
    (V : (Spec (.of A)).AffineProEt)
    (hweak : ∀ (P Q : Sheaf (topology (Spec (.of A))) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)))
    (hspec : ∀ x : V.left, ∃ z : ↥(pullback V.hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))),
      Specializes x ((pullback.fst V.hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) z)) :
    IsIso (adj.counit.app V) := by
  obtain ⟨_, _, hfull, hfaith, _, _, _, _⟩ := affine_closed_site_functor_properties A I
  have : (closedSiteLift A I).Full := hfull
  have : (closedSiteLift A I).Faithful := hfaith
  let v := closedSiteLift A I
  let r := closedSiteBaseChange A I
  let p := adj.counit.app V
  have hp : IsIso (r.map p) := inferInstance
  have hpi : IsIso (r.map p).left := inferInstance
  have hs : Surjective p.left := by
    constructor
    intro x
    obtain ⟨z, hxz⟩ := hspec x
    obtain ⟨w, hw⟩ := (asIso (r.map p).left).hom.surjective z
    have hfst : (r.map p).left ≫ pullback.fst V.hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
        pullback.fst (v.obj (r.obj V)).hom
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ p.left := by
      exact pullback.lift_fst _ _ _
    have hw' : p.left ((pullback.fst (v.obj (r.obj V)).hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) w) =
        (pullback.fst V.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) z := by
      exact (congrArg (fun f : _ ⟶ V.left ↦ f w) hfst).symm.trans
        (congrArg (fun z ↦ (pullback.fst V.hom
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) z) hw)
    obtain ⟨t, _, ht⟩ := Flat.generalizingMap p.left (hw' ▸ hxz)
    exact ⟨t, ht⟩
  let : (topology (Spec (.of A))).Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful (toProEt (Spec (.of A)))
      (topology (Spec (.of A))) (ProEt.topology (Spec (.of A)))
  obtain ⟨s, hs⟩ := cover_split V hweak p hs
  have hrs : r.map s = inv (r.map p) := by
    apply (cancel_mono (r.map p)).mp
    rw [← r.map_comp, hs, r.map_id, IsIso.inv_hom_id]
  have hps : p ≫ s = 𝟙 _ := by
    apply (adj.homEquiv _ _).injective
    change adj.unit.app (r.obj V) ≫ r.map (p ≫ s) =
      adj.unit.app (r.obj V) ≫ r.map (𝟙 _)
    have hmap : r.map (p ≫ s) = r.map (𝟙 _) := by
      rw [r.map_comp, hrs, IsIso.hom_inv_id, r.map_id]
    exact congrArg (fun f ↦ adj.unit.app (r.obj V) ≫ f) hmap
  exact ⟨⟨s, hps, hs⟩⟩
end AlgebraicGeometry.Scheme.AffineProEt
