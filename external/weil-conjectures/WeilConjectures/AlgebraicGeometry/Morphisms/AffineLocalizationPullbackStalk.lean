/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.Localization

/-! # Points and stalks of a coefficient-localized cartesian square -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A scheme base change along an affine localization preserves the stalk of every
point whose image avoids the denominators. -/
theorem exists_lift_stalkEquiv_of_isLocalization
    (R S : CommRingCat.{u}) [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    {X Y : Scheme.{u}} (c : Y ⟶ X) (f : Y ⟶ Spec S) (g : X ⟶ Spec R)
    (hsq : IsPullback c f g (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (x : X) (hx : Disjoint (M : Set R) ((g x).asIdeal : Set R)) :
    ∃ x0 : Y, c x0 = x ∧
      ∃ e : Y.presheaf.stalk x0 ≃+* X.presheaf.stalk x,
        ∀ r : R,
          e ((f.stalkMap x0).hom
            (StructureSheaf.toStalk S (f x0) (algebraMap R S r))) =
              (g.stalkMap x).hom (StructureSheaf.toStalk R (g x) r) := by
  -- A flat preimmersion has bijective stalk maps: surjectivity and faithful flatness.
  have hloc : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    IsPreimmersion.of_isLocalization M
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S M))
  have hc : IsPreimmersion c := MorphismProperty.of_isPullback hsq.flip hloc
  have hcf : Flat c := MorphismProperty.of_isPullback hsq.flip hflat
  have hrange : g x ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
    rw [PrimeSpectrum.localization_comap_range S M]
    exact hx
  obtain ⟨s, hs⟩ := hrange
  obtain ⟨x0, hx0, _⟩ := exists_preimage_of_isPullback hsq x s hs.symm
  subst x
  have hinj : Function.Injective (c.stalkMap x0).hom := by
    algebraize [(c.stalkMap x0).hom]
    have : Module.FaithfullyFlat (X.presheaf.stalk (c x0)) (Y.presheaf.stalk x0) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap c x0) (c.toLRSHom.prop x0)
    exact ‹RingHom.FaithfullyFlat _›.injective
  let e := (RingEquiv.ofBijective (c.stalkMap x0).hom
    ⟨hinj, c.stalkMap_surjective x0⟩).symm
  refine ⟨x0, rfl, e, ?_⟩
  intro r
  apply e.symm.injective
  simp only [RingEquiv.symm_apply_apply]
  change (f.stalkMap x0).hom
    (StructureSheaf.toStalk S (f x0) (algebraMap R S r)) =
      (c.stalkMap x0).hom ((g.stalkMap (c x0)).hom
        (StructureSheaf.toStalk R (g (c x0)) r))
  have hcomp := Hom.stalkMap_congr_hom (c ≫ g)
    (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) hsq.w x0
  rw [Hom.stalkMap_comp, Hom.stalkMap_comp] at hcomp
  have hpoint : g (c x0) =
      PrimeSpectrum.comap (algebraMap R S) (f x0) := by
    exact congrArg (fun k : Y ⟶ Spec R => k x0) hsq.w
  have htransport : StructureSheaf.toStalk R (g (c x0)) ≫
      ((Spec R).presheaf.stalkCongr (.of_eq hpoint)).hom =
        StructureSheaf.toStalk R (PrimeSpectrum.comap (algebraMap R S) (f x0)) := by
    generalize g (c x0) = p at hpoint ⊢
    generalize PrimeSpectrum.comap (algebraMap R S) (f x0) = q at hpoint ⊢
    subst q
    simp [TopCat.Presheaf.stalkCongr]
    rfl
  have hcompat : StructureSheaf.toStalk R (g (c x0)) ≫
      g.stalkMap (c x0) ≫ c.stalkMap x0 =
        CommRingCat.ofHom (algebraMap R S) ≫
          StructureSheaf.toStalk S (f x0) ≫ f.stalkMap x0 := by
    rw [hcomp, ← Category.assoc, ← Category.assoc, htransport]
    have hspec : StructureSheaf.toStalk R
        (PrimeSpectrum.comap (algebraMap R S) (f x0)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap (f x0) =
            CommRingCat.ofHom (algebraMap R S) ≫ StructureSheaf.toStalk S (f x0) :=
      stalkMap_toStalk (CommRingCat.ofHom (algebraMap R S)) (f x0)
    rw [hspec, Category.assoc]
  exact (DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hcompat) r).symm

end AlgebraicGeometry.Scheme
