/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageComparisonMap
import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate

/-! # Bounded-below comparison in the unbounded derived category

Source: blueprint direct-image comparison, Step 9.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

section Restriction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives D] [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]

private theorem restrict_derived_adjunction (adj : f ⊣ g) :
    Adjunction.restrictFullyFaithful adj.mapDerivedCategoryRightDerivedAdjunction
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      f.mapDerivedCategoryPlusCompatibility.symm
      g.rightDerivedFunctorPlusCompatibility.symm = adj.derivedPlus := by
  apply Adjunction.ext
  apply adj.derivedPlus_unit_eq
  intro K
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, Adjunction.map_restrictFullyFaithful_unit_app]
  have h₁ := adj.mapHomotopyCategory (ComplexShape.up ℤ) |>.derivedη_fac_app
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) f.mapDerivedCategoryFactorsh.hom
    g.rightDerivedFunctorUnit K.obj
  have h₃ : g.rightDerivedFunctorPlusιUnit.app (f.mapHomotopyCategoryPlus.obj K) ≫
      g.rightDerivedFunctorPlusCompatibility.hom.app
        (DerivedCategory.Plus.Qh.obj (f.mapHomotopyCategoryPlus.obj K)) =
      g.ιRightDerivedFunctorUnit.app (f.mapHomotopyCategoryPlus.obj K) := by
    simp [Functor.rightDerivedFunctorPlusCompatibility]
  have h₄ : DerivedCategory.Plus.ι.map
      (g.rightDerivedFunctorPlusUnith.app (f.mapHomotopyCategoryPlus.obj K)) =
      g.ιRightDerivedFunctorUnit.app (f.mapHomotopyCategoryPlus.obj K) ≫
        g.rightDerivedFunctorPlusCompatibility.inv.app
          (DerivedCategory.Plus.Qh.obj (f.mapHomotopyCategoryPlus.obj K)) := by
    rw [← h₃, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have h₅ := g.rightDerivedFunctorPlusCompatibility.inv.naturality
    (f.mapDerivedCategoryPlusFactorsh.hom.app K)
  simp only [Functor.comp_map, Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app] at h₅
  have h₇ : DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K)) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app K.obj) := by
    exact congrArg DerivedCategory.Qh.map
      (Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app adj K)
  rw [h₄, h₇]
  dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app, Iso.symm_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.assoc, ← h₅, ← Category.assoc, h₁, Category.assoc]
  rfl

private theorem included_counit (adj : f ⊣ g) (K : DerivedCategory.Plus D) :
    DerivedCategory.Plus.ι.map (adj.derivedPlus.counit.app K) =
      f.mapDerivedCategory.map (g.rightDerivedFunctorPlusCompatibility.hom.app K) ≫
        adj.mapDerivedCategoryRightDerivedAdjunction.counit.app K.obj := by
  rw [← restrict_derived_adjunction adj, Adjunction.map_restrictFullyFaithful_counit_app]
  simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]
  rfl

end Restriction

namespace AlgebraicGeometry.ProEtale

private theorem included_pullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map ((fixedComparisonPullbackPlus A g).hom.app K) =
      (unboundedDirectImagePullbackIso A g).inv.app K.obj := by
  have hc : DerivedCategory.Plus.ι.mapIso
      ((Functor.mapDerivedCategoryPlusCompIso
        (Etale.upperStar (ModuleCat.{u + 1} A) g)
        (comparisonUpperStar (ModuleCat.{u + 1} A) X)).app K) =
      (Functor.mapDerivedCategoryCompIso
        (Etale.upperStar (ModuleCat.{u + 1} A) g)
        (comparisonUpperStar (ModuleCat.{u + 1} A) X)).symm.app K.obj :=
    Iso.ext (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app _ _ K)
  simp only [fixedComparisonPullbackPlus, unboundedDirectImagePullbackIso,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.map_comp]
  rw [show DerivedCategory.Plus.ι.map
      ((Functor.mapDerivedCategoryPlusCompIso
        (Etale.upperStar (ModuleCat.{u + 1} A) g)
        (comparisonUpperStar (ModuleCat.{u + 1} A) X)).inv.app K) =
      (Functor.mapDerivedCategoryCompIso
        (Etale.upperStar (ModuleCat.{u + 1} A) g)
        (comparisonUpperStar (ModuleCat.{u + 1} A) X)).hom.app K.obj from
    congrArg Iso.inv hc]
  rw [Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
    Functor.mapDerivedCategoryNatIso_symm]
  simp only [Category.assoc]
  rfl

/-- The bounded-below direct-image comparison, expressed using total unbounded derivation.
Source: blueprint `sk-prop-pe-unbounded-classical-direct-image.proof.md`, Step 9;
`theorem-comparison-direct-images` and Stacks Tag 09A6
(auxiliary; not a blueprint node).

Proof: Regard K as an object of D+ using its lower bound n. For each direct image use
rightDerivedFunctorPlusCompatibility to identify its D+ value, included into D, with
its total right derived value. Exact inverse image commutes with these inclusions.
The pullback square becomes the same square under mapDerivedCategoryPlusCompatibility.
Both derived adjunctions are normalized by the underived adjunction on resolutions:
apply the derived unit/counit factorization and uniqueness of right derived functors
on bounded-below injective resolutions. Thus the included D+ canonical mate is the
unbounded mate, conjugated by the two compatibility isomorphisms. The D+ mate is
invertible for qcqs g by isIso_comparisonDirectImageCanonicalMate. Inclusion and
conjugation preserve invertibility, proving the assertion. This argument works for
K=0, negative lower bounds, the zero coefficient ring, and empty schemes.
-/
theorem unboundedDirectImageComparison_boundedBelow
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (n : ℤ) [K.IsGE n] : IsIso (unboundedDirectImageComparisonMap A g K) := by
  let Kp : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨K, ⟨n, inferInstance⟩⟩
  let E := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g
  let P := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g
  let F := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
  let G := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let R := (Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor
  let S := (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor
  let L := (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory
  let re := (Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlusCompatibility
  let rp := (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlusCompatibility
  let b := (fixedComparisonDirectImageMatePlus A g).app Kp
  have hb : IsIso b := by
    have := isIso_fixedComparisonDirectImageMatePlus A g
    dsimp [b]
    infer_instance
  have hc := congrArg (fun z ↦ DerivedCategory.Plus.ι.map z)
    (fixedComparisonDirectImageMatePlus_counit A g Kp)
  simp only [Functor.map_comp, derivedUpperStarLowerStarAdjunctionPlus,
    Etale.derivedUpperStarLowerStarAdjunctionPlus,
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus] at hc
  change DerivedCategory.Plus.ι.map
      ((fixedComparisonPullbackPlus A g).hom.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) g).obj Kp)) ≫
      L.map (DerivedCategory.Plus.ι.map b) ≫
      DerivedCategory.Plus.ι.map (P.derivedPlus.counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj Kp)) =
      G.map (DerivedCategory.Plus.ι.map (E.derivedPlus.counit.app Kp)) at hc
  rw [included_pullback, included_counit, included_counit] at hc
  have hn := (unboundedDirectImagePullbackIso A g).hom.naturality (re.hom.app Kp)
  simp only [Functor.comp_map] at hn
  have ht : F.map (re.hom.app Kp) ≫ unboundedDirectImageComparisonMap A g K =
      DerivedCategory.Plus.ι.map b ≫ rp.hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj Kp) := by
    apply (P.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm]
    dsimp only [P]
    rw [unboundedDirectImageComparisonMap]
    simp only [F, Kp, Functor.comp_obj, ObjectProperty.ι,
      inducedFunctor, Equiv.symm_apply_apply]
    change L.map (F.map (re.hom.app Kp)) ≫
        (unboundedDirectImagePullbackIso A g).hom.app (R.obj K) ≫
          G.map (E.mapDerivedCategoryRightDerivedAdjunction.counit.app K) = _
    erw [reassoc_of% hn]
    simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
    have hc' := hc
    simp only [Functor.map_comp] at hc'
    have hh := congrArg (fun z ↦
      (unboundedDirectImagePullbackIso A g).hom.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) g).obj Kp).obj ≫ z) hc'
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] at hh
    simpa only [F, G, L, E, P, re, rp, Kp, Functor.comp_obj, Functor.comp_map,
      DerivedCategory.Plus.ι, ObjectProperty.ι, inducedFunctor, Functor.mapDerivedCategoryPlus,
      ObjectProperty.lift, ObjectProperty.homMk, Functor.id_obj,
      Etale.rightDerivedLowerStarPlus, Category.assoc] using hh.symm
  have : IsIso (F.map (re.hom.app Kp) ≫ unboundedDirectImageComparisonMap A g K) := by
    rw [ht]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map (re.hom.app Kp)) _

end AlgebraicGeometry.ProEtale
