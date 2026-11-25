/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import WeilConjectures.Algebra.Homology.DerivedHomFiniteFreeModel
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.AlgebraicGeometry.HomComplexRestrictScheme
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Local finite free computation of scalar derived Hom cohomology

Source: Stacks Project, Tag 08DL; Tag 08DM for bounded truncations.
(blueprint: lem-sc-local-finite-free-scalar-homology). -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Scheme.Modules.overEquiv Scheme.Modules.restrictFunctor
  homComplexFunctor derivedInternalHom

set_option backward.isDefEq.respectTransparency true in
/-- A finite free resolution on an open computes restricted scalar Ext, independently
of the supplied universe of the ambient derived category.

Source: Stacks Project, Tag 08DL, restriction; Tag 08DM, strictly perfect Hom
applied to bounded truncations of the bounded-above finite free model.
(blueprint: lem-sc-local-finite-free-scalar-homology).

Proof: Choose a bounded-below injective resolution I of the degree-zero structure
sheaf on Y. It is K-injective; its restriction remains bounded below and K-injective.
The representative comparison for derived internal Hom and the homology factorization
identify ambient cohomology with homology of Hom(single K,I). Restriction is exact;
restriction of I is K-injective and restriction commutes with the Hom complex.
The over-site equivalence transports these complexes to U.toScheme. The augmentation
E -> single(K|U) becomes invertible in the derived category. Compute in the standard
universe on U.toScheme, using this same restricted I: the representative comparison
and the finite free Hom model identify Hom(single(K|U),I|U) with Hom(E,O_U).
Take homology and transport back through the over-site equivalence. Since the
initial computation used a complex of module sheaves independent of the derived
universe, its homology comparison applies to the arbitrary supplied ambient universe.
The finite free model applies because E is bounded above and O_U[0] is bounded
below. Equivalently, for each fixed Hom cohomology degree only a finite truncation
of E contributes when paired with the bounded-below I; Tag 08DM applies to this
strictly perfect truncation. Thus no lower bound on E is required.
The zero resolution and empty opens are included. No affine or Koszul hypothesis
is involved in this assertion. -/
theorem local_finite_free_scalar_homology
    {Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (U : Y.Opens) (K : Y.Modules)
    (E : CochainComplex U.toScheme.Modules ℤ)
    (hbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p))
    (hfree : ∀ p : ℤ, ∃ r : ℕ, Nonempty (E.X p ≅
      SheafOfModules.free (R := moduleRings U.toScheme.toRingedSpace)
        (ULift.{u} (Fin r))))
    (ε : E ⟶ (CochainComplex.singleFunctor U.toScheme.Modules 0).obj
      ((Scheme.Modules.restrictFunctor U.ι).obj K)) [QuasiIso ε] (q : ℤ) :
    let F : Y.Modules := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) q).obj
        ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj K),
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                (SheafOfModules.unit Y.ringCatSheaf)))
    Nonempty (F.over U ≅ (Scheme.Modules.overEquiv U).inverse.obj
      ((homComplex (R := U.toScheme.toRingedSpace.sheaf) E
        ((CochainComplex.singleFunctor U.toScheme.Modules 0).obj
          (SheafOfModules.unit U.toScheme.ringCatSheaf))).homology q)) := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let O := SheafOfModules.overFunctor.{u} Y.ringCatSheaf U
  let T := (Scheme.Modules.overEquiv U).functor
  let : PreservesFiniteLimits O := moduleOverFunctor_limits Y.toRingedSpace U
  let : PreservesFiniteColimits O := moduleOverFunctor_colimits Y.toRingedSpace U
  let : PreservesFiniteLimits (O ⋙ T) := comp_preservesFiniteLimits O T
  let : PreservesFiniteColimits (O ⋙ T) := comp_preservesFiniteColimits O T
  let : T.Additive := T.additive_of_preserves_binary_products
  let R := O ⋙ T
  have hRAdd : R.Additive := R.additive_of_preserves_binary_products
  let eR : R ≅ Scheme.Modules.restrictFunctor U.ι := Scheme.Modules.overFunctorEquiv U
  have hRestrAdd : (Scheme.Modules.restrictFunctor U.ι).Additive :=
    @Functor.additive_of_iso _ _ _ _ _ _ R hRAdd _ eR
  have hRestrZero : (Scheme.Modules.restrictFunctor U.ι).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ hRestrAdd
  have hRZero : R.PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ R hRAdd
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let eRc := @NatIso.mapHomologicalComplex ℤ _ _ _ _ _ _ R
    (Scheme.Modules.restrictFunctor U.ι) hRZero hRestrZero eR (.up ℤ)
  let L := (CochainComplex.singleFunctor A 0).obj K
  let M := (CochainComplex.singleFunctor A 0).obj (SheafOfModules.unit Y.ringCatSheaf)
  obtain ⟨I, η, hη, _, _, hI⟩ := SheafOfModules.exists_boundedBelow_injective_resolution
    (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf M ⟨0, inferInstance⟩
  let : QuasiIso η := hη
  let : I.IsKInjective := hI
  let eI : DerivedCategory.Q.obj I ≅ (DerivedCategory.singleFunctor A 0).obj
      (SheafOfModules.unit Y.ringCatSheaf) := (asIso (DerivedCategory.Q.map η)).symm
  let DY := (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
    (op ((DerivedCategory.singleFunctor A 0).obj K),
      (DerivedCategory.singleFunctor A 0).obj (SheafOfModules.unit Y.ringCatSheaf))
  obtain ⟨eY⟩ := derivedInternalHom_obj_iso.{u, w} (Opens.grothendieckTopology Y)
    Y.toRingedSpace.sheaf ((DerivedCategory.singleFunctor A 0).obj K)
    ((DerivedCategory.singleFunctor A 0).obj (SheafOfModules.unit Y.ringCatSheaf))
    L I (Iso.refl _) eI
  let : (Scheme.Modules.overEquiv U).symm.functor.Additive :=
    (Scheme.Modules.overEquiv U).symm.functor.additive_of_preserves_binary_products
  let : T.PreservesKInjectiveComplexes :=
    (Scheme.Modules.overEquiv U).symm.toAdjunction.preservesKInjectiveComplexes
  let : CochainComplex.IsKInjective ((O.mapHomologicalComplex (.up ℤ)).obj I) :=
    kInjective_of_restrict_open Y.toRingedSpace U I
  let : CochainComplex.IsKInjective ((T.mapHomologicalComplex (.up ℤ)).obj
      ((O.mapHomologicalComplex (.up ℤ)).obj I)) := inferInstance
  have hRcKI : CochainComplex.IsKInjective (Rc.obj I) :=
    CochainComplex.isKInjective_of_iso (L₁ := (T.mapHomologicalComplex (.up ℤ)).obj
      ((O.mapHomologicalComplex (.up ℤ)).obj I))
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (O ⋙ T)) (.up ℤ)).app I)
  let B := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
  let : HasDerivedCategory.{u + 1} B := HasDerivedCategory.standard B
  let QU := @DerivedCategory.Q B _ _ (HasDerivedCategory.standard B)
  let KU := (CochainComplex.singleFunctor B 0).obj
    ((Scheme.Modules.restrictFunctor U.ι).obj K)
  let GU := (CochainComplex.singleFunctor B 0).obj
    (SheafOfModules.unit U.toScheme.ringCatSheaf)
  let eL : Rc.obj L ≅ KU :=
    (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app K ≪≫
      (CochainComplex.singleFunctor B 0).mapIso (eR.app K)
  let eM : Rc.obj M ≅ GU :=
    (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app _ ≪≫
      (CochainComplex.singleFunctor B 0).mapIso
        (eR.app _ ≪≫ Scheme.Modules.restrictUnitIso U.ι)
  have hRcη : QuasiIso (Rc.map η) := inferInstance
  let : IsIso (QU.map (Rc.map η)) :=
    (@DerivedCategory.isIso_Q_map_iff_quasiIso B _ _ (HasDerivedCategory.standard B)
      _ _ (Rc.map η)).mpr hRcη
  let eIU : QU.obj (Rc.obj I) ≅ QU.obj GU :=
    (asIso (QU.map (Rc.map η))).symm ≪≫ QU.mapIso eM
  obtain ⟨eU⟩ := @derivedInternalHom_obj_iso.{u, u + 1}
    (TopologicalSpace.Opens U.toScheme) _ (Opens.grothendieckTopology U.toScheme)
    U.toScheme.toRingedSpace.sheaf (HasDerivedCategory.standard B) (QU.obj KU) (QU.obj GU)
    (Rc.obj L) (Rc.obj I) hRcKI (QU.mapIso eL) eIU
  have hε : QuasiIso ε := inferInstance
  obtain ⟨eE⟩ := @derivedInternalHom_of_boundedAbove_finiteFree.{u, u + 1}
    U.toScheme.toRingedSpace (HasDerivedCategory.standard B) E GU KU hbounded hfree
    ⟨0, fun i hi ↦
      HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i (ne_of_lt hi)⟩ ε hε
  obtain ⟨eC⟩ := homComplex_restrict_scheme U L I
  let changeInputs := (Functor.uncurry.obj
    (homComplexFunctor (R := U.toScheme.toRingedSpace.sheaf))).mapIso
      ((eRc.app L).op.prod
        (eRc.app I).symm)
  let H := homComplex (R := Y.toRingedSpace.sheaf) L I
  let HY := DerivedCategory.homologyFunctor A q
  let HU := @DerivedCategory.homologyFunctor B _ _ (HasDerivedCategory.standard B) q
  let fU := @DerivedCategory.homologyFunctorFactors B _ _ (HasDerivedCategory.standard B) q
  let eH : R.obj (HY.obj DY) ≅
      (homComplex (R := U.toScheme.toRingedSpace.sheaf) E GU).homology q :=
    R.mapIso (HY.mapIso eY ≪≫ (DerivedCategory.homologyFunctorFactors A q).app H) ≪≫
      ((R.mapHomologicalComplexHomologyIso (.up ℤ) q).app H).symm ≪≫
      (HomologicalComplex.homologyFunctor B (.up ℤ) q).mapIso
        (eRc.app H ≪≫ eC ≪≫ changeInputs) ≪≫
      (fU.app _).symm ≪≫
      HU.mapIso (eU.symm ≪≫ eE.symm) ≪≫
      fU.app _
  exact ⟨(Scheme.Modules.overEquiv U).unitIso.app ((HY.obj DY).over U) ≪≫
    (Scheme.Modules.overEquiv U).inverse.mapIso
      eH⟩

end AlgebraicGeometry
