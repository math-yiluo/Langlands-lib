/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import all WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleDirectScalarProjection
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarProjection
import WeilConjectures.AlgebraicGeometry.Etale.EtaleDirectImageScalarComposition
import WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarExchange
import WeilConjectures.AlgebraicGeometry.Etale.EtaleDirectImageScalarExchange
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackUnitCoherence
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientLeftUnitCoherence

import all WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientMate
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-!
# Scalar coherence for ordinary etale compact support

Source: Stacks Project, more-etale.tex, Tag 0GL6, with Tags 0F7I, 0F7J and 0F7L;
sites-cohomology.tex, Tags 07A4, 0GL1 and 0E48
(blueprint: lem-pur-etale-compact-scalar-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

private noncomputable abbrev scalarSheafMonoidal
    (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    MonoidalCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) := inferInstance

attribute [local instance 2000] scalarSheafMonoidal
attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
  cachedEtaleMonoidalPreadditive cachedEtaleCoproducts cachedEtaleColimits
  cachedEtaleFlatResolution cachedEtaleInjectiveResolution cachedEtaleExactColimits
  cachedEtaleTensor4 cachedEtaleTensor12 cachedEtaleTensor23
  cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

/-- The inverse of the published open balancing map has the specified open-unit transpose.
Source: Stacks 07A4, 0GL1 and 0GL6
(blueprint: lem-pur-etale-compact-scalar-coherence).
Proof: regard each exact open adjunction as an adjunction to the left-derived
pullback by transporting its right adjoint along the canonical exact-pullback comparison.
The published open comparison is a conjugate under the two composite adjunctions.
The iterated-mate identity identifies its inverse with the open mate of the inverse
scalar-restriction mate. The existing scalarPullback_eq identifies that inner mate with
the inverse of the normalized scalar/pullback comparison. The mate's unit equation
therefore computes its open-adjunction transpose. Naturality of the exact-pullback
comparison transports this equation back to the published exact open adjunction;
cancellation of its inverse and forward components yields exactly the transpose defining
properOpenCoefficientOpenInverse. Injectivity of the open adjunction's Hom equivalence
proves equality. This works without finite coefficients or boundedness. -/
theorem compactScalarOpen_normalization (φ : A →+* B) {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (M : DerivedCategoryModule A U) :
    (ExceptionalCoefficients.openIso φ j).inv.app M =
      properOpenCoefficientOpenInverse φ j M := by
  let a := (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm
  let b := (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).symm
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
  let u := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let α := (mateEquiv x u).symm
    (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ j).hom)
  have he : α = (scalarPullbackIso φ j).inv := by
    exact congrArg Iso.inv
      (ProEtale.scalarPullbackEtaleIso_eq_fromMate φ j).symm
  have h := 
    (iterated_mateEquiv_conjugateEquiv_symm a b u x
      (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ j).hom))
  change ((mateEquiv a b).symm α) = (ExceptionalCoefficients.openIso φ j).inv at h
  have ht := unit_mateEquiv_symm a b α M
  change (scalarExtension φ U).map (a.unit.app M) ≫ α.app _ =
    b.unit.app _ ≫ (upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.map
      (((mateEquiv a b).symm α).app M) at ht
  rw [h] at ht
  rw [he] at ht
  apply ((derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) j).homEquiv _ _).injective
  unfold properOpenCoefficientOpenInverse
  dsimp only [Functor.comp_obj]
  rw [Equiv.apply_symm_apply]
  simp only [Adjunction.homEquiv_unit]
  have htransport := congrArg (fun z ↦ z ≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).hom.app
      ((scalarExtension φ T).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M))) ht.symm
  simp only [a, b, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.comp_obj, Functor.map_comp,
    Category.assoc] at htransport
  erw [(leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} B) j).hom.naturality
      ((ExceptionalCoefficients.openIso φ j).inv.app M)] at htransport
  dsimp only [Functor.comp_obj] at htransport
  erw [Iso.inv_hom_id_app_assoc] at htransport
  simpa only [scalarExtension, ProEtale.pbcFixedScalarExtension,
    properOpenCoefficientPullbackIso, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using htransport

-- Compare inverses by their prescribed open-unit transposes.
private theorem compactScalarOpen_eq (φ : A →+* B) {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] :
    ExceptionalCoefficients.openIso φ j = openScalarExtension φ j := by
  suffices h : (ExceptionalCoefficients.openIso φ j).symm =
      (openScalarExtension φ j).symm from congrArg Iso.symm h
  apply Iso.ext
  ext M
  change (ExceptionalCoefficients.openIso φ j).inv.app M =
    (openScalarExtension φ j).inv.app M
  rw [compactScalarOpen_normalization]
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  apply (adj.homEquiv _ _).injective
  unfold properOpenCoefficientOpenInverse
  rw [Equiv.apply_symm_apply]
  simpa only [Adjunction.homEquiv_unit, adj] using (scalarOpen_unit φ j M).symm

-- The unit-mate argument also applies to an arbitrary specified cartesian open square.
private theorem compactScalarOpen_exchange
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U U' T T' : Scheme.{u}} {j : U ⟶ T} [IsOpenImmersion j]
    {g : T' ⟶ T} {h : U' ⟶ U} {j' : U' ⟶ T'} [IsOpenImmersion j']
    (sq : IsPullback h j' j g) (M : DerivedCategoryModule A U) :
    (upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory.map
        ((openScalarExtension φ j).hom.app M) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} B) sq).inv.app
          ((scalarExtension φ U).obj M) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j').mapDerivedCategory.map
          ((properOpenCoefficientPullbackIso φ h).hom.app M) =
    (properOpenCoefficientPullbackIso φ g).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
      (scalarExtension φ T').map
        ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} A) sq).inv.app M) ≫
      (openScalarExtension φ j').hom.app
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M) := by
  set_option backward.isDefEq.respectTransparency true in
    let LA := (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
    let LB' := (openImmersionLowerShriek (ModuleCat.{u + 1} B) j').mapDerivedCategory
    let GB := (upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory
    let HA := (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory
    let Q' := scalarExtension φ T'
    let S := scalarExtension φ U
    let dA := mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} A) sq
    let dB := mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} B) sq
    let cA := Functor.mapDerivedCategorySquareIso
      (openImmersionSquareIso (ModuleCat.{u + 1} A) sq.toCommSq)
    let cB := Functor.mapDerivedCategorySquareIso
      (openImmersionSquareIso (ModuleCat.{u + 1} B) sq.toCommSq)
    have hi := mate_cube
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j')
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j')
      (openScalarExtension φ j) (openScalarExtension φ j') dA dB
      (properOpenCoefficientPullbackIso φ j) (properOpenCoefficientPullbackIso φ j')
      (properOpenCoefficientPullbackIso φ h) (properOpenCoefficientPullbackIso φ g) cA cB
      (scalarOpen_unit φ j) (scalarOpen_unit φ j')
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso_mate _ sq)
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso_mate _ sq)
      (scalarPullback_square φ h j' j g sq.toCommSq) M
    let l := LB'.mapIso ((properOpenCoefficientPullbackIso φ h).symm.app M) ≪≫
      dB.app (S.obj M) ≪≫ GB.mapIso ((openScalarExtension φ j).symm.app M)
    let r := (openScalarExtension φ j').symm.app (HA.obj M) ≪≫
      Q'.mapIso (dA.app M) ≪≫ (properOpenCoefficientPullbackIso φ g).symm.app (LA.obj M)
    have he : l.hom = r.hom := hi
    have hinv := congrArg Iso.inv (Iso.ext he)
    simpa only [l, r, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv,
      Category.assoc] using hinv

/-- Naturality of the published proper/open scalar components.
Source: Stacks 0GL6 (blueprint: lem-pur-etale-compact-scalar-coherence).
Proof: expand compactSupportMap. Naturality of scalarMate moves the open-extension
map past the proper scalar component. Naturality of openIso moves it past the open
component. Functoriality of proper direct image gives the displayed equality. -/
theorem compactScalarMap_naturality (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) {M N : DerivedCategoryModule A X} (a : M ⟶ N) :
    (scalarExtension φ Y).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map a) ≫
        ExceptionalCoefficients.compactSupportMap φ c N =
      ExceptionalCoefficients.compactSupportMap φ c M ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
          ((scalarExtension φ X).map a) := by
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
  let R := (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor
  change (scalarExtension φ Y).map
      ((lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map (J.map a)) ≫
      (scalarMate φ c.g).app (J.obj N) ≫ R.map ((ExceptionalCoefficients.openIso φ c.i).hom.app N) =
    ((scalarMate φ c.g).app (J.obj M) ≫ R.map
      ((ExceptionalCoefficients.openIso φ c.i).hom.app M)) ≫
        R.map ((openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.map
          ((scalarExtension φ X).map a))
  have h := (scalarMate φ c.g).naturality (J.map a)
  dsimp only [Functor.comp_map] at h
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  rw [← R.map_comp, ← R.map_comp]
  congr 1
  have h' := (ExceptionalCoefficients.openIso φ c.i).hom.naturality a
  dsimp only [Functor.comp_map] at h'
  exact congrArg R.map h'

/-- Package the published proper/open scalar components as a natural transformation.
Source: Stacks 0GL6 (blueprint: lem-pur-etale-compact-scalar-coherence). -/
def compactScalarMap (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        scalarExtension φ Y ⟶ scalarExtension φ X ⋙
          rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c where
  app := ExceptionalCoefficients.compactSupportMap φ c
  naturality _ _ a := compactScalarMap_naturality φ c a

/-- The proper-counit/open-tensor projection, in coefficient-first order.
Source: Stacks 0GL6, preceding projection lemma
(blueprint: lem-pur-etale-compact-scalar-coherence). -/
def compactScalarProjection (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule R Y) (M : DerivedCategoryModule R X) :
    ((derivedTensor (ModuleCat.{u + 1} R) Y).obj K).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj M) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj
        (((derivedTensor (ModuleCat.{u + 1} R) X).obj
          ((upperStar (ModuleCat.{u + 1} R) f).leftDerivedFunctor.obj K)).obj M) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Y).hom.app K).app
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj M) ≫
    ((projectionMapOfCompactification (ModuleCat.{u + 1} R) c).app M).app K ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app M).app
        ((upperStar (ModuleCat.{u + 1} R) f).leftDerivedFunctor.obj K))

private theorem compactScalarMap_isIso
    [Finite A] [Finite B] (φ : A →+* B) {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) (M : DerivedCategoryModule A X) :
    IsIso ((compactScalarMap φ c).app M) := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have := (properFiniteCoefficientExtension φ c.g).1
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)
  change IsIso ((scalarMate φ c.g).app _ ≫
    (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
      ((ExceptionalCoefficients.openIso φ c.i).hom.app M))
  infer_instance

/-- Scalar identification of the target of the ordered projection map.
Source: Stacks 07A4 (blueprint: lem-pur-etale-compact-scalar-coherence). -/
def compactScalarProjectionTarget (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategoryModule A Y) (M : DerivedCategoryModule A X) :
    (scalarExtension φ X).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).obj M) ⟶
      ((derivedTensor (ModuleCat.{u + 1} B) X).obj
        ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
          ((scalarExtension φ Y).obj K))).obj ((scalarExtension φ X).obj M) :=
  (ExceptionalCoefficients.tensorIso φ X).hom.app
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K, M) ≫
    ((derivedTensor (ModuleCat.{u + 1} B) X).map
      ((scalarPullbackIso φ f).inv.app K)).app ((scalarExtension φ X).obj M)

/-- The specified scalar map for the chosen compactification.
Source: Stacks 0GL6 (blueprint: lem-pur-etale-compact-scalar-coherence). -/
def compactScalarChosenMap (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] :=
  compactScalarMap φ (HasCompactification.compactification f)

-- Paste proper exchange with open exchange, using naturality of both proper maps.
private theorem compact_scalar_exchange_raw
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {h : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback h f' f g) (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory.map
        ((compactScalarMap φ c).app M) ≫
      (unboundedEtaleCompactSupportExchange B sq c).app ((scalarExtension φ X).obj M) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B)
        (c.ofIsPullback sq)).map ((properOpenCoefficientPullbackIso φ h).hom.app M) =
      (properOpenCoefficientPullbackIso φ g).hom.app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ≫
      (scalarExtension φ Y').map ((unboundedEtaleCompactSupportExchange A sq c).app M) ≫
      (compactScalarMap φ (c.ofIsPullback sq)).app
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M) := by
  let psq : ChosenCartesianSquare (pullback.fst c.g g) (pullback.snd c.g g) c.g g :=
    { toCommSq := (IsPullback.of_hasPullback c.g g).toCommSq
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  have hp := exactDerivedBaseChangeMap_scalarExtension φ _ _ _ _ psq
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)
  have ho := compactScalarOpen_exchange φ (c.isPullback_i_ofIsPullback sq) M
  rw [← compactScalarOpen_eq, ← compactScalarOpen_eq] at ho
  have hn := (exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) psq.toCommSq).naturality
    ((ExceptionalCoefficients.openIso φ c.i).hom.app M)
  have hm := (scalarMate φ (c.ofIsPullback sq).g).naturality
    ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} A) (c.isPullback_i_ofIsPullback sq)).inv.app M)
  simp only [unboundedEtaleCompactSupport_exchange_normalization,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  dsimp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    rightDerivedLowerShriekOfCompactification, Functor.comp_map, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hm
  dsimp only [Compactification.ofIsPullback, rightDerivedLowerStar] at ho hm hp hn ⊢
  erw [reassoc_of% hn]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  erw [ho]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hp, reassoc_of% hm]

private theorem scalarMate_directImage_composition_eq
    [Finite A] [Finite B] (φ : A →+* B) {X Y Z : Scheme.{u}}
    (r : X ⟶ Y) (s : Y ⟶ Z) (t : X ⟶ Z) (h : t = r ≫ s)
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ Z).map
        ((Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) r)
          (lowerStar (ModuleCat.{u + 1} A) s)
          (lowerStarComp (ModuleCat.{u + 1} A) r s t h)).hom.app M) ≫
      (scalarMate φ t).app M =
    (scalarMate φ s).app ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj M) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) s).map ((scalarMate φ r).app M) ≫
      (Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} B) r)
        (lowerStar (ModuleCat.{u + 1} B) s)
        (lowerStarComp (ModuleCat.{u + 1} B) r s t h)).hom.app
          ((scalarExtension φ X).obj M) := by
  subst h
  apply (cancel_mono ((Functor.rightDerivedFunctorCompIso'
    (lowerStar (ModuleCat.{u + 1} B) r) (lowerStar (ModuleCat.{u + 1} B) s)
    (lowerStarComp (ModuleCat.{u + 1} B) r s)).inv.app
      ((scalarExtension φ X).obj M))).1
  rw [Category.assoc, scalarMate_directImage_composition]
  simp only [Category.assoc, Iso.hom_inv_id_app,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    _root_.CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [rightDerivedLowerStar, Functor.comp_obj, Category.comp_id]

private theorem refinement_transpose_normalization
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J₁ : C ⥤ D) (U₁ : D ⥤ C) (J₂ : C ⥤ E) (U₂ : E ⥤ C)
    (L : E ⥤ D) (R : D ⥤ E) (a₁ : J₁ ⊣ U₁) (a₂ : J₂ ⊣ U₂) (a : L ⊣ R)
    (k : U₂ ≅ L ⋙ U₁) (b : J₁ ≅ J₂ ⋙ L)
    (hb : ∀ K, a₁.unit.app K ≫ U₁.map (b.hom.app K) =
      a₂.unit.app K ≫ k.hom.app (J₂.obj K)) (K : C) :
    a₂.homEquiv _ _ (a.unit.app (J₂.obj K) ≫ R.map (b.inv.app K)) ≫
      k.hom.app (R.obj (J₁.obj K)) ≫ U₁.map (a.counit.app (J₁.obj K)) =
        a₁.unit.app K := by
  have hn := k.hom.naturality (R.map (b.inv.app K))
  have hu := k.hom.naturality (a.unit.app (J₂.obj K))
  dsimp only [Functor.comp_map] at hn hu
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hu, ← reassoc_of% (hb K)]
  simp only [← U₁.map_comp_assoc]
  have ht : b.hom.app K ≫ L.map (a.unit.app (J₂.obj K)) ≫
      L.map (R.map (b.inv.app K)) ≫ a.counit.app (J₁.obj K) = 𝟙 _ := by
    have hc := a.counit.naturality (b.inv.app K)
    dsimp only [Functor.comp_map, Functor.id_map] at hc
    rw [hc]
    calc
      _ = b.hom.app K ≫ 𝟙 _ ≫ b.inv.app K := by
        simpa only [Functor.comp_obj, Category.assoc] using congrArg
          (fun z ↦ b.hom.app K ≫ z ≫ b.inv.app K)
          (a.left_triangle_components (J₂.obj K))
      _ = 𝟙 _ := by rw [Category.id_comp, Iso.hom_inv_id_app]
  rw [← U₁.map_comp, Category.assoc, Category.assoc, ht,
    _root_.CategoryTheory.Functor.map_id, Category.comp_id]

private theorem refinement_open_comparison_eq
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hp : IsPullback c.i (𝟙 X) r.hom d.i)
    (M : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) r.hom).unit.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) d.i).mapDerivedCategory.obj M.obj) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} R) r.hom).map
        ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} R) r hp).inv.app
          M.obj) = properOpenComparisonAmbient R r.hom c.i d.i r.i_hom M := by
  have hn := refinementRestriction_normalization R r.hom c.i d.i r.i_hom M
  have := hn.2
  apply ((derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} R) d.i).homEquiv _ _).injective
  apply (cancel_mono ((refinementRestriction R r.hom c.i d.i r.i_hom).app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.obj M.obj))).1
  rw [hn.1]
  simpa only [refinementRestriction, upperStarCompIso_eq, Functor.mapDerivedCategoryTriangleIso,
    Functor.id_obj, rightDerivedLowerStar, mapDerivedUpperStarLowerStarAdjunction_eq] using
    refinement_transpose_normalization
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory
      (upperStar (ModuleCat.{u + 1} R) c.i).mapDerivedCategory
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) d.i).mapDerivedCategory
      (upperStar (ModuleCat.{u + 1} R) d.i).mapDerivedCategory
      (upperStar (ModuleCat.{u + 1} R) r.hom).mapDerivedCategory
      (rightDerivedLowerStar (ModuleCat.{u + 1} R) r.hom)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) c.i)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) d.i)
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) r.hom)
      (Functor.mapDerivedCategoryTriangleIso
        (upperStarCompIso (ModuleCat.{u + 1} R) c.i r.hom d.i r.i_hom))
      (refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} R) r hp)
      (unit_map_refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} R) r hp) M.obj

private theorem compactScalar_refinement
    [Finite A] [Finite B] (φ : A →+* B) {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hp : IsPullback c.i (𝟙 X) r.hom d.i)
    (M : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hQ : _root_.DerivedCategory.TStructure.t.plus ((scalarExtension φ X).obj M.obj)) :
    (scalarExtension φ Y).map
        ((rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A)
          r hp).app M.obj) ≫ (compactScalarMap φ c).app M.obj =
      (compactScalarMap φ d).app M.obj ≫
        (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} B)
          r hp).app ((scalarExtension φ X).obj M.obj) := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have : IsNoetherian d.Z := ⟨⟩
  let αA := properOpenComparisonAmbient A r.hom c.i d.i r.i_hom M
  let αB := properOpenComparisonAmbient B r.hom c.i d.i r.i_hom
    ⟨(scalarExtension φ X).obj M.obj, hQ⟩
  let kA := Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) r.hom)
    (lowerStar (ModuleCat.{u + 1} A) d.g) (refinementLowerStarComp (ModuleCat.{u + 1} A) r)
  let kB := Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} B) r.hom)
    (lowerStar (ModuleCat.{u + 1} B) d.g) (refinementLowerStarComp (ModuleCat.{u + 1} B) r)
  have heA : (rightDerivedLowerShriekOfCompactificationComparison
      (ModuleCat.{u + 1} A) r hp).app M.obj =
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) d.g).map αA ≫
        kA.hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M.obj) := by
    simp only [rightDerivedLowerShriekOfCompactificationComparison, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
      ← Functor.map_comp_assoc]
    dsimp only [αA, αB, kA, kB]
    congr 2
    exact refinement_open_comparison_eq A r hp M
  have heB : (rightDerivedLowerShriekOfCompactificationComparison
      (ModuleCat.{u + 1} B) r hp).app ((scalarExtension φ X).obj M.obj) =
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) d.g).map αB ≫
        kB.hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.obj
            ((scalarExtension φ X).obj M.obj)) := by
    simp only [rightDerivedLowerShriekOfCompactificationComparison, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
      ← Functor.map_comp_assoc]
    dsimp only [αA, αB, kA, kB]
    congr 2
    exact refinement_open_comparison_eq B r hp ⟨_, hQ⟩
  have ho := properOpenComparison_coefficient_refinement φ r.hom c.i d.i r.i_hom M hQ
  have hc (N : DerivedCategoryModule A c.Z) :
      (scalarExtension φ Y).map (kA.hom.app N) ≫ (scalarMate φ c.g).app N =
        (scalarMate φ d.g).app ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r.hom).obj N) ≫
          (rightDerivedLowerStar (ModuleCat.{u + 1} B) d.g).map ((scalarMate φ r.hom).app N) ≫
          kB.hom.app ((scalarExtension φ c.Z).obj N) := by
    dsimp only [kA, kB]
    rw [refinementLowerStarComp_eq, refinementLowerStarComp_eq]
    exact scalarMate_directImage_composition_eq φ r.hom d.g c.g r.hom_g.symm N
  dsimp only [rightDerivedLowerStar] at *
  rw [heA, heB]
  dsimp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    rightDerivedLowerShriekOfCompactification, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc]
  have hn := (scalarMate φ d.g).naturality αA
  dsimp only [Functor.comp_map, rightDerivedLowerStar] at hn
  erw [reassoc_of% hn]
  have hk := kB.hom.naturality ((ExceptionalCoefficients.openIso φ c.i).hom.app M.obj)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hk
  erw [← hk]
  simp only [← Functor.map_comp_assoc]
  have heq {T : Scheme.{u}} (j : X ⟶ T) [IsOpenImmersion j] :
      (ExceptionalCoefficients.openIso φ j).hom.app M.obj =
        (properOpenCoefficientOpenIso φ j M.obj).hom := by
    have h : ((ExceptionalCoefficients.openIso φ j).app M.obj).symm =
        (properOpenCoefficientOpenIso φ j M.obj).symm := by
      apply Iso.ext
      exact compactScalarOpen_normalization φ j M.obj
    exact congrArg (fun e ↦ e.inv) h
  rw [heq c.i, heq d.i]
  dsimp only [αA, αB]
  exact congrArg (fun z ↦ (scalarMate φ d.g).app _ ≫
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) d.g).map z ≫
      kB.hom.app _) ho

private theorem compactScalar_compactification_comparison
    [Finite A] [Finite B] (φ : A →+* B) {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (M : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hQ : _root_.DerivedCategory.TStructure.t.plus ((scalarExtension φ X).obj M.obj)) :
    (scalarExtension φ Y).map
        ((rightDerivedLowerShriekOfCompactificationIso A c d).hom.app M.obj) ≫
      (compactScalarMap φ d).app M.obj =
      (compactScalarMap φ c).app M.obj ≫
        (rightDerivedLowerShriekOfCompactificationIso B c d).hom.app
          ((scalarExtension φ X).obj M.obj) := by
  have h₁ := compactScalar_refinement φ (Compactification.infFst c d)
    (Compactification.isPullback_infFst c d) M hQ
  have h₂ := compactScalar_refinement φ (Compactification.infSnd c d)
    (Compactification.isPullback_infSnd c d) M hQ
  simp only [rightDerivedLowerShriekOfCompactificationIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, asIso_hom]
  apply (cancel_mono ((rightDerivedLowerShriekOfCompactificationComparison
    (ModuleCat.{u + 1} B) (Compactification.infSnd c d)
      (Compactification.isPullback_infSnd c d)).app
        ((scalarExtension φ X).obj M.obj))).1
  simp only [Category.assoc, asIso_inv, NatIso.isIso_inv_app, IsIso.inv_hom_id, Category.comp_id]
  rw [← h₂]
  simp only [← Functor.map_comp_assoc, IsIso.inv_hom_id,
    _root_.CategoryTheory.Functor.map_id, Category.id_comp]
  exact h₁

private theorem exact_open_preserves_plus
    (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j]
    (M : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    _root_.DerivedCategory.TStructure.t.plus
      ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj M.obj) := by
  let F := openImmersionLowerShriek (ModuleCat.{u + 1} R) j
  exact _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
    (F.mapDerivedCategoryPlusCompatibility.app M) (F.mapDerivedCategoryPlus.obj M).property

private theorem compactification_preserves_plus
    (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (M : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    _root_.DerivedCategory.TStructure.t.plus
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj M.obj) := by
  let J := openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i
  let R := lowerStar (ModuleCat.{u + 1} R) c.g
  let N := J.mapDerivedCategoryPlus.obj M
  have hn := (R.rightDerivedFunctorPlus.obj N).property
  let e := R.rightDerivedFunctorPlusCompatibility.app N ≪≫
    R.rightDerivedFunctor.mapIso (J.mapDerivedCategoryPlusCompatibility.app M)
  exact _root_.DerivedCategory.TStructure.t.plus.prop_of_iso e hn

private theorem scalar_open_preserves_plus
    (φ : A →+* B) {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hQ : _root_.DerivedCategory.TStructure.t.plus ((scalarExtension φ X).obj M.obj)) :
    _root_.DerivedCategory.TStructure.t.plus
      ((scalarExtension φ Y).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M.obj)) := by
  exact _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
    ((openScalarExtension φ j).app M.obj).symm
    (exact_open_preserves_plus B j ⟨_, hQ⟩)

private theorem scalar_compactification_preserves_plus
    [Finite A] [Finite B] (φ : A →+* B)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f)
    (M : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hQ : _root_.DerivedCategory.TStructure.t.plus ((scalarExtension φ X).obj M.obj)) :
    _root_.DerivedCategory.TStructure.t.plus
      ((scalarExtension φ Y).obj
        ((rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).obj M.obj)) := by
  have := compactScalarMap_isIso φ c M.obj
  exact _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
    (asIso ((compactScalarMap φ c).app M.obj)).symm
    (compactification_preserves_plus B c ⟨_, hQ⟩)

private theorem properOpenCoefficientInterchange_source
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U V W Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
    {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : IsPullback k r p i) (E : DerivedCategoryModule R U) :
    (properOpenCoefficientInterchange R sq).hom.app E =
      (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} R) sq.flip).app E := by
  have hn := properOpenCoefficientInterchange_normalization R sq E
  have := hn.2
  let η := (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} R) k).unit.app E
  have : IsIso η := by dsimp only [η]; infer_instance
  have hl : IsIso (unboundedEtaleProperOpenRestriction R sq E) := by
    dsimp only [unboundedEtaleProperOpenRestriction]
    infer_instance
  apply ((derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} R) i).homEquiv _ _).injective
  apply (cancel_mono (unboundedEtaleProperOpenRestriction R sq E)).1
  rw [unboundedEtaleCompactSupport_tower_adjunct]
  dsimp only [unboundedEtaleProperOpenRestriction]
  rw [← Category.assoc, hn.1]
  dsimp only [rightDerivedLowerStar, Functor.comp_obj] at *
  rw [← Functor.map_comp]
  have hc : (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} R) k).unit.app E ≫
      (asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} R) k).unit).inv.app E = 𝟙 E :=
    (asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} R) k).unit).hom_inv_id_app E
  rw [hc]
  exact _root_.CategoryTheory.Functor.map_id _ _

private theorem finiteCoefficientDirectImage_scalarMate
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : DerivedCategoryModule A X) :
    finiteCoefficientDirectImageMap φ f E = (scalarMate φ f).app E := by
  rw [finiteCoefficientDirectImageMap_eq_mate]
  rfl

private theorem scalarOpen_composition_eq
    [Finite A] [Finite B] (φ : A →+* B) {X Y Z : Scheme.{u}}
    (k : X ⟶ Y) (j : Y ⟶ Z) (t : X ⟶ Z) (h : k ≫ j = t)
    [IsOpenImmersion k] [IsOpenImmersion j] [IsOpenImmersion t]
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ Z).map
        (((mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) k j).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr
            (ModuleCat.{u + 1} A) h).hom.app M) ≫
      (openScalarExtension φ t).hom.app M =
    (openScalarExtension φ j).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj M) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((openScalarExtension φ k).hom.app M) ≫
      (((mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} B) k j).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr
            (ModuleCat.{u + 1} B) h).hom.app ((scalarExtension φ X).obj M)) := by
  subst t
  simp only [mapDerivedCategoryOpenImmersionLowerShriekCongr, Iso.trans_hom,
    Iso.symm_hom, Iso.refl_hom, Category.comp_id]
  apply (cancel_epi ((scalarExtension φ Z).map
    ((mapDerivedCategoryOpenImmersionLowerShriekComp
      (ModuleCat.{u + 1} A) k j).hom.app M))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    _root_.CategoryTheory.Functor.map_id, Category.id_comp]
  exact (ProEtale.OpenScalarSite.etale_scalar_comp φ k j M).symm

private theorem compactScalar_properOpen_interchange
    [Finite A] [Finite B] (φ : A →+* B)
    {U V W Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
    {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : IsPullback k r p i) (E : DerivedCategoryModule A U)
    (hE : ∃ n : ℤ, E.IsGE n)
    (hQ : ∃ n : ℤ, ((scalarExtension φ U).obj E).IsGE n) :
    (scalarExtension φ Z).map
        ((openImmersionLowerShriekLowerStarExchange
          (ModuleCat.{u + 1} A) sq.flip).app E) ≫
      (scalarMate φ p).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj E) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) p).map
        ((openScalarExtension φ k).hom.app E) =
    (openScalarExtension φ i).hom.app
        ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj E) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) i).mapDerivedCategory.map
        ((scalarMate φ r).app E) ≫
      (openImmersionLowerShriekLowerStarExchange
        (ModuleCat.{u + 1} B) sq.flip).app ((scalarExtension φ U).obj E) := by
  simpa only [properOpenCoefficientComposite, properOpenCoefficientInterchange_source,
    finiteCoefficientDirectImage_scalarMate, rightDerivedLowerStar] using
    properOpen_coefficient_mate φ sq E hE hQ

private theorem tower_scalar_pasting
    {C₀ C₁ C₂ C₃ C₄ C₅ D₀ D₁ D₂ D₃ D₄ D₅ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄] [Category C₅]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃] [Category D₄] [Category D₅]
    (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂)
    (Q₃ : C₃ ⥤ D₃) (Q₄ : C₄ ⥤ D₄) (Q₅ : C₅ ⥤ D₅)
    (J : C₀ ⥤ C₁) (K : C₁ ⥤ C₂) (L : C₀ ⥤ C₂) (I : C₃ ⥤ C₄)
    (F : C₁ ⥤ C₃) (G : C₂ ⥤ C₄) (H : C₄ ⥤ C₅) (T : C₂ ⥤ C₅)
    (J' : D₀ ⥤ D₁) (K' : D₁ ⥤ D₂) (L' : D₀ ⥤ D₂) (I' : D₃ ⥤ D₄)
    (F' : D₁ ⥤ D₃) (G' : D₂ ⥤ D₄) (H' : D₄ ⥤ D₅) (T' : D₂ ⥤ D₅)
    (bJ : J ⋙ Q₁ ⟶ Q₀ ⋙ J') (bK : K ⋙ Q₂ ⟶ Q₁ ⋙ K')
    (bL : L ⋙ Q₂ ⟶ Q₀ ⋙ L') (bI : I ⋙ Q₄ ⟶ Q₃ ⋙ I')
    (cF : F ⋙ Q₃ ⟶ Q₁ ⋙ F') (cG : G ⋙ Q₄ ⟶ Q₂ ⋙ G')
    (cH : H ⋙ Q₅ ⟶ Q₄ ⋙ H') (cT : T ⋙ Q₅ ⟶ Q₂ ⋙ T')
    (a : J ⋙ K ⟶ L) (a' : J' ⋙ K' ⟶ L')
    (e : F ⋙ I ⟶ K ⋙ G) (e' : F' ⋙ I' ⟶ K' ⋙ G')
    (k : G ⋙ H ⟶ T) (k' : G' ⋙ H' ⟶ T') (M : C₀)
    (hb : Q₂.map (a.app M) ≫ bL.app M =
      bK.app (J.obj M) ≫ K'.map (bJ.app M) ≫ a'.app (Q₀.obj M))
    (hc : Q₅.map (k.app (K.obj (J.obj M))) ≫ cT.app (K.obj (J.obj M)) =
      cH.app (G.obj (K.obj (J.obj M))) ≫ H'.map (cG.app (K.obj (J.obj M))) ≫
        k'.app (Q₂.obj (K.obj (J.obj M))))
    (he : Q₄.map (e.app (J.obj M)) ≫ cG.app (K.obj (J.obj M)) ≫
        G'.map (bK.app (J.obj M)) =
      bI.app (F.obj (J.obj M)) ≫ I'.map (cF.app (J.obj M)) ≫
        e'.app (Q₁.obj (J.obj M))) :
    Q₅.map (H.map (e.app (J.obj M)) ≫ k.app (K.obj (J.obj M)) ≫ T.map (a.app M)) ≫
        cT.app (L.obj M) ≫ T'.map (bL.app M) =
      cH.app (I.obj (F.obj (J.obj M))) ≫
        H'.map (bI.app (F.obj (J.obj M))) ≫ H'.map (I'.map (cF.app (J.obj M))) ≫
        H'.map (I'.map (F'.map (bJ.app M))) ≫
        H'.map (e'.app (J'.obj (Q₀.obj M))) ≫
        k'.app (K'.obj (J'.obj (Q₀.obj M))) ≫ T'.map (a'.app (Q₀.obj M)) := by
  have nT := cT.naturality (a.app M)
  have nH := cH.naturality (e.app (J.obj M))
  have nk := k'.naturality (bK.app (J.obj M))
  have nkJ := k'.naturality (K'.map (bJ.app M))
  have ne := e'.naturality (bJ.app M)
  dsimp only [Functor.comp_map] at nT nH nk nkJ ne
  simp only [Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% nT, reassoc_of% hc, reassoc_of% nH]
  rw [← T'.map_comp, hb]
  simp only [Functor.map_comp]
  rw [← reassoc_of% nk]
  simp only [← H'.map_comp_assoc]
  rw [he]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% nkJ]
  simp only [← H'.map_comp_assoc]
  have hn : bI.app (F.obj (J.obj M)) ≫ I'.map (cF.app (J.obj M)) ≫
      e'.app (Q₁.obj (J.obj M)) ≫ G'.map (K'.map (bJ.app M)) =
      bI.app (F.obj (J.obj M)) ≫ I'.map (cF.app (J.obj M)) ≫
        I'.map (F'.map (bJ.app M)) ≫ e'.app (J'.obj (Q₀.obj M)) := by
    simpa only [Category.assoc, Functor.comp_obj] using congrArg
      (fun z ↦ bI.app (F.obj (J.obj M)) ≫ I'.map (cF.app (J.obj M)) ≫ z) ne.symm
  simpa only [Category.assoc, Functor.comp_obj] using congrArg
    (fun z ↦ cH.app (I.obj (F.obj (J.obj M))) ≫ H'.map z ≫
      k'.app (K'.obj (J'.obj (Q₀.obj M))) ≫ T'.map (a'.app (Q₀.obj M))) hn

private theorem compactScalar_tower
    [Finite A] [Finite B] (φ : A →+* B)
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (d : Compactification g)
    (e : Compactification (f ≫ d.i)) (M : DerivedCategoryModule A X)
    (hE : ∃ n : ℤ,
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) e.restrict.i).mapDerivedCategory.obj
        M).IsGE n)
    (hQ : ∃ n : ℤ, ((scalarExtension φ e.restrict.Z).obj
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) e.restrict.i).mapDerivedCategory.obj
        M)).IsGE n) :
    (scalarExtension φ Z).map
        ((rightDerivedLowerShriekOfCompactificationCompIso A d e).hom.app M) ≫
      (compactScalarMap φ (d.comp e)).app M =
    (compactScalarMap φ d).app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          e.restrict).obj M) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) d).map
        ((compactScalarMap φ e.restrict).app M) ≫
      (rightDerivedLowerShriekOfCompactificationCompIso B d e).hom.app
        ((scalarExtension φ X).obj M) := by
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have : IsNoetherian d.Z := ⟨⟩
  have : IsLocallyNoetherian e.Z := LocallyOfFiniteType.isLocallyNoetherian e.g
  have : CompactSpace e.Z := QuasiCompact.compactSpace_of_compactSpace e.g
  have : IsNoetherian e.Z := ⟨⟩
  have : IsLocallyNoetherian e.restrict.Z :=
    LocallyOfFiniteType.isLocallyNoetherian e.restrict.g
  have : CompactSpace e.restrict.Z := QuasiCompact.compactSpace_of_compactSpace e.restrict.g
  have : IsNoetherian e.restrict.Z := ⟨⟩
  have hi := compactScalar_properOpen_interchange φ e.isPullback_restrict.flip
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
      e.restrict.i).mapDerivedCategory.obj M) hE hQ
  have ho := scalarOpen_composition_eq φ e.restrict.i (pullback.fst e.g d.i)
    e.i e.restrict_i_fst M
  have hp := scalarMate_directImage_composition_eq φ e.g d.g (e.g ≫ d.g) rfl
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
      (pullback.fst e.g d.i)).mapDerivedCategory.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
          e.restrict.i).mapDerivedCategory.obj M))
  rw [right_derived_star_comp_eq, right_derived_star_comp_eq] at hp
  let aR := fun (R : Type (u + 1)) [CommRing R] ↦
    ((mapDerivedCategoryOpenImmersionLowerShriekComp
      (ModuleCat.{u + 1} R) e.restrict.i (pullback.fst e.g d.i)).symm ≪≫
      mapDerivedCategoryOpenImmersionLowerShriekCongr
        (ModuleCat.{u + 1} R) e.restrict_i_fst).hom
  have h := tower_scalar_pasting
    (scalarExtension φ X) (scalarExtension φ e.restrict.Z) (scalarExtension φ e.Z)
    (scalarExtension φ Y) (scalarExtension φ d.Z) (scalarExtension φ Z)
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) e.restrict.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} A)
      (pullback.fst e.g d.i)).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) e.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) e.restrict.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) e.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) d.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) (e.g ≫ d.g))
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) e.restrict.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} B)
      (pullback.fst e.g d.i)).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) e.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) d.i).mapDerivedCategory
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) e.restrict.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) e.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) d.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) (e.g ≫ d.g))
    (openScalarExtension φ e.restrict.i).hom
    (openScalarExtension φ (pullback.fst e.g d.i)).hom
    (openScalarExtension φ e.i).hom (openScalarExtension φ d.i).hom
    (scalarMate φ e.restrict.g) (scalarMate φ e.g)
    (scalarMate φ d.g) (scalarMate φ (e.g ≫ d.g))
    (aR A) (aR B)
    (openImmersionLowerShriekLowerStarExchange
      (ModuleCat.{u + 1} A) e.isPullback_restrict)
    (openImmersionLowerShriekLowerStarExchange
      (ModuleCat.{u + 1} B) e.isPullback_restrict)
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.g d.g).hom
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} B) e.g d.g).hom M ho hp hi
  simpa only [rightDerivedLowerShriekOfCompactificationCompIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc, asIso_hom,
    compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    rightDerivedLowerShriekOfCompactification, Functor.comp_obj, Functor.comp_map,
    compactScalarOpen_eq, Compactification.comp, Compactification.copy,
    Compactification.postcomp, rightDerivedLowerStar, aR] using h

private theorem composition_scalar_transport
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    (Q₀ : C ⥤ C') (Q₁ : D ⥤ D') (Q₂ : E ⥤ E')
    (F₀ F₁ : C ⥤ D) (G₀ G₁ : D ⥤ E) (H₀ H₁ : C ⥤ E)
    (F₀' F₁' : C' ⥤ D') (G₀' G₁' : D' ⥤ E') (H₀' H₁' : C' ⥤ E')
    (a : F₁ ≅ F₀) (b : G₁ ≅ G₀) (d : H₁ ≅ H₀)
    (a' : F₁' ≅ F₀') (b' : G₁' ≅ G₀') (d' : H₁' ≅ H₀')
    (α : F₀ ⋙ G₀ ≅ H₀) (β : F₁ ⋙ G₁ ≅ H₁)
    (α' : F₀' ⋙ G₀' ≅ H₀') (β' : F₁' ⋙ G₁' ≅ H₁')
    (hα : α.hom = NatTrans.hcomp a.inv b.inv ≫ β.hom ≫ d.hom)
    (hα' : α'.hom = NatTrans.hcomp a'.inv b'.inv ≫ β'.hom ≫ d'.hom)
    (sF₀ : F₀ ⋙ Q₁ ⟶ Q₀ ⋙ F₀') (sF₁ : F₁ ⋙ Q₁ ⟶ Q₀ ⋙ F₁')
    (sG₀ : G₀ ⋙ Q₂ ⟶ Q₁ ⋙ G₀') (sG₁ : G₁ ⋙ Q₂ ⟶ Q₁ ⋙ G₁')
    (sH₀ : H₀ ⋙ Q₂ ⟶ Q₀ ⋙ H₀') (sH₁ : H₁ ⋙ Q₂ ⟶ Q₀ ⋙ H₁')
    (M : C)
    (ha : Q₁.map (a.hom.app M) ≫ sF₀.app M =
      sF₁.app M ≫ a'.hom.app (Q₀.obj M))
    (hb : Q₂.map (b.hom.app (F₁.obj M)) ≫ sG₀.app (F₁.obj M) =
      sG₁.app (F₁.obj M) ≫ b'.hom.app (Q₁.obj (F₁.obj M)))
    (hd : Q₂.map (d.hom.app M) ≫ sH₀.app M =
      sH₁.app M ≫ d'.hom.app (Q₀.obj M))
    (hβ : Q₂.map (β.hom.app M) ≫ sH₁.app M =
      sG₁.app (F₁.obj M) ≫ G₁'.map (sF₁.app M) ≫ β'.hom.app (Q₀.obj M)) :
    Q₂.map (α.hom.app M) ≫ sH₀.app M =
      sG₀.app (F₀.obj M) ≫ G₀'.map (sF₀.app M) ≫ α'.hom.app (Q₀.obj M) := by
  have ha' : Q₁.map (a.inv.app M) ≫ sF₁.app M =
      sF₀.app M ≫ a'.inv.app (Q₀.obj M) := by
    apply (cancel_mono (a'.hom.app (Q₀.obj M))).1
    rw [Category.assoc, ← ha]
    simp only [← Q₁.map_comp_assoc, Iso.inv_hom_id_app,
      _root_.CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact (Category.comp_id _).symm
  have hb' : Q₂.map (b.inv.app (F₁.obj M)) ≫ sG₁.app (F₁.obj M) =
      sG₀.app (F₁.obj M) ≫ b'.inv.app (Q₁.obj (F₁.obj M)) := by
    apply (cancel_mono (b'.hom.app (Q₁.obj (F₁.obj M)))).1
    rw [Category.assoc, ← hb]
    simp only [← Q₂.map_comp_assoc, Iso.inv_hom_id_app,
      _root_.CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact (Category.comp_id _).symm
  rw [hα, hα']
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Functor.map_comp, Category.assoc]
  have nb := Q₂.congr_map (b.inv.naturality (a.inv.app M))
  simp only [Functor.map_comp] at nb
  rw [← reassoc_of% nb]
  rw [hd, reassoc_of% hβ, reassoc_of% hb']
  have hn := sG₀.naturality (a.inv.app M)
  have hn' := b'.inv.naturality (sF₁.app M)
  dsimp only [Functor.comp_map] at hn hn'
  rw [reassoc_of% hn, ← reassoc_of% hn']
  simp only [← G₀'.map_comp_assoc]
  rw [ha']
  simp only [Functor.map_comp, Category.assoc]
  simpa only [Category.assoc] using congrArg (fun z ↦ sG₀.app (F₀.obj M) ≫ G₀'.map (sF₀.app M) ≫ z ≫
    β'.hom.app (Q₀.obj M) ≫ d'.hom.app (Q₀.obj M))
      (b'.inv.naturality (a'.inv.app (Q₀.obj M)))

private theorem compactScalarProjection_factorization
    (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule R Y) (M : DerivedCategoryModule R X) :
    compactScalarProjection R c K M =
      orderedDirectProjection R c.g K
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.obj M) ≫
      (lowerStar (ModuleCat.{u + 1} R) c.g).rightDerivedFunctor.map
        (compactOpenProjection R c K M) := by
  simp only [compactScalarProjection, orderedDirectProjection_eq, compactOpenProjection,
    projectionMapOfCompactification_app_app, rightDerivedLowerShriekOfCompactification,
    Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc]
  have hs := ((derivedTensorSymmetry (ModuleCat.{u + 1} R) c.Z).app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.obj M)).hom_inv_id_app
      ((upperStar (ModuleCat.{u + 1} R) c.g).leftDerivedFunctor.obj K)
  erw [reassoc_of% hs]

private theorem orderedDirectProjection_naturality
    (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (K : DerivedCategoryModule R Y)
    {E E' : DerivedCategoryModule R X} (a : E ⟶ E') :
    ((derivedTensor (ModuleCat.{u + 1} R) Y).obj K).map
        ((lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.map a) ≫
      orderedDirectProjection R p K E' =
    orderedDirectProjection R p K E ≫
      (lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.map
        (((derivedTensor (ModuleCat.{u + 1} R) X).obj
          ((upperStar (ModuleCat.{u + 1} R) p).leftDerivedFunctor.obj K)).map a) := by
  simpa only [orderedDirectProjection, Functor.comp_map] using
    (orderedDirectProjectionNat R p K).naturality a

/-- Scalar coherence for the fixed compactification: natural invertibility, the ordered
projection square on every derived input, and proper-refinement compatibility on precisely
the bounded-below pair of inputs specified in the node.
Source: Stacks 0GL6, 0E48 and 0F7I
(blueprint: lem-pur-etale-compact-scalar-coherence).
Proof: step 4 combines the proper scalar isomorphism with the open balancing isomorphism.
The ambient compactification is Noetherian by finite type over its Noetherian target.
Step 5 applies ringed exchange/tensor coherence to the identity-topos coefficient square,
then the two tensor symmetries give the ordered proper projection square. Step 6 checks
the open square on K-flat total tensor generators, including the identical Koszul signs.
Step 7 substitutes the proper/open definitions and uses naturality to paste those squares.
Step 8 proves proper composition by counit mate pasting and open composition by open-unit
transposes. Step 9 applies properOpenComparison_coefficient_refinement to M and Q M in D+,
then proper composition and common-refinement coherence give the displayed comparison
for every pair of compactifications. No flatness or Tor bound is used. -/
theorem compactScalarMap_coherence
    [Finite A] [Finite B] (φ : A →+* B)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    (∀ M : DerivedCategoryModule A X, IsIso ((compactScalarMap φ c).app M)) ∧
    (∀ (K : DerivedCategoryModule A Y) (M : DerivedCategoryModule A X),
      (scalarExtension φ Y).map (compactScalarProjection A c K M) ≫
          (compactScalarMap φ c).app
            (((derivedTensor (ModuleCat.{u + 1} A) X).obj
              ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).obj M) ≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
            (compactScalarProjectionTarget φ f K M) =
        (ExceptionalCoefficients.tensorIso φ Y).hom.app
            (K, (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ≫
          ((derivedTensor (ModuleCat.{u + 1} B) Y).obj
            ((scalarExtension φ Y).obj K)).map ((compactScalarMap φ c).app M) ≫
          compactScalarProjection B c ((scalarExtension φ Y).obj K)
            ((scalarExtension φ X).obj M)) ∧
    (∀ (d : Compactification f)
      (M : _root_.DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
      (∃ N : _root_.DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
        N.obj = (scalarExtension φ X).obj M.obj) →
      (scalarExtension φ Y).map
          ((rightDerivedLowerShriekOfCompactificationIso A c d).hom.app M.obj) ≫
          (compactScalarMap φ d).app M.obj =
        (compactScalarMap φ c).app M.obj ≫
          (rightDerivedLowerShriekOfCompactificationIso B c d).hom.app
            ((scalarExtension φ X).obj M.obj))  := by
  refine ⟨compactScalarMap_isIso φ c, ?_, ?_⟩
  · intro K M
    let J := (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
    have hn := (scalarMate φ c.g).naturality (compactOpenProjection A c K M)
    dsimp only [Functor.comp_map] at hn
    have ho := (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.congr_map
      (compactOpenProjection_scalarExtension φ c K M)
    simp only [Functor.map_comp] at ho
    have hp := etaleDirectScalarProjection φ c.g K (J.obj M)
    simp only [Functor.map_comp] at hp
    have ht := orderedDirectProjection_naturality B c.g ((scalarExtension φ Y).obj K)
      ((ExceptionalCoefficients.openIso φ c.i).hom.app M)
    rw [compactScalarProjection_factorization, compactScalarProjection_factorization]
    dsimp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
      rightDerivedLowerShriekOfCompactification, Functor.comp_obj, Functor.comp_map]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hn]
    simp only [compactScalarProjectionTarget, Functor.map_comp]
    rw [ho]
    rw [reassoc_of% hp]
    rw [← reassoc_of% ht]
  · intro d M hQM
    obtain ⟨N, hN⟩ := hQM
    apply compactScalar_compactification_comparison φ c d M
    rw [← hN]
    exact N.property

/-- The normalized proper/open composition square for scalar extension.
Source: Stacks 0F7J and 0GL6 (blueprint: lem-pur-etale-compact-scalar-coherence).
Proof: step 10 chooses the proper/open tower of the compact-support comparison theorem.
Apply the coefficient mate theorem to its cartesian proper/open square. Its input j_!M
and its scalar extension are bounded below by exactness of open extension and the two
assumed bounds. Paste with the scalar squares for the outer proper map and inner open.
Step 8 supplies composition of the proper and open scalar maps. Step 9 transfers the
result to the chosen compactifications. For the outer compactification this is valid
because F_f M and Q F_f M are bounded below: use bounded-below injective resolutions,
exact open extension, and Q F_f M = F_f Q M from the scalar isomorphism. This is exactly
the specified normalized composition equation, with no claim that arbitrary Q preserves D+. -/
theorem compactScalarChosenMap_comp
    [Finite A] [Finite B] (φ : A →+* B)
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (M : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hQM : ∃ N : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
      N.obj = (scalarExtension φ X).obj M.obj) :
    (scalarExtension φ Z).map
        ((unboundedEtaleLowerShriekCompIso A f g).hom.app M.obj) ≫
        (compactScalarChosenMap φ (f ≫ g)).app M.obj =
      (compactScalarChosenMap φ g).app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M.obj) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g).map
          ((compactScalarChosenMap φ f).app M.obj) ≫
        (unboundedEtaleLowerShriekCompIso B f g).hom.app
          ((scalarExtension φ X).obj M.obj) := by
  have hQM : _root_.DerivedCategory.TStructure.t.plus
      ((scalarExtension φ X).obj M.obj) := by
    obtain ⟨N, hN⟩ := _hQM
    rw [← hN]
    exact N.property
  let d := HasCompactification.compactification g
  let e := (HasCompactification.compactification (f ≫ g)).ofComp d
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} A)
    e.restrict.i).mapDerivedCategory
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e.restrict
  have hF := compactification_preserves_plus A e.restrict M
  have hQF := scalar_compactification_preserves_plus φ e.restrict M hQM
  apply composition_scalar_transport (scalarExtension φ X) (scalarExtension φ Y)
    (scalarExtension φ Z)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) F
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (d.comp e))
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) e.restrict)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) g)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) d)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (f ≫ g))
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) (d.comp e))
    (rightDerivedLowerShriekIso A e.restrict) (rightDerivedLowerShriekIso A d)
    (rightDerivedLowerShriekIso A (d.comp e))
    (rightDerivedLowerShriekIso B e.restrict) (rightDerivedLowerShriekIso B d)
    (rightDerivedLowerShriekIso B (d.comp e))
    (unboundedEtaleLowerShriekCompIso A f g)
    (rightDerivedLowerShriekOfCompactificationCompIso A d e)
    (unboundedEtaleLowerShriekCompIso B f g)
    (rightDerivedLowerShriekOfCompactificationCompIso B d e)
    (unboundedEtaleLowerShriekCompIso_tower A f g d e)
    (unboundedEtaleLowerShriekCompIso_tower B f g d e)
    (compactScalarChosenMap φ f) (compactScalarMap φ e.restrict)
    (compactScalarChosenMap φ g) (compactScalarMap φ d)
    (compactScalarChosenMap φ (f ≫ g)) (compactScalarMap φ (d.comp e)) M.obj
  · exact compactScalar_compactification_comparison φ e.restrict
      (HasCompactification.compactification f) M hQM
  · exact compactScalar_compactification_comparison φ d
      (HasCompactification.compactification g) ⟨F.obj M.obj, hF⟩ hQF
  · exact compactScalar_compactification_comparison φ (d.comp e)
      (HasCompactification.compactification (f ≫ g)) M hQM
  · exact compactScalar_tower φ f g d e M.obj
      (exact_open_preserves_plus A e.restrict.i M)
      (scalar_open_preserves_plus φ e.restrict.i M hQM)

end AlgebraicGeometry.Etale
