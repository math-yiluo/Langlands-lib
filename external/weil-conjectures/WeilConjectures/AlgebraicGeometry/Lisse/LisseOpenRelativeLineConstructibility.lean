/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.CategoryTheory.Abelian.PrimeFactorDevissage
import WeilConjectures.CategoryTheory.Sites.Point.Linear
import WeilConjectures.AlgebraicGeometry.FiniteEtaleUnitStalkInclusion
import WeilConjectures.AlgebraicGeometry.Constant.ConstantShriekRelativeDimensionOne
import WeilConjectures.CategoryTheory.Etale.EtaleLisseFiltrationDevissage
import WeilConjectures.AlgebraicGeometry.Etale.EtaleShriekQcqsComposition
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenCoverShriekNaturalSES
import WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteEtaleFiltration
import WeilConjectures.AlgebraicGeometry.Curve.DisjointOpenExtensionBiproduct
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues

/-!
# Constructibility for lisse coefficients on an open relative affine line

## References

* Stacks Project, Tag 0GKY, specialized to finite coefficient rings and affine finite-type integer
  bases
-/

@[expose] public section

universe u' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ZeroObject

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

section StableInstances

/-- A fixed abelian structure on étale sheaves of modules, used as a high-priority local
instance to keep instance paths stable. -/
@[instance_reducible] noncomputable def etaleSheafModuleAbelian
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := inferInstance

attribute [local instance 2000] etaleSheafModuleAbelian

/-- A fixed choice of derived category of étale sheaves of modules, compatible with
`etaleSheafModuleAbelian`. -/
@[instance_reducible] noncomputable def etaleSheafModuleHasDerivedCategory
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := by
  unfold etaleSheafModuleAbelian
  infer_instance

attribute [local instance 2000] etaleSheafModuleHasDerivedCategory

-- Stalk calculation adapted from Bin Wu, FiniteEtaleModuleTraceData.
private theorem lisse_unit_stalk_component
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (t : f.GeometricFiber s) :
    (Scheme.pointSmallEtale s).sheafFiber.map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G) ≫
      stalkRestrict (ModuleCat.{u + 1} R) f s t ((f)^*[ModuleCat.{u + 1} R].obj G) =
    eqToHom (by rw [t.2]; rfl) ≫
      ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t.1).app G).inv := by
  obtain ⟨t, rfl⟩ := t
  simp only [eqToHom_refl, Category.id_comp]
  erw [stalkRestrict_eq_counit]
  have hn := (upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t).inv.naturality
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G)
  dsimp only [Functor.comp_map] at hn
  erw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  erw [Adjunction.left_triangle_components]
  simp

private theorem lisse_trace_stalk_component
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (t : f.GeometricFiber s) :
    sheafFiberToLowerStar (ModuleCat.{u + 1} R) f t ((f)^*[ModuleCat.{u + 1} R].obj G) ≫
      (Scheme.pointSmallEtale s).sheafFiber.map
        ((lowerStarUpperStarAdjunctionOfIsFinite (ModuleCat.{u + 1} R) f).counit.app G) =
    ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t.1).app G).hom ≫
      eqToHom (by rw [t.2]; rfl) := by
  obtain ⟨t, rfl⟩ := t
  erw [← finiteEtaleUnit_stalk_inclusion R f
    ((f)^*[ModuleCat.{u + 1} R].obj G) (t ≫ f) ⟨t, rfl⟩]
  simp only [eqToHom_refl, Category.comp_id]
  have hn := (upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t).hom.naturality
    ((lowerStarUpperStarAdjunctionOfIsFinite (ModuleCat.{u + 1} R) f).counit.app G)
  dsimp only [Functor.comp_map] at hn
  erw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp,
    Adjunction.right_triangle_components]
  simp

-- The trace proof tests equality only at algebraically closed stalks.
/-- For a finite étale map of constant geometric degree `d`, the trace retracts the
adjunction unit up to multiplication by `d`. -/
theorem lisse_trace_degree
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (d : ℕ)
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nat.card (f.GeometricFiber s) = d) :
    ∃ t : (f)_*[ModuleCat.{u + 1} R].obj ((f)^*[ModuleCat.{u + 1} R].obj G) ⟶ G,
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G ≫ t =
        (d : R) • 𝟙 G := by
  classical
  let A := ModuleCat.{u + 1} R
  let H := (f)^*[A].obj G
  let η := (upperStarLowerStarAdjunction A f).unit.app G
  let tr := (lowerStarUpperStarAdjunctionOfIsFinite A f).counit.app G
  refine ⟨tr, ?_⟩
  apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro x
  let s := X.algClosurePoint x
  let Φ := (Scheme.pointSmallEtale s).sheafFiber (A := A)
  let : Fintype (f.GeometricFiber s) := Fintype.ofFinite _
  let ρ := fun t : f.GeometricFiber s ↦ stalkRestrict A f s t H
  let j := fun t : f.GeometricFiber s ↦ sheafFiberToLowerStar A f t H
  have htotal : ∑ t, ρ t ≫ j t = 𝟙 (Φ.obj ((f)_*[A].obj H)) := by
    apply (cancel_mono (Limits.Pi.lift ρ)).mp
    apply Limits.Pi.hom_ext
    intro t
    simp only [Category.assoc, Limits.Pi.lift_comp_π]
    erw [Preadditive.sum_comp, Category.id_comp]
    simp only [Category.assoc]
    change ∑ a, ρ a ≫ (j a ≫ ρ t) = ρ t
    erw [Finset.sum_eq_single t]
    · simp [ρ, j]
    · intro a ha hat
      erw [sheafFiberToLowerStar_stalkRestrict_of_ne A f hat H, Limits.comp_zero]
    · intro ht
      exact (ht (Finset.mem_univ t)).elim
  simp only [CategoryTheory.Functor.map_comp,
    GrothendieckTopology.Point.sheafFiber_map_smul]
  change Φ.map η ≫ Φ.map tr = (d : R) • Φ.map (𝟙 G)
  erw [Φ.map_id]
  calc
    Φ.map η ≫ Φ.map tr = Φ.map η ≫ (∑ t, ρ t ≫ j t) ≫ Φ.map tr := by
      erw [htotal, Category.id_comp]
    _ = ∑ t, (Φ.map η ≫ ρ t) ≫ (j t ≫ Φ.map tr) := by
      erw [Preadditive.sum_comp, Preadditive.comp_sum]
      simp only [Category.assoc]
    _ = ∑ _t : f.GeometricFiber s, 𝟙 (Φ.obj G) := by
      apply Finset.sum_congr rfl
      intro t ht
      erw [lisse_unit_stalk_component R f G s t, lisse_trace_stalk_component R f G s t]
      simp
    _ = (d : R) • 𝟙 _ := by
      erw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
        hdeg _ s, ← Nat.cast_smul_eq_nsmul R]

/-- The single-complex functor in degree zero to the bounded-below derived category. -/
noncomputable abbrev singleZero (C : Type*) [Category* C] [Abelian C]
    [HasDerivedCategory C] : C ⥤ _root_.DerivedCategory.Plus C :=
  _root_.DerivedCategory.Plus.singleFunctor C 0

/-- An isomorphism-closed property holds on `F.obj K` iff it holds on `G.obj K` for
naturally isomorphic functors. -/
theorem prop_iff_of_natIso
    {C D : Type*} [Category* C] [Category* D]
    (W : ObjectProperty D) [W.IsClosedUnderIsomorphisms]
    {F G : C ⥤ D} (e : F ≅ G) (K : C) : W (F.obj K) ↔ W (G.obj K) :=
  W.prop_iff_of_iso (e.app K)

/-- An abelian category has finite biproducts for any choice of zero morphisms. -/
theorem abelian_hasFiniteBiproducts
    {C : Type*} [Category* C] [Abelian C] [Z : HasZeroMorphisms C] :
    HasFiniteBiproducts C := by
  obtain rfl : Z = Preadditive.preadditiveHasZeroMorphisms := Subsingleton.elim _ _
  exact Abelian.hasFiniteBiproducts

/-- A property closed under finite products holds on the image of a finite biproduct
if it holds on the images of its summands. -/
theorem objectProperty_map_biproduct
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (W : ObjectProperty D) [W.IsClosedUnderIsomorphisms] [W.IsClosedUnderFiniteProducts]
    {J : Type} [Finite J] (G : J → C) [HasBiproduct G] [PreservesBiproduct G F]
    [HasBiproduct (fun j ↦ F.obj (G j))] (hG : ∀ j, W (F.obj (G j))) :
    W (F.obj (⨁ G)) := by
  exact W.prop_of_iso (F.mapBiproduct G ≪≫ biproduct.isoProduct _).symm (W.prop_product hG)

/-- The constructible étale sheaves of `Λ`-modules, as an object property. -/
abbrev constructibleProperty (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fun F ↦ Scheme.IsConstructibleSheaf F

private instance (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (constructibleProperty Λ X).IsClosedUnderIsomorphisms := ⟨fun e h ↦ by
  have := h
  exact Scheme.IsConstructibleSheaf.of_iso e⟩

private instance (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (constructibleProperty Λ X).ContainsZero :=
  ⟨0, isZero_zero _, Scheme.IsConstructibleSheaf.of_isZero (isZero_zero _)⟩

private instance (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) :
    (constructibleProperty Λ X).IsClosedUnderKernels := ⟨by
  rintro _ ⟨f, k, hk, hX, hY⟩
  have := hX
  have := hY
  have := Scheme.IsConstructibleSheaf.kernel f
  exact Scheme.IsConstructibleSheaf.of_iso (F := kernel f)
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hk)⟩

private instance (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (constructibleProperty Λ X).IsClosedUnderCokernels := ⟨by
  rintro _ ⟨f, k, hk, hX, hY⟩
  have := hX
  have := hY
  have := Scheme.IsConstructibleSheaf.cokernel f
  exact Scheme.IsConstructibleSheaf.of_iso (F := cokernel f)
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hk)⟩

private instance (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) :
    (constructibleProperty Λ X).IsClosedUnderExtensions := ⟨fun h h₁ h₃ ↦ by
  have := h₁
  have := h₃
  exact Scheme.IsConstructibleSheaf.of_shortExact h⟩

/-- The bounded-below compact-support functor of the specified compactification. -/
@[irreducible]
noncomputable def shriekFunctor
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  rightDerivedLowerShriekOfCompactificationPlus A c

private noncomputable instance
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (shriekFunctor A c).CommShift ℤ := by
  unfold shriekFunctor
  infer_instance

private instance
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (shriekFunctor A c).Additive := by
  unfold shriekFunctor
  infer_instance

private instance
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (shriekFunctor A c).IsTriangulated := by
  unfold shriekFunctor
  infer_instance

/-- For an open immersion, compact support with the trivial compactification is the
derived extension by zero. -/
noncomputable def shriekOpenIso
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    shriekFunctor A (Compactification.ofIsOpenImmersion j) ≅
      (openImmersionLowerShriek A j).mapDerivedCategoryPlus := by
  unfold shriekFunctor
  exact Functor.isoWhiskerLeft _ (lowerStarIdDerivedPlus A Y) ≪≫ Functor.rightUnitor _

/-- The extension by zero along the identity is the identity functor. -/
noncomputable def shriekIdentityIso
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    (X : Scheme.{u}) : openImmersionLowerShriek A (𝟙 X) ≅ 𝟭 _ :=
  (openImmersionLowerShriekUpperStarAdjunction A (𝟙 X)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight (upperStarId A X).symm)

/-- For a proper morphism, compact support with the identity compactification is the
derived direct image. -/
noncomputable def shriekProperIso
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [PreservesFiniteColimits (lowerStar A f)] :
    shriekFunctor A (Compactification.ofIsProper f) ≅
      (lowerStar A f).mapDerivedCategoryPlus := by
  unfold shriekFunctor
  exact Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryPlusNatIso (shriekIdentityIso A X) ≪≫
      Functor.mapDerivedCategoryPlusIdIso _) _ ≪≫
    Functor.leftUnitor _ ≪≫ (lowerStar A f).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus

private theorem shriek_comp
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cgf : Compactification (f ≫ g)) :
    Nonempty
      (shriekFunctor (ModuleCat.{u + 1} Λ) cf ⋙
        shriekFunctor (ModuleCat.{u + 1} Λ) cg ≅
        shriekFunctor (ModuleCat.{u + 1} Λ) cgf) := by
  unfold shriekFunctor
  exact nonempty_iso_etaleShriek_qcqs_compactification_comp Λ f g cf cg cgf

/-- Bounded-below complexes all of whose cohomology objects satisfy `P`. -/
def plusProperty {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (P : ObjectProperty C) : ObjectProperty (_root_.DerivedCategory.Plus C) :=
  fun K ↦ ∀ q : ℤ, P ((_root_.DerivedCategory.Plus.homologyFunctor C q).obj K)

/-- `plusProperty` is the inverse image of the homology property along the inclusion. -/
theorem plusProperty_eq {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (P : ObjectProperty C) :
    plusProperty P = (_root_.DerivedCategory.homologyProperty P).inverseImage
      _root_.DerivedCategory.Plus.ι := rfl

private instance {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] :
    (plusProperty P).IsClosedUnderIsomorphisms := by rw [plusProperty_eq]; infer_instance

private instance {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions] :
    (plusProperty P).IsTriangulated := by rw [plusProperty_eq]; infer_instance

/-- Compact support applied to a sheaf placed in degree zero. -/
@[irreducible] noncomputable def sourceFunctor
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Sheaf X.smallEtaleTopology A ⥤ _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  singleZero _ ⋙ shriekFunctor A c

private noncomputable instance
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sourceFunctor A c).Additive := by
  unfold sourceFunctor
  infer_instance

private theorem constant_shriek
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (A : Type u) [CommRing A] [Algebra.FiniteType ℤ A]
    {X : Scheme.{u}} (h : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated h] [IsAffineHom h] [SmoothOfRelativeDimension 1 h]
    (hΛ : ∀ (a : Λ) (s : Spec (CommRingCat.of A)),
      IsUnit (addOrderOf a : (Spec (CommRingCat.of A)).presheaf.stalk s))
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (c : Compactification h) [QuasiCompact c.i] (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((sourceFunctor (ModuleCat.{u + 1} Λ) c).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))  := by
  unfold sourceFunctor shriekFunctor
  exact constructibleCohomology_lowerShriek_constant_of_smooth_relativeDimension_one Λ A h hΛ M c q

/-- The sheaves whose compactly supported cohomology sheaves all satisfy `P`. -/
def cohomologySourceProperty
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} (P : ObjectProperty (Sheaf Y.smallEtaleTopology A))
    {f : X ⟶ Y} (c : Compactification f) : ObjectProperty (Sheaf X.smallEtaleTopology A) :=
  (plusProperty P).inverseImage (sourceFunctor A c)

private abbrev sourceProperty (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  cohomologySourceProperty (ModuleCat.{u + 1} Λ) (constructibleProperty Λ Y) c

private instance (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sourceProperty Λ c).IsClosedUnderIsomorphisms := by
  unfold sourceProperty cohomologySourceProperty
  infer_instance

private instance (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sourceProperty Λ c).IsClosedUnderFiniteProducts := by
  apply ObjectProperty.IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape.{0}
  intro J _
  have : PreservesLimitsOfShape (Discrete.{0} J) (sourceFunctor (ModuleCat.{u + 1} Λ) c) :=
    preservesProductsOfShape_of_preservesBiproductsOfShape _
  unfold sourceProperty cohomologySourceProperty
  infer_instance

/-- Compose a single-degree inclusion with an exact functor and a derived identification. -/
noncomputable def single_composite_iso
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : _root_.DerivedCategory.Plus D ⥤ E)
    {H : _root_.DerivedCategory.Plus C ⥤ _root_.DerivedCategory.Plus D}
    {I : _root_.DerivedCategory.Plus C ⥤ E}
    (eH : H ≅ F.mapDerivedCategoryPlus) (e : H ⋙ G ≅ I) :
    F ⋙ (singleZero D ⋙ G) ≅ singleZero C ⋙ I :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapDerivedCategoryPlusSingleFunctor 0).symm G ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight eH.symm G ≪≫ e)

private theorem source_open_hom_comp
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X' X Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (j : X' ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (ca : Compactification (j ≫ f)) :
    Nonempty (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j ⋙
      sourceFunctor (ModuleCat.{u + 1} Λ) c ≅
        sourceFunctor (ModuleCat.{u + 1} Λ) ca) := by
  obtain ⟨ec⟩ := shriek_comp Λ j f (Compactification.ofIsOpenImmersion j) c ca
  unfold sourceFunctor
  exact ⟨single_composite_iso _ _ (shriekOpenIso _ j) ec⟩

private theorem source_proper_comp
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X' X Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g : X' ⟶ X) [IsProper g]
    [PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} Λ) g)]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (ca : Compactification (g ≫ f)) :
    Nonempty (lowerStar (ModuleCat.{u + 1} Λ) g ⋙
      sourceFunctor (ModuleCat.{u + 1} Λ) c ≅
        sourceFunctor (ModuleCat.{u + 1} Λ) ca) := by
  obtain ⟨ec⟩ := shriek_comp Λ g f (Compactification.ofIsProper g) c ca
  unfold sourceFunctor
  exact ⟨single_composite_iso _ _ (shriekProperIso _ g) ec⟩

private theorem sourceProperty_openExtension
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (T : X.Opens) (hT : IsCompact (T : Set X))
    (ca : Compactification (T.ι ≫ f))
    (Q : Sheaf T.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : sourceProperty Λ ca Q) :
    sourceProperty Λ c ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.ι).obj Q) := by
  have : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hT
  have : QuasiSeparatedSpace T.toScheme := T.ι.isOpenEmbedding.quasiSeparatedSpace
  obtain ⟨e⟩ := source_open_hom_comp Λ T.ι f c ca
  exact (prop_iff_of_natIso (plusProperty (constructibleProperty Λ Y)) e Q).mpr h

/-- Two-out-of-three for the compactly supported cohomology property along a short exact
sequence of sheaves. -/
theorem sourceFunctor_shortExact
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [Z : HasZeroMorphisms (Sheaf X.smallEtaleTopology A)]
    (P : ObjectProperty (Sheaf Y.smallEtaleTopology A))
    [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    (S : ShortComplex (Sheaf X.smallEtaleTopology A)) (hS : S.ShortExact) :
    (cohomologySourceProperty A P c S.X₁ → cohomologySourceProperty A P c S.X₃ →
      cohomologySourceProperty A P c S.X₂) ∧
    (cohomologySourceProperty A P c S.X₁ → cohomologySourceProperty A P c S.X₂ →
      cohomologySourceProperty A P c S.X₃) := by
  unfold cohomologySourceProperty sourceFunctor
  let W := (plusProperty P).inverseImage (shriekFunctor A c)
  obtain ⟨δ, hδ⟩ := hS.exists_mk_singleTrianglePlus_distinguished
  exact ⟨fun h₁ h₃ ↦ W.ext_of_isTriangulatedClosed₂ (Triangle.mk _ _ δ) hδ h₁ h₃,
    fun h₁ h₂ ↦ W.ext_of_isTriangulatedClosed₃ (Triangle.mk _ _ δ) hδ h₁ h₂⟩

private theorem sourceProperty_shortExact_three
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hS : S.ShortExact) (h₁ : sourceProperty Λ c S.X₁)
    (h₂ : sourceProperty Λ c S.X₂) : sourceProperty Λ c S.X₃ := by
  exact (sourceFunctor_shortExact (ModuleCat.{u + 1} Λ) c
    (constructibleProperty Λ Y) S hS).2 h₁ h₂

private theorem shriekProperty_shortExact
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hS : S.ShortExact)
    (h₁ : sourceProperty Λ c S.X₁)
    (h₃ : sourceProperty Λ c S.X₃) :
    sourceProperty Λ c S.X₂ := by
  exact (sourceFunctor_shortExact (ModuleCat.{u + 1} Λ) c
    (constructibleProperty Λ Y) S hS).1 h₁ h₃

private theorem cohomology_property_filtration
    {C D E : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Z : HasZeroMorphisms C]
    (Φ : _root_.DerivedCategory.Plus C ⥤ _root_.DerivedCategory.Plus D)
    [Φ.CommShift ℤ] [Φ.IsTriangulated] [Φ.Additive]
    (P : ObjectProperty D) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    (T : E → C) (H : E → Prop)
    (L : C) (r : ℕ) (F : Fin (r + 1) → Subobject L) (hF : Monotone F)
    (h₀ : IsZero (F 0 : C)) (hᵣ : F (Fin.last r) = ⊤)
    (hQ : ∀ i : Fin r, ∃ M : E, H M ∧
      Nonempty (cokernel (Subobject.ofLE (F i.castSucc) (F i.succ)
        (hF (Fin.castSucc_le_succ i))) ≅ T M))
    (hT : ∀ M, H M → plusProperty P (Φ.obj ((singleZero C).obj (T M)))) :
    plusProperty P (Φ.obj ((singleZero C).obj L)) := by
  obtain rfl : Z = Preadditive.preadditiveHasZeroMorphisms := Subsingleton.elim _ _
  have hb : F 0 = ⊥ := by
    rw [← Subobject.mk_arrow (F 0)]
    exact Subobject.mk_eq_bot_iff_zero.mpr (h₀.eq_of_src _ _)
  apply cohomology_mem_of_filtration Φ P L r F hb hᵣ
    (fun i ↦ hF (Fin.castSucc_le_succ i))
  intro i
  obtain ⟨M, hM, ⟨e⟩⟩ := hQ i
  exact ((plusProperty P).inverseImage ((singleZero C) ⋙ Φ)).prop_of_iso e.symm (hT M hM)

/-- A finite filtration whose graded pieces have constructible-type compactly supported
cohomology gives the same property for the filtered sheaf. -/
theorem sourceFunctor_filtration
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [Z : HasZeroMorphisms (Sheaf X.smallEtaleTopology A)]
    (P : ObjectProperty (Sheaf Y.smallEtaleTopology A))
    [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    {E : Type*} (T : E → Sheaf X.smallEtaleTopology A) (H : E → Prop)
    (L : Sheaf X.smallEtaleTopology A)
    (r : ℕ) (F : Fin (r + 1) → Subobject L) (hF : Monotone F)
    (h₀ : IsZero (F 0 : Sheaf X.smallEtaleTopology A)) (hᵣ : F (Fin.last r) = ⊤)
    (hQ : ∀ i : Fin r, ∃ M : E, H M ∧
      Nonempty (cokernel (Subobject.ofLE (F i.castSucc) (F i.succ)
        (hF (Fin.castSucc_le_succ i))) ≅ T M))
    (hT : ∀ M, H M → plusProperty P ((sourceFunctor A c).obj (T M))) :
    plusProperty P ((sourceFunctor A c).obj L) := by
  unfold sourceFunctor at *
  exact cohomology_property_filtration (shriekFunctor A c) P T H L r F hF h₀ hᵣ hQ hT

private theorem shriekProperty_filtration
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsAffineHom f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (hΛ : ∀ (a : Λ) (s : Spec (.of R)), IsUnit (addOrderOf a : (Spec (.of R)).presheaf.stalk s))
    (c : Compactification f)
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (r : ℕ) (F : Fin (r + 1) → Subobject L) (hF : Monotone F)
    (h₀ : IsZero (F 0 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hᵣ : F (Fin.last r) = ⊤)
    (hQ : ∀ i : Fin r, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
      Nonempty (cokernel (Subobject.ofLE (F i.castSucc) (F i.succ)
        (hF (Fin.castSucc_le_succ i))) ≅
          (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :
    sourceProperty Λ c L := by
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  apply sourceFunctor_filtration (ModuleCat.{u + 1} Λ) c
    (constructibleProperty Λ (Spec (.of R)))
    (fun M : ModuleCat.{u + 1} Λ ↦
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
    (fun M ↦ Finite M) L r F hF h₀ hᵣ hQ
  intro M hM q
  have := hM
  exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
    (constant_shriek Λ R f hΛ M c q)

private theorem shriekProperty_disjoint
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (n : ℕ) (U : Fin n → X.Opens)
    (hdisj : Pairwise (fun a b ↦ Disjoint (U a) (U b)))
    (hcover : (⋃ a, (U a : Set X)) = Set.univ)
    (hcompact : ∀ a, IsCompact (U a : Set X))
    (hlocal : ∀ a (ca : Compactification ((U a).ι ≫ f)),
      sourceProperty Λ ca (((upperStar (ModuleCat.{u + 1} Λ) (U a).ι).obj L))) :
    sourceProperty Λ c L := by
  classical
  let A := ModuleCat.{u + 1} Λ
  have : HasFiniteBiproducts (Sheaf X.smallEtaleTopology A) := abelian_hasFiniteBiproducts
  let G (a : Fin n) := (openImmersionLowerShriek A (U a).ι).obj
    ((upperStar A (U a).ι).obj L)
  have htop : (⨆ a, U a) = ⊤ := by
    apply SetLike.coe_injective
    simpa only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top] using hcover
  have : IsIso (⨆ a, U a).ι := by
    rw [htop]
    exact (inferInstance : IsIso X.topIso.hom)
  obtain ⟨e⟩ := disjointOpenExtension_biproduct_iso Λ L n U
    (fun _ _ h ↦ TopologicalSpace.Opens.coe_disjoint.mpr (hdisj h))
  let eL : L ≅ ⨁ G :=
    (asIso ((openImmersionLowerShriekUpperStarAdjunction A (⨆ a, U a).ι).counit.app L)).symm
      ≪≫ e
  have hG (a : Fin n) : sourceProperty Λ c (G a) := by
    have : CompactSpace (U a).toScheme := isCompact_iff_compactSpace.mp (hcompact a)
    have : QuasiSeparatedSpace (U a).toScheme :=
      (U a).ι.isOpenEmbedding.quasiSeparatedSpace
    obtain ⟨ca⟩ :=
      (inferInstance : HasCompactification ((U a).ι ≫ f)).nonempty_compactification
    exact sourceProperty_openExtension Λ f c (U a) (hcompact a) ca _ (hlocal a ca)
  apply (sourceProperty Λ c).prop_of_iso eL.symm
  exact objectProperty_map_biproduct (sourceFunctor A c)
    (plusProperty (constructibleProperty Λ Y)) G hG

private theorem shriekProperty_affine_prime
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (f : Spec (.of A) ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 f]
    (hΛ : ∀ (a : Λ) (s : Spec (.of R)), IsUnit (addOrderOf a : (Spec (.of R)).presheaf.stalk s))
    (L : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf L]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hL : ℓ • 𝟙 L = 0) (c : Compactification f) :
    sourceProperty Λ c L := by
  classical
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  obtain ⟨T, g, hgfin, hget, hgsurj, d, hdpos, hd, hdeg,
    k, U, hU, hdisj, hcover, hfil⟩ :=
    exists_lisse_finiteEtale_filtration A Λ L ℓ 1 hℓ (by omega) (by simpa using hL)
  have := hgfin
  have := hget
  have : IsAffine T := isAffine_of_isAffineHom g
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian g
  let B := ModuleCat.{u + 1} Λ
  let G := (upperStar B g).obj L
  let cg := Compactification.ofIsProper g
  have : SmoothOfRelativeDimension 1 (g ≫ f) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (g ≫ f))
  obtain ⟨cf⟩ :=
    (inferInstance : HasCompactification (g ≫ f)).nonempty_compactification
  have hG : sourceProperty Λ cf G := by
    apply shriekProperty_disjoint Λ (g ≫ f) cf G k U hdisj hcover
      (fun a ↦ (hU a).1.isCompact)
    intro a ca
    have : IsAffine (U a).toScheme := (hU a).1
    have : IsClosedImmersion (U a).ι :=
      IsClosedImmersion.of_isPreimmersion (U a).ι (by simpa using (hU a).2)
    have : SmoothOfRelativeDimension 0 ((U a).ι ≫ g) := inferInstance
    have : SmoothOfRelativeDimension 1 ((U a).ι ≫ g ≫ f) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 1) ((U a).ι ≫ (g ≫ f)))
    obtain ⟨r, F, hF, h₀, hᵣ, hQ⟩ := hfil a
    exact shriekProperty_filtration Λ R ((U a).ι ≫ g ≫ f) hΛ ca
      ((upperStar B (U a).ι).obj G) r F hF h₀ hᵣ hQ
  obtain ⟨ecomp⟩ := source_proper_comp Λ g f c cf
  have hpush : sourceProperty Λ c ((lowerStar B g).obj G) :=
    (prop_iff_of_natIso (plusProperty (constructibleProperty Λ (Spec (.of R)))) ecomp G).mpr hG
  obtain ⟨t, ht⟩ := lisse_trace_degree Λ g L d hdeg
  obtain ⟨a, _, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((hℓ.coprime_iff_not_dvd.mpr hd).symm) hℓ.one_lt
  have hret : (upperStarLowerStarAdjunction B g).unit.app L ≫ (a • t) = 𝟙 L := by
    rw [Preadditive.comp_nsmul, ht, Nat.cast_smul_eq_nsmul, smul_smul, mul_comm a d,
      ← Nat.mod_add_div (d * a) ℓ, add_nsmul, ha, one_nsmul]
    have hz : (ℓ * (d * a / ℓ)) • 𝟙 L = 0 := by
      rw [mul_comm, mul_smul, hL, smul_zero]
    rw [hz, add_zero]
  let retract : Retract L ((lowerStar B g).obj G) :=
    ⟨(upperStarLowerStarAdjunction B g).unit.app L, a • t, hret⟩
  intro q
  let H := sourceFunctor B c ⋙ _root_.DerivedCategory.Plus.homologyFunctor
    (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
  have : Scheme.IsConstructibleSheaf (H.obj ((lowerStar B g).obj G)) := hpush q
  exact Scheme.IsConstructibleSheaf.of_retract (retract.map H)

/-- Strong induction on a positive integer killing an object: a property closed under
extensions holds on every object killed by a positive integer if it holds on objects killed by
a prime, provided the auxiliary property is stable under kernels and images of multiples. -/
theorem objectProperty_of_nsmul_id_eq_zero
    {C : Type*} [Category* C] [Abelian C] [Z : HasZeroMorphisms C]
    (P H : ObjectProperty C)
    (hext : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (hkernel : ∀ (F : C), H F → ∀ r : ℕ, H (kernel (r • 𝟙 F)))
    (himage : ∀ (F : C), H F → ∀ r : ℕ, H (image (r • 𝟙 F)))
    (hprime : ∀ r : ℕ, r.Prime → ∀ F : C, H F → r • 𝟙 F = 0 → P F) :
    ∀ (n : ℕ), 0 < n → ∀ F : C, H F → n • 𝟙 F = 0 → P F := by
  obtain rfl : Z = Preadditive.preadditiveHasZeroMorphisms := Subsingleton.elim _ _
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn F hF hkill
    by_cases h1 : n = 1
    · subst n
      exact hprime 2 Nat.prime_two F hF
        (by rw [two_nsmul, ← one_nsmul (𝟙 F), hkill, add_zero])
    obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd h1
    exact hext _ (Abelian.shortExact_nsmulShortComplex F r)
      (hprime r hr _ (hkernel F hF r) (Abelian.nsmul_id_kernel_eq_zero F r))
      (ih (n / r) (Nat.div_lt_self hn hr.one_lt)
        (Nat.div_pos (Nat.le_of_dvd hn hrn) hr.pos) _ (himage F hF r)
        (Abelian.nsmul_id_image_eq_zero F hkill hrn))

private theorem shriekProperty_spec
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (f : Spec (.of A) ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 f]
    (hΛ : ∀ (a : Λ) (s : Spec (.of R)), IsUnit (addOrderOf a : (Spec (.of R)).presheaf.stalk s))
    (L : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf L] (c : Compactification f) :
    sourceProperty Λ c L := by
  classical
  let H : ObjectProperty (Sheaf (Spec (.of A)).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) := Scheme.IsFiniteLocallyConstantSheaf
  have hk (F : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (hF : H F) (r : ℕ) : H (kernel (r • 𝟙 F)) := by
    have : Scheme.IsFiniteLocallyConstantSheaf F := hF
    exact Scheme.IsFiniteLocallyConstantSheaf.kernel (r • 𝟙 F)
  have hi (F : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (hF : H F) (r : ℕ) : H (image (r • 𝟙 F)) := by
    have : Scheme.IsFiniteLocallyConstantSheaf F := hF
    have := Scheme.IsFiniteLocallyConstantSheaf.kernel (r • 𝟙 F)
    have := Scheme.IsFiniteLocallyConstantSheaf.cokernel (kernel.ι (r • 𝟙 F))
    exact Scheme.IsFiniteLocallyConstantSheaf.of_iso (Abelian.coimageIsoImage' (r • 𝟙 F))
  let : Fintype Λ := Fintype.ofFinite Λ
  apply objectProperty_of_nsmul_id_eq_zero (sourceProperty Λ c) H
    (shriekProperty_shortExact Λ c) hk hi
    (fun r hr F hF hkill ↦ by
      have : Scheme.IsFiniteLocallyConstantSheaf F := hF
      exact shriekProperty_affine_prime Λ R A f hΛ F r hr hkill c)
    (Fintype.card Λ) Fintype.card_pos L inferInstance
  rw [← Nat.cast_smul_eq_nsmul Λ, Nat.cast_card_eq_zero, zero_smul]

private theorem shriekProperty_iso_source
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X X' Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (e : X' ≅ X) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (c : Compactification f) (c' : Compactification (e.hom ≫ f))
    (h : sourceProperty Λ c' (((upperStar (ModuleCat.{u + 1} Λ) e.hom).obj L))) :
    sourceProperty Λ c L := by
  let B := ModuleCat.{u + 1} Λ
  obtain ⟨ec⟩ := source_open_hom_comp Λ e.hom f c c'
  apply (sourceProperty Λ c).prop_of_iso
    (asIso ((openImmersionLowerShriekUpperStarAdjunction B e.hom).counit.app L))
  exact (prop_iff_of_natIso (plusProperty (constructibleProperty Λ Y)) ec
    ((upperStar B e.hom).obj L)).mpr h

private theorem shriekProperty_affine
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 f]
    (hΛ : ∀ (a : Λ) (s : Spec (.of R)), IsUnit (addOrderOf a : (Spec (.of R)).presheaf.stalk s))
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf L] (c : Compactification f) :
    sourceProperty Λ c L := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let e := X.isoSpec.symm
  obtain ⟨c'⟩ :=
    (inferInstance : HasCompactification (e.hom ≫ f)).nonempty_compactification
  apply shriekProperty_iso_source Λ e f L c c'
  have : SmoothOfRelativeDimension 1 (e.hom ≫ f) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (e.hom ≫ f))
  have : Scheme.IsFiniteLocallyConstantSheaf
      ((upperStar (ModuleCat.{u + 1} Λ) e.hom).obj L) :=
    Scheme.IsFiniteLocallyConstantSheaf.upperStar e.hom L
  exact shriekProperty_spec Λ R Γ(X, ⊤) (e.hom ≫ f) hΛ
    ((upperStar (ModuleCat.{u + 1} Λ) e.hom).obj L) c'

private theorem shriekProperty_sup
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} [IsNoetherian X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) (c : Compactification f)
    (hU : ∀ ca : Compactification (U.ι ≫ f),
      sourceProperty Λ ca (((upperStar (ModuleCat.{u + 1} Λ) U.ι).obj L)))
    (hV : ∀ ca : Compactification (V.ι ≫ f),
      sourceProperty Λ ca (((upperStar (ModuleCat.{u + 1} Λ) V.ι).obj L)))
    (hW : ∀ ca : Compactification ((U ⊓ V).ι ≫ f),
      sourceProperty Λ ca (((upperStar (ModuleCat.{u + 1} Λ) (U ⊓ V).ι).obj L))) :
    sourceProperty Λ c L := by
  let B := ModuleCat.{u + 1} Λ
  have hlocal (T : X.Opens)
      (h : ∀ ca : Compactification (T.ι ≫ f),
        sourceProperty Λ ca ((upperStar B T.ι).obj L)) :
      sourceProperty Λ c ((openImmersionLowerShriek B T.ι).obj
        ((upperStar B T.ι).obj L)) := by
    have : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp
      (TopologicalSpace.NoetherianSpace.isCompact (T : Set X))
    have : QuasiSeparatedSpace T.toScheme := T.ι.isOpenEmbedding.quasiSeparatedSpace
    obtain ⟨ca⟩ := (inferInstance : HasCompactification (T.ι ≫ f)).nonempty_compactification
    exact sourceProperty_openExtension Λ f c T
      (TopologicalSpace.NoetherianSpace.isCompact _) ca _ (h ca)
  obtain ⟨iU, iV, hS⟩ := exists_natural_shortExact_openCover_lowerShriek Λ U V hcover
  obtain ⟨hz, hs⟩ := hS L
  apply sourceProperty_shortExact_three Λ c _ hs (hlocal (U ⊓ V) hW)
  exact (sourceProperty Λ c).prop_of_iso (biprod.isoProd _ _).symm
    ((sourceProperty Λ c).prop_prod _ _ (hlocal U hU) (hlocal V hV))

private theorem shriekProperty_affine_cover
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (hΛ : ∀ (a : Λ) (s : Spec (.of R)), IsUnit (addOrderOf a : (Spec (.of R)).presheaf.stalk s))
    (n : ℕ) :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (.of R))
      [IsSeparated f] [SmoothOfRelativeDimension 1 f]
      (U : Fin (n + 1) → X.Opens), (∀ i, IsAffineOpen (U i)) → (⨆ i, U i) = ⊤ →
      ∀ (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        [Scheme.IsFiniteLocallyConstantSheaf L] (c : Compactification f),
        sourceProperty Λ c L := by
  induction n with
  | zero =>
    intro X _ f _ _ U hU hcov L _ c
    have h0 : U 0 = ⊤ := by simpa using hcov
    have : IsAffine X := by
      have : IsAffine (⊤ : X.Opens).toScheme := h0 ▸ hU 0
      exact .of_isIso X.topIso.inv
    exact shriekProperty_affine Λ R f hΛ L c
  | succ n ih =>
    intro X _ f _ _ U hU hcov L _ c
    have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
    have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
    let V₁ : X.Opens := ⨆ i : Fin (n + 1), U i.castSucc
    let V₂ : X.Opens := U (Fin.last _)
    have hV : V₁ ⊔ V₂ = ⊤ := by
      refine eq_top_iff.mpr (hcov.symm.le.trans (iSup_le fun i ↦ ?_))
      induction i using Fin.lastCases with
      | last => exact le_sup_right
      | cast i => exact (le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i).trans le_sup_left
    have hsep := isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal f))
      ⊤ (isAffineOpen_top (Spec (.of R)))
    have hsm (W : X.Opens) : SmoothOfRelativeDimension 1 (W.ι ≫ f) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (W.ι ≫ f))
    have hnoeth (W : X.Opens) : IsNoetherian W.toScheme := by
      have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp
        (TopologicalSpace.NoetherianSpace.isCompact (W : Set X))
      exact { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
    apply shriekProperty_sup Λ f L V₁ V₂ hV c
    · intro ca
      have := hsm V₁
      have := hnoeth V₁
      have : Scheme.IsFiniteLocallyConstantSheaf
          ((upperStar (ModuleCat.{u + 1} Λ) V₁.ι).obj L) :=
        Scheme.IsFiniteLocallyConstantSheaf.upperStar V₁.ι L
      have ha (i : Fin (n + 1)) : IsAffineOpen (V₁.ι ⁻¹ᵁ U i.castSucc) := by
        apply (hU _).preimage_of_isOpenImmersion
        rw [Scheme.Opens.opensRange_ι]
        exact le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i
      have hc : (⨆ i : Fin (n + 1), V₁.ι ⁻¹ᵁ U i.castSucc) = ⊤ := by
        rw [← Scheme.Hom.preimage_iSup, Scheme.Opens.ι_preimage_self]
      exact ih (X := V₁.toScheme) (V₁.ι ≫ f) (fun i ↦ V₁.ι ⁻¹ᵁ U i.castSucc)
        ha hc ((upperStar (ModuleCat.{u + 1} Λ) V₁.ι).obj L) ca
    · intro ca
      have : IsAffine V₂.toScheme := hU _
      have := hsm V₂
      have : Scheme.IsFiniteLocallyConstantSheaf
          ((upperStar (ModuleCat.{u + 1} Λ) V₂.ι).obj L) :=
        Scheme.IsFiniteLocallyConstantSheaf.upperStar V₂.ι L
      exact shriekProperty_affine Λ R (V₂.ι ≫ f) hΛ
        ((upperStar (ModuleCat.{u + 1} Λ) V₂.ι).obj L) ca
    · intro ca
      have := hsm (V₁ ⊓ V₂)
      have := hnoeth (V₁ ⊓ V₂)
      have : Scheme.IsFiniteLocallyConstantSheaf
          ((upperStar (ModuleCat.{u + 1} Λ) (V₁ ⊓ V₂).ι).obj L) :=
        Scheme.IsFiniteLocallyConstantSheaf.upperStar (V₁ ⊓ V₂).ι L
      have ha (i : Fin (n + 1)) :
          IsAffineOpen ((V₁ ⊓ V₂).ι ⁻¹ᵁ (U i.castSucc ⊓ V₂)) := by
        apply (hsep _ (by simp) _ (by simp) (hU _) (hU _)).preimage_of_isOpenImmersion
        rw [Scheme.Opens.opensRange_ι]
        exact inf_le_inf_right _ (le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i)
      have hc : (⨆ i : Fin (n + 1), (V₁ ⊓ V₂).ι ⁻¹ᵁ (U i.castSucc ⊓ V₂)) = ⊤ := by
        rw [← Scheme.Hom.preimage_iSup, ← iSup_inf_eq, Scheme.Opens.ι_preimage_self]
      exact ih (X := (V₁ ⊓ V₂).toScheme) ((V₁ ⊓ V₂).ι ≫ f)
        (fun i ↦ (V₁ ⊓ V₂).ι ⁻¹ᵁ (U i.castSucc ⊓ V₂)) ha hc
        ((upperStar (ModuleCat.{u + 1} Λ) (V₁ ⊓ V₂).ι).obj L) ca

end StableInstances

/-- Lisse sheaves with finite module values on an open relative affine line over a
finite-type integer base, on which the additive orders of the coefficients are invertible,
have constructible compactly supported cohomology sheaves. -/
theorem isConstructibleEtaleModuleSheaf_lisse_openRelativeLine_shriek
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (hΛ : ∀ (a : Λ) (s : Spec (.of R)), IsUnit (addOrderOf a : (Spec (.of R)).presheaf.stalk s))
    (U : (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))).Opens)
    (L : Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hL : ∃ d : Scheme.LocallyConstantDatum L, ∀ i : d.cover.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty ((L.over (d.cover.etalePrecoverageToEtale i)) ≅
          (constantSheaf
            (U.toScheme.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} Λ)).obj M))
    (c : Compactification
      (U.ι ≫ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))))
    (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj L))) := by
  classical
  let : ∀ X : Scheme.{u}, Abelian
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := etaleSheafModuleAbelian Λ
  let : ∀ X : Scheme.{u}, HasDerivedCategory.{u + 1}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := etaleSheafModuleHasDerivedCategory Λ
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  let X := U.toScheme
  let f := U.ι ≫ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))
  have : SmoothOfRelativeDimension 1
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over
      (ULift.{u} (Fin 1)) (Spec (.of R))
  have : Smooth (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R)) :=
    SmoothOfRelativeDimension.smooth 1 _
  have : IsLocallyNoetherian (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))
  have : IsNoetherian (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))) :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  have : SmoothOfRelativeDimension 1 f :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) f)
  have : Scheme.IsFiniteLocallyConstantSheaf L :=
    (Scheme.finite_locally_constant_module_values_iff L).1.mp hL
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact
      (U : Set (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)))))
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun W : X.affineOpens ↦ (W : Set X)) (fun W ↦ W.1.isOpen) (by
      intro x _
      have hx : x ∈ (⨆ W : X.affineOpens, (W : X.Opens)) := by
        rw [iSup_affineOpens_eq_top X]
        trivial
      obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨W, hW⟩)
  let V : Fin (s.card + 1) → X.Opens := Fin.cons ⊥ fun i ↦ (s.equivFin.symm i).1.1
  have hV (i : Fin (s.card + 1)) : IsAffineOpen (V i) := by
    induction i using Fin.cases with
    | zero => exact isAffineOpen_bot X
    | succ i => exact (s.equivFin.symm i).1.2
  have hcov : (⨆ i, V i) = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨W, hW, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨(s.equivFin ⟨W, hW⟩).succ, by simpa [V] using hx⟩
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  have h := shriekProperty_affine_cover Λ R hΛ s.card (X := X) f V hV hcov L c
  unfold sourceProperty cohomologySourceProperty sourceFunctor shriekFunctor at h
  exact h q

end AlgebraicGeometry.Etale
