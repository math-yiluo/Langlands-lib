/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.CategoryTheory.Sites.ReductionFlat
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import all WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact

/-! # Exceptional coefficient comparisons

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (2)--(3); Stacks 0GL6 and 0F7L
(blueprint: lem-pur-exceptional-coefficient-comparison).

All scalar functors are the published left adjoints to exact scalar restriction.
The scalar/pullback identification and the proper coefficient map are the recorded
`scalarPullbackIso` and `scalarMate` of lem-pur-etale-scalar-mate-projection.
The comparison for compact support is constructed from its open and proper parts.
The auxiliary tensor and pullback identifications are fixed by their ordinary
adjunctions and their computation on cochain representatives.

(blueprint: def-pur-exceptional-coefficient-normalizations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
namespace ExceptionalCoefficients

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)

/-- Scalar extension and open extension by zero are left adjoint to canonically
identified right adjoints; uniqueness gives the identity/zero comparison.
Source: Stacks 0GL6 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def openIso {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        scalarExtension φ Z ≅
      scalarExtension φ X ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  (conjugateIsoEquiv
    (((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm).comp
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)))
    ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).comp
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).symm))).symm
    (scalarRestrictionPullbackIso φ j) |>.symm

/-- The canonical compact-support coefficient arrow, on a fixed compactification: the
recorded proper coefficient mate `scalarMate` at the open extension, followed by
proper direct image of the open comparison.
Source: Stacks 0GL6 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def compactSupportMap {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ Y).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((scalarExtension φ X).obj M) :=
  (scalarMate φ c.g).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) ≫
    (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
      ((openIso φ c.i).hom.app M)

/-- Inverse of the canonical comparison on its isomorphism domain, extended by zero.
This extension only makes the term total; every theorem use is on the domain where
b is an isomorphism. Source: Stacks 0GL6
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def comparisonInverse {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((scalarExtension φ X).obj M) ⟶
      (scalarExtension φ Y).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) :=
  open Classical in
  if h : IsIso (compactSupportMap φ c M) then
    @inv _ _ _ _ (compactSupportMap φ c M) h
  else 0

/-- A total extension of the counit-transpose construction; its zero fallback is
irrelevant on the stated domain, where the theorem proves invertibility of b.
Source: blueprint compatibilities (2)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def mateMap [Finite A] [Finite B] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (K : DerivedCategoryModule A Y) :
    (scalarExtension φ X).obj ((rightDerivedUpperShriek A f).obj K) ⟶
      (rightDerivedUpperShriek B f).obj ((scalarExtension φ Y).obj K) :=
  (rightDerivedUpperShriekAdjunction B f).homEquiv _ _
    (comparisonInverse φ (HasCompactification.compactification f)
      ((rightDerivedUpperShriek A f).obj K) ≫
      (scalarExtension φ Y).map
        ((rightDerivedUpperShriekAdjunction A f).counit.app K))

/-- The ordinary extension has its actual scalar-restriction adjunction.
Source: Stacks 06YY (blueprint: lem-pur-exceptional-coefficient-comparison). -/
instance ordinaryIsLeftAdjoint (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ T).IsLeftAdjoint :=
  (ProEtale.etaleSheafExtendScalarsAdjunction φ T).isLeftAdjoint

/-- The ordinary tensorator is the sheafified scalar balancing map.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
instance ordinaryOplax (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ T).OplaxMonoidal :=
  composeAndSheafifyOplaxMonoidal T.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)

/-- Representative normalization for a scalar tensor comparison, with monoidal data
kept shared in both categories. Source: Stacks 07A4
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def TensorNormalizationAux
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E ≅
      E.prod E ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D))) : Prop :=
  ∀ P Q : CochainComplex C ℤ,
    δ.hom.app (_root_.DerivedCategory.Q.obj P, _root_.DerivedCategory.Q.obj Q) ≫
        (rep P ⊗ₘ rep Q) ≫ Functor.LaxMonoidal.μ _root_.DerivedCategory.Q
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) =
      E.map (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q P Q) ≫ rep (P ⊗ Q) ≫
        _root_.DerivedCategory.Q.map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q)

/-- The all-complex normalization with site tensor functors kept as shared constants.
This is exactly `TensorNormalizationAux` on the small etale sheaf categories.
Keeping its monoidal arguments inside this generic body avoids repeated comparison
of the nested sheafification and derived-monoidal proofs in specialized theorem types.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def SiteTensorNormalizationAux
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (D : Type w) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [Abelian.HasFunctorialFlatResolution D] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology C ⥤ Sheaf T.smallEtaleTopology D)
    [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (S : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology D))
    (r : ∀ P : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ,
      S.obj (_root_.DerivedCategory.Q.obj P) ⟶
        _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : Functor.uncurry.obj (derivedTensor C T) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (derivedTensor D T)) : Prop :=
  TensorNormalizationAux F S r δ

/-- Small-etale specialization of the shared all-complex tensor normalization.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
abbrev TensorNormalization (T : Scheme.{u}) :=
  SiteTensorNormalizationAux (ModuleCat.{u + 1} A) (ModuleCat.{u + 1} B) T
    (ProEtale.etaleSheafExtendScalars φ T)
    (scalarExtension φ T) (scalarExtensionRepresentative φ T)

private theorem mapComplex_unit_formula
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {E : C ⥤ D} {U : D ⥤ C} [E.Additive] [U.Additive] (adj : E ⊣ U)
    (P : CochainComplex C ℤ) :
    (adj.mapHomologicalComplex (.up ℤ)).unit.app P =
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P := by
  ext i
  simp only [Functor.id_obj, Functor.comp_obj, Adjunction.mapHomologicalComplex_unit_app_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexIdIso_inv_app_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  exact (Category.comp_id _).symm

open AlgebraicGeometry AlgebraicGeometry.Etale
open MonoidalCategory Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ u₂
private def productLaxTensorator
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] :
    F.prod F ⋙ Functor.uncurry.obj (curriedTensor D) ⟶
      Functor.uncurry.obj (curriedTensor C) ⋙ F where
  app X := Functor.LaxMonoidal.μ F X.1 X.2
  naturality X Y f := by
    have h := Functor.LaxMonoidal.μ_natural F f.1 f.2
    rw [MonoidalCategory.tensorHom_def (F.map f.1) (F.map f.2),
      MonoidalCategory.tensorHom_def f.1 f.2] at h
    simpa only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
      Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map] using h

private def productOplaxTensorator
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D)
    (τ : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj U) :
    Functor.uncurry.obj T ⋙ F ⟶ F.prod F ⋙ Functor.uncurry.obj U where
  app X := (τ.app X.1).app X.2
  naturality X Y f := by
    change F.map ((T.map f.1).app X.2 ≫ (T.obj Y.1).map f.2) ≫ _ =
      _ ≫ ((U.map (F.map f.1)).app (F.obj X.2) ≫ (U.obj (F.obj Y.1)).map (F.map f.2))
    rw [F.map_comp, Category.assoc]
    have h₁ := congr_app (τ.naturality f.1) X.2
    have h₂ := (τ.app Y.1).naturality f.2
    change F.map ((T.map f.1).app X.2) ≫ (τ.app Y.1).app X.2 =
      (τ.app X.1).app X.2 ≫ (U.map (F.map f.1)).app (F.obj X.2) at h₁
    change F.map ((T.obj Y.1).map f.2) ≫ (τ.app Y.1).app Y.2 =
      (τ.app Y.1).app X.2 ≫ (U.obj (F.obj Y.1)).map (F.map f.2) at h₂
    rw [h₂, ← Category.assoc, h₁, Category.assoc]

private def productIsoOfFamily
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D)
    (μ : ∀ K L : C, (U.obj (F.obj K)).obj (F.obj L) ≅ F.obj ((T.obj K).obj L))
    (h₁ : ∀ {K K'} (f : K ⟶ K') L,
      (U.map (F.map f)).app (F.obj L) ≫ (μ K' L).hom =
        (μ K L).hom ≫ F.map ((T.map f).app L))
    (h₂ : ∀ K {L L'} (f : L ⟶ L'),
      (U.obj (F.obj K)).map (F.map f) ≫ (μ K L').hom =
        (μ K L).hom ≫ F.map ((T.obj K).map f)) :
    Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj U :=
  (NatIso.ofComponents (fun X ↦ μ X.1 X.2) (by
    intro X Y f
    change ((U.map (F.map f.1)).app (F.obj X.2) ≫
      (U.obj (F.obj Y.1)).map (F.map f.2)) ≫ (μ Y.1 Y.2).hom =
      (μ X.1 X.2).hom ≫ F.map ((T.map f.1).app X.2 ≫ (T.obj Y.1).map f.2)
    rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc, ← F.map_comp])).symm

private theorem productIso_natural₁
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D)
    (δ : Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj U)
    {K K' : C} (f : K ⟶ K') (L : C) :
    (U.map (F.map f)).app (F.obj L) ≫ (δ.app (K', L)).inv =
      (δ.app (K, L)).inv ≫ F.map ((T.map f).app L) := by
  have h := δ.inv.naturality (show (K, L) ⟶ (K', L) from (f, 𝟙 L))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at h
  simpa only [_root_.CategoryTheory.Functor.map_id, Functor.comp_obj, Functor.uncurry_obj_obj,
    Functor.prod_obj, Iso.app_inv, Category.comp_id] using h

private theorem productIso_natural₂
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D)
    (δ : Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj U)
    (K : C) {L L' : C} (f : L ⟶ L') :
    (U.obj (F.obj K)).map (F.map f) ≫ (δ.app (K, L')).inv =
      (δ.app (K, L)).inv ≫ F.map ((T.obj K).map f) := by
  have h := δ.inv.naturality (show (K, L) ⟶ (K, L') from (𝟙 K, f))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at h
  simpa only [_root_.CategoryTheory.Functor.map_id, Functor.comp_obj, Functor.uncurry_obj_obj,
    Functor.prod_obj, Iso.app_inv, NatTrans.id_app, Category.id_comp] using h

private theorem tensor_normalization_flat
    {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (r : ∀ P : CochainComplex C ℤ, E.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E ≅
      E.prod E ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D)))
    (hn : TensorNormalizationAux F E r δ) :
    Functor.rightExactTensorModelNormalization F E r
      (fun K L ↦ (δ.app (K, L)).symm) := by
  intro P Q _ _ _ _
  exact (hn P Q).symm

private theorem tensor_normalization_all_of_flat
    {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (r : _root_.DerivedCategory.Q ⋙ E ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q)
    (δ : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E ≅
      E.prod E ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D)))
    (hflat : Functor.rightExactTensorModelNormalization F E r.app
      (fun K L ↦ (δ.app (K, L)).symm)) :
    AlgebraicGeometry.Etale.ExceptionalCoefficients.TensorNormalizationAux F E r.app δ := by
  let QC := _root_.DerivedCategory.Q (C := C)
  let QD := _root_.DerivedCategory.Q (C := D)
  let FC := F.mapHomologicalComplex (.up ℤ)
  let α : QC.prod QC ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E ⟶
      FC.prod FC ⋙ Functor.uncurry.obj (curriedTensor (CochainComplex D ℤ)) ⋙ QD :=
    Functor.whiskerLeft (QC.prod QC) δ.hom ≫
      Functor.whiskerRight (r.prod r)
        (Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D))) ≫
      Functor.whiskerLeft (FC.prod FC)
        (productLaxTensorator QD)
  let β : QC.prod QC ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E ⟶
      FC.prod FC ⋙ Functor.uncurry.obj (curriedTensor (CochainComplex D ℤ)) ⋙ QD :=
    Functor.whiskerRight (productLaxTensorator QC) E ≫
      Functor.whiskerLeft (Functor.uncurry.obj (curriedTensor (CochainComplex C ℤ))) r ≫
      Functor.whiskerRight
        (productOplaxTensorator (curriedTensor (CochainComplex C ℤ))
          (curriedTensor (CochainComplex D ℤ)) FC
          (Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F)) QD
  intro P Q
  have hab : α.app (P, Q) = β.app (P, Q) := by
    obtain ⟨P', π, hπ, hPflat, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat P
    obtain ⟨Q', ρ, hρ, hQflat, hQ⟩ := CochainComplex.exists_quasiIso_flat_kFlat Q
    have : IsIso (QC.map π) := by
      exact Localization.inverts QC (HomologicalComplex.quasiIso C (.up ℤ)) π hπ
    have : IsIso (QC.map ρ) := by
      exact Localization.inverts QC (HomologicalComplex.quasiIso C (.up ℤ)) ρ hρ
    have hi : IsIso
        ((QC.prod QC ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E).map
          (show (P', Q') ⟶ (P, Q) from (π, ρ))) := by
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj, Functor.uncurry_obj_map,
        curriedTensor_map_app, curriedTensor_obj_map]
      rw [← MonoidalCategory.tensorHom_def (QC.map π) (QC.map ρ)]
      infer_instance
    apply (cancel_epi
      ((QC.prod QC ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E).map
        (show (P', Q') ⟶ (P, Q) from (π, ρ)))).1
    rw [α.naturality, β.naturality]
    have h : α.app (P', Q') = β.app (P', Q') := by
      simpa only [α, β, QC, QD, FC, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.prod_obj, Functor.uncurry_obj_obj,
        Functor.uncurry_obj_map, NatTrans.prod_app_fst, NatTrans.prod_app_snd, Functor.comp_obj,
        productLaxTensorator,
        productOplaxTensorator, curriedTensor_map_app, curriedTensor_obj_map,
        MonoidalCategory.tensorHom_def, curriedTensor_obj_obj,
        Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, Iso.symm_inv, Iso.app_hom,
        Category.assoc] using (hflat P' Q' hP hQ hPflat hQflat).symm
    rw [h]
  simpa only [α, β, QC, QD, FC, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.prod_obj, Functor.uncurry_obj_obj,
    Functor.uncurry_obj_map, NatTrans.prod_app_fst, NatTrans.prod_app_snd, Functor.comp_obj,
        productLaxTensorator,
    productOplaxTensorator, curriedTensor_map_app, curriedTensor_obj_map,
    MonoidalCategory.tensorHom_def, curriedTensor_obj_obj,
        Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, Iso.symm_inv, Iso.app_hom,
    Category.assoc] using hab

private theorem tensor_normalization_all_onSite
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (D : Type w) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [Abelian.HasFunctorialFlatResolution D] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology C ⥤ Sheaf T.smallEtaleTopology D)
    [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (S : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology D))
    (r : _root_.DerivedCategory.Q ⋙ S ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q)
    (δ : Functor.uncurry.obj (derivedTensor C T) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (derivedTensor D T))
    (hflat : AlgebraicGeometry.Etale.EtaleHomTensorModelNormalization C D T F S r.app
      (fun K L ↦ (δ.app (K, L)).symm)) :
    AlgebraicGeometry.Etale.ExceptionalCoefficients.SiteTensorNormalizationAux C D T F S
      r.app δ := by
  exact tensor_normalization_all_of_flat F S r δ hflat

private theorem site_normalization_flat
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (D : Type w) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [Abelian.HasFunctorialFlatResolution D] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology C ⥤ Sheaf T.smallEtaleTopology D)
    [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (S : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology D))
    (r : ∀ P : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ,
      S.obj (_root_.DerivedCategory.Q.obj P) ⟶
        _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : Functor.uncurry.obj (derivedTensor C T) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (derivedTensor D T))
    (hn : AlgebraicGeometry.Etale.ExceptionalCoefficients.SiteTensorNormalizationAux
      C D T F S r δ) :
    EtaleHomTensorModelNormalization C D T F S r
      (fun K L ↦ (δ.app (K, L)).symm) := by
  exact tensor_normalization_flat F S r δ hn

private def adjointRepresentative
    {C D V W : Type*} [Category C] [Category D] [Category V] [Category W]
    (QC : C ⥤ V) (QD : D ⥤ W) (FC : C ⥤ D) (UC : D ⥤ C)
    (E : V ⥤ W) (U : W ⥤ V) (adj : E ⊣ U)
    (a : FC ⊣ UC) (fac : UC ⋙ QC ≅ QD ⋙ U) : QC ⋙ E ⟶ FC ⋙ QD := by
  let t : QC ⟶ FC ⋙ QD ⋙ U :=
    Functor.whiskerRight a.unit QC ≫ Functor.whiskerLeft FC fac.hom
  exact {
    app P := (adj.homEquiv _ _).symm (t.app P)
    naturality P Q f := by
      change E.map (QC.map f) ≫ _ = _ ≫ QD.map (FC.map f)
      calc
        _ = (adj.homEquiv _ _).symm (QC.map f ≫ t.app Q) :=
          (adj.homEquiv_naturality_left_symm (QC.map f) (t.app Q)).symm
        _ = (adj.homEquiv _ _).symm (t.app P ≫ U.map (QD.map (FC.map f))) :=
          congrArg (adj.homEquiv _ _).symm (t.naturality f)
        _ = _ := adj.homEquiv_naturality_right_symm _ _ }

/-- The canonical scalar tensor isomorphism is determined by ordinary balancing.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison).
Proof: on flat-term K-flat pairs the counits and the localization tensorators
are invertible. Ordinary balancing therefore defines δ by the displayed equation.
It commutes with resolutions and differentials. Localize in both variables to obtain
a natural isomorphism. Every pair admits such resolutions, proving uniqueness;
naturality with respect to a resolution proves the equation for all complexes. -/
theorem tensorIso_existsUnique (T : Scheme.{u}) :
    ∃! δ, TensorNormalization φ T δ := by
  let E := ProEtale.etaleSheafExtendScalars φ T
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  let ad : scalarExtension φ T ⊣ U.mapDerivedCategory := Adjunction.ofIsRightAdjoint _
  let r := adjointRepresentative _root_.DerivedCategory.Q
    _root_.DerivedCategory.Q (E.mapHomologicalComplex (.up ℤ))
    (U.mapHomologicalComplex (.up ℤ)) (scalarExtension φ T) U.mapDerivedCategory ad
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).mapHomologicalComplex (.up ℤ))
    U.mapDerivedCategoryFactors.symm
  have hr' : r.app = scalarExtensionRepresentative φ T := by
    funext P
    unfold scalarExtensionRepresentative
    rw [← mapComplex_unit_formula]
    rfl
  obtain ⟨μ, hμ, hμuniq⟩ := etaleHomTensorComparison_existsUnique T φ
  let δ := productIsoOfFamily
    (derivedTensor (ModuleCat.{u + 1} A) T) (derivedTensor (ModuleCat.{u + 1} B) T)
    (scalarExtension φ T) μ hμ.1 hμ.2.1
  have hflat : EtaleHomTensorModelNormalization (ModuleCat.{u + 1} A)
      (ModuleCat.{u + 1} B) T E (scalarExtension φ T) r.app
      (fun K L ↦ (δ.app (K, L)).symm) := by
    rw [hr']
    exact hμ.2.2
  have hδ : TensorNormalization φ T δ := by
    have h := tensor_normalization_all_onSite (ModuleCat.{u + 1} A)
      (ModuleCat.{u + 1} B) T E (scalarExtension φ T) r δ hflat
    rw [hr'] at h
    exact h
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  have hεcanonical : IsEtaleHomTensorCanonical T φ
      (fun K L ↦ (ε.app (K, L)).symm) := by
    refine ⟨productIso_natural₁ _ _ _ ε,
      productIso_natural₂ _ _ _ ε, ?_⟩
    exact site_normalization_flat (ModuleCat.{u + 1} A)
      (ModuleCat.{u + 1} B) T E (scalarExtension φ T)
      (scalarExtensionRepresentative φ T) ε hε
  have hεμ := hμuniq _ hεcanonical
  apply Iso.ext
  apply NatTrans.ext
  funext ⟨K, L⟩
  have h := congrFun (congrFun hεμ K) L
  exact congrArg Iso.inv h

/-- The same normalized tensor comparison, expressed using the site's tensor functor.
The heterogeneous equality asserts equality of the very same natural isomorphism,
including its endpoints, rather than choosing an unrelated comparison.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison).
Proof: unfold derivedTensor, which is curriedTensor of the canonical derived
monoidal structure. The normalized isomorphism from tensorIso_existsUnique
therefore has exactly this type. Reflexive heterogeneous equality supplies the
witness, and heterogeneous equality to that fixed witness implies uniqueness.
Keeping the transport opaque prevents expansion of the full monoidal structure. -/
theorem siteTensorIso_existsUnique (T : Scheme.{u}) :
    ∃! e : Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) T) ⋙
        scalarExtension φ T ≅
      (scalarExtension φ T).prod (scalarExtension φ T) ⋙
        Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} B) T),
      HEq e (tensorIso_existsUnique φ T).choose := by
  exact ⟨(tensorIso_existsUnique φ T).choose, HEq.rfl, fun _ h ↦ eq_of_heq h⟩

/-- The site's tensor comparison, uniquely equal to the representative-normalized one.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def tensorIso (T : Scheme.{u}) :
    Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) T) ⋙ scalarExtension φ T ≅
      (scalarExtension φ T).prod (scalarExtension φ T) ⋙
        Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} B) T) :=
  (siteTensorIso_existsUnique φ T).choose

/-- Unit normalization using shared monoidal data for the ordinary scalar functor.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def UnitNormalizationAux
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (e : E.obj (𝟙_ _) ≅ 𝟙_ _) : Prop :=
  E.map (Functor.LaxMonoidal.ε _root_.DerivedCategory.Q) ≫ rep (𝟙_ _) ≫
      _root_.DerivedCategory.Q.map (Functor.OplaxMonoidal.mapHomologicalComplexη (.up ℤ) F) =
    e.hom ≫ Functor.LaxMonoidal.ε _root_.DerivedCategory.Q

/-- Specialization of scalar-unit normalization to the ordinary small-etale site.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
abbrev UnitNormalization (T : Scheme.{u}) :=
  UnitNormalizationAux (ProEtale.etaleSheafExtendScalars φ T)
    (scalarExtension φ T) (scalarExtensionRepresentative φ T)

private theorem extension_preservesKFlatQuasiIso {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) (X : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ X).PreservesKFlatQuasiIso := by
  exact AlgebraicGeometry.Etale.extension_preservesKFlatQuasiIso φ X

private theorem derivedUnit_isIso
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C] :
    IsIso (Functor.LaxMonoidal.ε (_root_.DerivedCategory.Q (C := C))) := by
  let := _root_.DerivedCategory.isIso_ε_Qh C
  change IsIso ((Functor.LaxMonoidal.ε _root_.DerivedCategory.Qh ≫
    _root_.DerivedCategory.Qh.map
      (Functor.LaxMonoidal.ε (HomotopyCategory.quotient _ _))) ≫ _)
  infer_instance

private theorem unitNormalizationAux_existsUnique
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    [IsIso (Functor.OplaxMonoidal.η F)]
    (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    [IsIso (rep (𝟙_ _))] : ∃! e, UnitNormalizationAux F E rep e := by
  have hC : IsIso (Functor.LaxMonoidal.ε (_root_.DerivedCategory.Q (C := C))) :=
    derivedUnit_isIso
  have hD : IsIso (Functor.LaxMonoidal.ε (_root_.DerivedCategory.Q (C := D))) :=
    derivedUnit_isIso
  have hη : IsIso (Functor.OplaxMonoidal.mapHomologicalComplexη (.up ℤ) F) := by
    unfold Functor.OplaxMonoidal.mapHomologicalComplexη
    infer_instance
  let a := E.map (Functor.LaxMonoidal.ε _root_.DerivedCategory.Q) ≫ rep (𝟙_ _) ≫
    _root_.DerivedCategory.Q.map
      (Functor.OplaxMonoidal.mapHomologicalComplexη (.up ℤ) F)
  let b := Functor.LaxMonoidal.ε (_root_.DerivedCategory.Q (C := D))
  have : IsIso a := by dsimp only [a]; infer_instance
  refine ⟨asIso a ≪≫ (asIso b).symm, ?_, ?_⟩
  · change a = (a ≫ inv b) ≫ b
    simp
  · intro e he
    apply Iso.ext
    apply (cancel_mono b).1
    change e.hom ≫ b = (a ≫ inv b) ≫ b
    change a = e.hom ≫ b at he
    rw [← he]
    simp

private theorem unit_normalization_existsUnique_onSite
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (D : Type w) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [Abelian.HasFunctorialFlatResolution D] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology C ⥤ Sheaf T.smallEtaleTopology D)
    [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (E : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology D))
    (rep : ∀ P : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ,
      E.obj (_root_.DerivedCategory.Q.obj P) ⟶
        _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    [IsIso (Functor.OplaxMonoidal.η F)] [IsIso (rep (𝟙_ _))] :
    ∃! e, UnitNormalizationAux F E rep e := by
  exact unitNormalizationAux_existsUnique F E rep

private theorem representative_isIso_of_kFlat
    {C : Type v} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : E ⊣ U) {L : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D}
    (ad : L ⊣ U.mapDerivedCategory) (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso ((ad.homEquiv _ _).symm
      (_root_.DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P) ≫
        U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P))) := by
  rw [← mapComplex_unit_formula]
  have := E.isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  rw [← Adjunction.leftDerivedCochainCounit E U adj ad P]
  infer_instance

private theorem unitRepresentative_isIso (T : Scheme.{u}) :
    IsIso (scalarExtensionRepresentative φ T
      (𝟙_ (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ))) := by
  let : (ProEtale.etaleSheafExtendScalars φ T).PreservesKFlatQuasiIso :=
    extension_preservesKFlatQuasiIso φ T
  exact representative_isIso_of_kFlat (ProEtale.etaleSheafExtendScalars φ T)
    (Sheaf.restrictScalars T.smallEtaleTopology φ)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ T)
    (Adjunction.ofIsRightAdjoint _) _
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat.prop_unit

/-- The scalar unit comparison is uniquely normalized by multiplication B tensor_A A -> B.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison).
Proof: the unit complex is flat and K-flat. Its derived counit, the localization
unit comparison and ordinary scalar unit are invertible. Solve the normalization
equation for e; cancellation gives uniqueness. -/
theorem unitIso_existsUnique (T : Scheme.{u}) :
    ∃! e, UnitNormalization φ T e := by
  have hrep := unitRepresentative_isIso φ T
  have hη : IsIso (Functor.OplaxMonoidal.η (ProEtale.etaleSheafExtendScalars φ T)) := by
    exact isIso_η_composeAndSheafify T.smallEtaleTopology
      (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)
  exact unit_normalization_existsUnique_onSite (ModuleCat.{u + 1} A)
    (ModuleCat.{u + 1} B) T (ProEtale.etaleSheafExtendScalars φ T)
    (scalarExtension φ T) (scalarExtensionRepresentative φ T)

/-- Canonical scalar unit identification, selected by its unique normalization.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def unitIso (T : Scheme.{u}) :
    (scalarExtension φ T).obj (𝟙_ (DerivedCategoryModule A T)) ≅
      𝟙_ (DerivedCategoryModule B T) :=
  (unitIso_existsUnique φ T).choose

end ExceptionalCoefficients
end AlgebraicGeometry.Etale
