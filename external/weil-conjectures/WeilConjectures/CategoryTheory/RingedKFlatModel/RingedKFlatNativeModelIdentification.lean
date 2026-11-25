/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
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
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import all WeilConjectures.CategoryTheory.Ringed.RingedOrdinaryEvaluationLocalization
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod

/-! # Identification of ringed and native K-flat tensor models

Source: Stacks Project, Cohomology on Sites, Tags 06YP, 06YT, 06YU and 0FPT.
(blueprint: lem-pd-ringed-kflat-native-model-identification).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u w d h

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory WeilConjectures
open scoped ZeroObject

namespace CategoryTheory.RingedKFlatModel

private theorem isoPair {D : Type d} [Category.{h} D]
    {X Y Z W : D} (f : X ⟶ Y) (g : Z ⟶ W) [IsIso f] [IsIso g] :
    @IsIso (D × D) _ (X, Z) (Y, W) (f, g) :=
  (isIso_prod_iff (f := ((f, g) : (X, Z) ⟶ (Y, W)))).mpr ⟨inferInstance, inferInstance⟩

attribute [local instance] isoPair

section ConstraintPaths
variable {D : Type d} [Category.{h} D]

private def leftInput (a : MonoidalCategory D) : D × D × D ⥤ D × D where
  obj X := (a.tensorObj X.1 X.2.1, X.2.2)
  map {X Y} f := ((@tensor D _ a).map (X := (X.1, X.2.1))
    (Y := (Y.1, Y.2.1)) (f.1, f.2.1), f.2.2)

private def rightInput (a : MonoidalCategory D) : D × D × D ⥤ D × D where
  obj X := (X.1, a.tensorObj X.2.1 X.2.2)
  map {X Y} f := (f.1, (@tensor D _ a).map (X := (X.2.1, X.2.2))
    (Y := (Y.2.1, Y.2.2)) (f.2.1, f.2.2))

private def leftInner {a r : MonoidalCategory D} (e : @tensor D _ a ≅ @tensor D _ r) :
    leftInput a ⟶ leftInput r where
  app X := (e.hom.app (X.1, X.2.1), 𝟙 X.2.2)
  naturality {X Y} f := by
    apply Prod.ext
    · exact e.hom.naturality (X := (X.1, X.2.1)) (Y := (Y.1, Y.2.1)) (f.1, f.2.1)
    · simp [leftInput]

private def rightInner {a r : MonoidalCategory D} (e : @tensor D _ a ≅ @tensor D _ r) :
    rightInput a ⟶ rightInput r where
  app X := (𝟙 X.1, e.hom.app (X.2.1, X.2.2))
  naturality {X Y} f := by
    apply Prod.ext
    · simp [rightInput]
    · exact e.hom.naturality (X := (X.2.1, X.2.2))
        (Y := (Y.2.1, Y.2.2)) (f.2.1, f.2.2)

private def associatorLeft {a r : MonoidalCategory D}
    (e : @tensor D _ a ≅ @tensor D _ r) :
    @leftAssocTensor D _ a ⟶ @rightAssocTensor D _ r :=
  Functor.whiskerLeft (leftInput a) e.hom ≫
    Functor.whiskerRight (leftInner (a := a) (r := r) e) (@tensor D _ r) ≫
      (@associatorNatIso D _ r).hom

private def associatorRight {a r : MonoidalCategory D}
    (e : @tensor D _ a ≅ @tensor D _ r) :
    @leftAssocTensor D _ a ⟶ @rightAssocTensor D _ r :=
  (@associatorNatIso D _ a).hom ≫
    Functor.whiskerLeft (rightInput a) e.hom ≫
      Functor.whiskerRight (rightInner (a := a) (r := r) e) (@tensor D _ r)

private def unitLeftInput (I : D) : D ⥤ D × D where
  obj X := (I, X)
  map f := (𝟙 I, f)

private def unitRightInput (I : D) : D ⥤ D × D where
  obj X := (X, I)
  map f := (f, 𝟙 I)

private def unitLeftInner {I U : D} (u : I ⟶ U) : unitLeftInput I ⟶ unitLeftInput U where
  app X := (u, 𝟙 X)
  naturality {X Y} f := by apply Prod.ext <;> simp [unitLeftInput]

private def unitRightInner {I U : D} (u : I ⟶ U) : unitRightInput I ⟶ unitRightInput U where
  app X := (𝟙 X, u)
  naturality {X Y} f := by apply Prod.ext <;> simp [unitRightInput]

private def leftUnitNat (a : MonoidalCategory D) :
    unitLeftInput a.tensorUnit ⋙ @tensor D _ a ⟶ 𝟭 D where
  app X := (a.leftUnitor X).hom
  naturality {X Y} f := by
    let := a
    change (𝟙 (𝟙_ D) ⊗ₘ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f
    simpa only [id_tensorHom] using leftUnitor_naturality f

private def rightUnitNat (a : MonoidalCategory D) :
    unitRightInput a.tensorUnit ⋙ @tensor D _ a ⟶ 𝟭 D where
  app X := (a.rightUnitor X).hom
  naturality {X Y} f := by
    let := a
    change (f ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f
    simpa only [tensorHom_id] using rightUnitor_naturality f

private def unitLeftPath (a : MonoidalCategory D) {I : D} (u : a.tensorUnit ≅ I) :
    unitLeftInput I ⋙ @tensor D _ a ⟶ 𝟭 D :=
  Functor.whiskerRight (unitLeftInner u.inv) (@tensor D _ a) ≫
    leftUnitNat a

private def unitRightPath (a : MonoidalCategory D) {I : D} (u : a.tensorUnit ≅ I) :
    unitRightInput I ⋙ @tensor D _ a ⟶ 𝟭 D :=
  Functor.whiskerRight (unitRightInner u.inv) (@tensor D _ a) ≫
    rightUnitNat a

private theorem map_comparison_left {a r : MonoidalCategory D}
    (e : @tensor D _ a ≅ @tensor D _ r) {L X Y Z : D}
    (f : L ⟶ a.tensorObj X Y) :
    (@tensor D _ a).map (X := (L, Z)) (Y := (a.tensorObj X Y, Z)) (f, 𝟙 Z) ≫
      e.hom.app (a.tensorObj X Y, Z) ≫
      (@tensor D _ r).map (X := (a.tensorObj X Y, Z))
        (Y := (r.tensorObj X Y, Z)) (e.hom.app (X, Y), 𝟙 Z) =
    e.hom.app (L, Z) ≫ (@tensor D _ r).map (X := (L, Z))
        (Y := (r.tensorObj X Y, Z)) (f ≫ e.hom.app (X, Y), 𝟙 Z) := by
  rw [e.hom.naturality_assoc]
  rw [← Functor.map_comp, prod_comp, Category.id_comp]

private theorem map_comparison_right {a r : MonoidalCategory D}
    (e : @tensor D _ a ≅ @tensor D _ r) {L X Y Z : D}
    (g : L ⟶ a.tensorObj Y Z) :
    (@tensor D _ a).map (X := (X, L)) (Y := (X, a.tensorObj Y Z)) (𝟙 X, g) ≫
      e.hom.app (X, a.tensorObj Y Z) ≫
      (@tensor D _ r).map (X := (X, a.tensorObj Y Z))
        (Y := (X, r.tensorObj Y Z)) (𝟙 X, e.hom.app (Y, Z)) =
    e.hom.app (X, L) ≫ (@tensor D _ r).map (X := (X, L))
        (Y := (X, r.tensorObj Y Z)) (𝟙 X, g ≫ e.hom.app (Y, Z)) := by
  rw [e.hom.naturality_assoc]
  rw [← Functor.map_comp, prod_comp, Category.id_comp]

private theorem associator_of_models {a r : MonoidalCategory D}
    (e : @tensor D _ a ≅ @tensor D _ r) (X Y Z L N M M' : D)
    (f : L ≅ a.tensorObj X Y) (g : N ≅ a.tensorObj Y Z)
    (l : M ≅ a.tensorObj L Z) (q : M' ≅ a.tensorObj X N) (h : M ⟶ M')
    (ha : l.hom ≫ (@tensor D _ a).map (X := (L, Z))
      (Y := (a.tensorObj X Y, Z)) (f.hom, 𝟙 Z) ≫ (a.associator X Y Z).hom =
      h ≫ q.hom ≫ (@tensor D _ a).map (X := (X, N))
      (Y := (X, a.tensorObj Y Z)) (𝟙 X, g.hom))
    (f' : L ≅ r.tensorObj X Y) (g' : N ≅ r.tensorObj Y Z)
    (l' : M ≅ r.tensorObj L Z) (q' : M' ≅ r.tensorObj X N)
    (hf : f.hom ≫ e.hom.app (X, Y) = f'.hom)
    (hg : g.hom ≫ e.hom.app (Y, Z) = g'.hom)
    (hl : l.hom ≫ e.hom.app (L, Z) = l'.hom)
    (hq : q.hom ≫ e.hom.app (X, N) = q'.hom)
    (hr : l'.hom ≫ (@tensor D _ r).map (X := (L, Z))
        (Y := (r.tensorObj X Y, Z)) (f'.hom, 𝟙 Z) ≫
          (r.associator X Y Z).hom =
      h ≫ q'.hom ≫ (@tensor D _ r).map (X := (X, N))
        (Y := (X, r.tensorObj Y Z)) (𝟙 X, g'.hom)) :
    (associatorLeft (a := a) (r := r) e).app (X, Y, Z) =
      (associatorRight (a := a) (r := r) e).app (X, Y, Z) := by
  apply (cancel_epi (l.hom ≫ (@tensor D _ a).map (X := (L, Z))
      (Y := (a.tensorObj X Y, Z)) (f.hom, 𝟙 Z))).1
  change (l.hom ≫ (@tensor D _ a).map (X := (L, Z))
      (Y := (a.tensorObj X Y, Z)) (f.hom, 𝟙 Z)) ≫
    (e.hom.app (a.tensorObj X Y, Z) ≫ (@tensor D _ r).map (X := (a.tensorObj X Y, Z))
        (Y := (r.tensorObj X Y, Z)) (e.hom.app (X, Y), 𝟙 Z) ≫
      (r.associator X Y Z).hom) =
    (l.hom ≫ (@tensor D _ a).map (X := (L, Z))
      (Y := (a.tensorObj X Y, Z)) (f.hom, 𝟙 Z)) ≫
      ((a.associator X Y Z).hom ≫ e.hom.app (X, a.tensorObj Y Z) ≫
        (@tensor D _ r).map (X := (X, a.tensorObj Y Z))
        (Y := (X, r.tensorObj Y Z)) (𝟙 X, e.hom.app (Y, Z)))
  calc
    _ = (l.hom ≫ e.hom.app (L, Z)) ≫
        (@tensor D _ r).map (X := (L, Z))
        (Y := (r.tensorObj X Y, Z)) (f.hom ≫ e.hom.app (X, Y), 𝟙 Z) ≫
          (r.associator X Y Z).hom := by
      simpa only [Category.assoc] using
        congrArg (fun t ↦ l.hom ≫ t ≫ (r.associator X Y Z).hom)
          (map_comparison_left (a := a) (r := r) e f.hom)
    _ = h ≫ (q.hom ≫ e.hom.app (X, N)) ≫
        (@tensor D _ r).map (X := (X, N))
        (Y := (X, r.tensorObj Y Z)) (𝟙 X, g.hom ≫ e.hom.app (Y, Z)) := by
      rw [hf, hg, hl, hq]
      exact hr
    _ = h ≫ q.hom ≫ (@tensor D _ a).map (X := (X, N))
      (Y := (X, a.tensorObj Y Z)) (𝟙 X, g.hom) ≫
        e.hom.app (X, a.tensorObj Y Z) ≫
          (@tensor D _ r).map (X := (X, a.tensorObj Y Z))
        (Y := (X, r.tensorObj Y Z)) (𝟙 X, e.hom.app (Y, Z)) := by
      simpa only [Category.assoc] using
        congrArg (fun t ↦ h ≫ q.hom ≫ t) (map_comparison_right (a := a) (r := r) e g.hom).symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun t ↦ t ≫ e.hom.app (X, a.tensorObj Y Z) ≫
          (@tensor D _ r).map (X := (X, a.tensorObj Y Z))
            (Y := (X, r.tensorObj Y Z)) (𝟙 X, e.hom.app (Y, Z))) ha.symm

private theorem unitLeft_of_models {a r : MonoidalCategory D}
    (e : @tensor D _ a ≅ @tensor D _ r) {I X M : D}
    (ua : a.tensorUnit ≅ I) (ur : r.tensorUnit ≅ I)
    (f : M ≅ a.tensorObj I X) (g : M ≅ r.tensorObj I X) (h : M ⟶ X)
    (hf : f.hom ≫ e.hom.app (I, X) = g.hom)
    (ha : f.hom ≫ (@tensor D _ a).map (X := (I, X))
      (Y := (a.tensorUnit, X)) (ua.inv, 𝟙 X) ≫ (a.leftUnitor X).hom = h)
    (hr : g.hom ≫ (@tensor D _ r).map (X := (I, X))
      (Y := (r.tensorUnit, X)) (ur.inv, 𝟙 X) ≫ (r.leftUnitor X).hom = h) :
    (Functor.whiskerLeft (unitLeftInput I) e.hom ≫ unitLeftPath r ur).app X =
      (unitLeftPath a ua).app X := by
  apply (cancel_epi f.hom).1
  change f.hom ≫ (e.hom.app (I, X) ≫ (@tensor D _ r).map (X := (I, X))
      (Y := (r.tensorUnit, X)) (ur.inv, 𝟙 X) ≫ (r.leftUnitor X).hom) = _
  rw [← Category.assoc, hf]
  exact hr.trans ha.symm

private theorem unitRight_of_models {a r : MonoidalCategory D}
    (e : @tensor D _ a ≅ @tensor D _ r) {I X M : D}
    (ua : a.tensorUnit ≅ I) (ur : r.tensorUnit ≅ I)
    (f : M ≅ a.tensorObj X I) (g : M ≅ r.tensorObj X I) (h : M ⟶ X)
    (hf : f.hom ≫ e.hom.app (X, I) = g.hom)
    (ha : f.hom ≫ (@tensor D _ a).map (X := (X, I))
      (Y := (X, a.tensorUnit)) (𝟙 X, ua.inv) ≫ (a.rightUnitor X).hom = h)
    (hr : g.hom ≫ (@tensor D _ r).map (X := (X, I))
      (Y := (X, r.tensorUnit)) (𝟙 X, ur.inv) ≫ (r.rightUnitor X).hom = h) :
    (Functor.whiskerLeft (unitRightInput I) e.hom ≫ unitRightPath r ur).app X =
      (unitRightPath a ua).app X := by
  apply (cancel_epi f.hom).1
  change f.hom ≫ (e.hom.app (X, I) ≫ (@tensor D _ r).map (X := (X, I))
      (Y := (X, r.tensorUnit)) (𝟙 X, ur.inv) ≫ (r.rightUnitor X).hom) = _
  rw [← Category.assoc, hf]
  exact hr.trans ha.symm

private theorem map_eq {B : Type*} [Category B] (F : B ⥤ D)
    {X Y : B} {f g : X ⟶ Y} (h : f = g) : F.map f = F.map g := congrArg F.map h

private theorem map_eq_comp {B : Type*} [Category B] (F : B ⥤ D)
    {X Y : B} {f g : X ⟶ Y} {Z : D} (k : F.obj Y ⟶ Z)
    (h : f = g) : F.map f ≫ k = F.map g ≫ k := congrArg (fun t ↦ F.map t ≫ k) h

end ConstraintPaths

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

/-- The existing abstract native tensor, with its monoidal instance explicitly named.
Source: Stacks 06YU, 0FPT (blueprint: lem-pd-ringed-kflat-native-model-identification). -/
def nativeTensor :=
  @tensor (DerivedCategory (RingedTensorModules.{c, v, u} J R)) _
    (RingedDerivedNative.monoidal.{c, v, u, w} J R)

/-- The actual native derived-to-ordinary transformation, the localization tensorator.
Source: Stacks 06YU (blueprint: lem-pd-ringed-kflat-native-model-identification). -/
def nativeLocalization
    (P Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    (nativeTensor.{c, v, u, w} J R).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ⟶
      DerivedCategory.Q.{w}.obj ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) :=
  letI := RingedDerivedNative.monoidal.{c, v, u, w} J R
  letI := RingedDerivedNative.lax.{c, v, u, w} J R
  Functor.LaxMonoidal.μ DerivedCategory.Q P Q

variable
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
  (T : CoefficientTensorModels.{u, c, v, w} J R S)

/-- The resolving-pair normalization determining a tensor comparison uniquely.
Source: Stacks 06YS, 06YU (blueprint: lem-pd-ringed-kflat-native-model-identification). -/
def Normalized (e : nativeTensor.{c, v, u, w} J R ≅ S.tensor) : Prop :=
  ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients),
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X n)) →
    (RingedDerivedNative.tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).hom ≫
      e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        (T.iso J R S P Q hP hQ).hom

/-- The type of all-complex localization transformations for the given ringed tensor.
Source: Stacks 06YU (blueprint: lem-pd-ringed-kflat-native-model-identification). -/
abbrev Localization :=
  (DerivedCategory.Q.prod DerivedCategory.Q) ⋙ S.tensor ⟶
    coefficientTotalTensor.{u, c, v} J R ⋙ DerivedCategory.Q.{w}

/-- The three monoidal comparison diagrams with a shared, identified unit.
This uses arbitrary monoidal structures only to keep the identical site diagrams small.
Source: Stacks 0FPT (blueprint: lem-pd-ringed-kflat-native-model-identification). -/
def Constraints {D : Type d} [Category.{h} D]
    (a r : MonoidalCategory D) (I : D)
    (ua : a.tensorUnit ≅ I) (ur : r.tensorUnit ≅ I)
    (e : @tensor D _ a ≅ @tensor D _ r) : Prop :=
  (∀ X Y Z : D,
    e.hom.app (a.tensorObj X Y, Z) ≫
      (@tensor D _ r).map
        (X := (a.tensorObj X Y, Z)) (Y := (r.tensorObj X Y, Z))
        (e.hom.app (X, Y), 𝟙 Z) ≫ (r.associator X Y Z).hom =
    (a.associator X Y Z).hom ≫ e.hom.app (X, a.tensorObj Y Z) ≫
      (@tensor D _ r).map
        (X := (X, a.tensorObj Y Z)) (Y := (X, r.tensorObj Y Z))
        (𝟙 X, e.hom.app (Y, Z))) ∧
  (∀ X : D,
    e.hom.app (I, X) ≫
      (@tensor D _ r).map (X := (I, X)) (Y := (r.tensorUnit, X))
        (ur.inv, 𝟙 X) ≫ (r.leftUnitor X).hom =
    (@tensor D _ a).map (X := (I, X)) (Y := (a.tensorUnit, X))
      (ua.inv, 𝟙 X) ≫ (a.leftUnitor X).hom) ∧
  (∀ X : D,
    e.hom.app (X, I) ≫
      (@tensor D _ r).map (X := (X, I)) (Y := (X, r.tensorUnit))
        (𝟙 X, ur.inv) ≫ (r.rightUnitor X).hom =
    (@tensor D _ a).map (X := (X, I)) (Y := (X, a.tensorUnit))
      (𝟙 X, ua.inv) ≫ (a.rightUnitor X).hom)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private theorem gradedTensorCache :
    ∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y :=
  RingedDerivedNative.gradedTensor.{c, v, u} J R

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private theorem gradedTensorFourCache :
    ∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
      GradedObject.HasTensor₄ObjExt W X Y Z :=
  RingedDerivedNative.gradedTensorFour.{c, v, u} J R

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private theorem gradedTensorLeftCache :
    ∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
      GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
  RingedDerivedNative.gradedTensorLeft.{c, v, u} J R

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private theorem gradedTensorRightCache :
    ∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
      GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
  RingedDerivedNative.gradedTensorRight.{c, v, u} J R

attribute [local instance 10000] gradedTensorCache gradedTensorFourCache
  gradedTensorLeftCache gradedTensorRightCache

@[reducible]
private def complexMonoidal :
    MonoidalCategory (CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) := inferInstance

@[reducible]
private def derivedMonoidal :
    MonoidalCategory (DerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)) :=
  RingedDerivedNative.monoidal.{c, v, u, w} J R

attribute [local instance 10000] complexMonoidal derivedMonoidal

@[reducible]
private def complexMonoidalStruct :
    MonoidalCategoryStruct (CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :=
  (complexMonoidal.{c, v, u} J R).toMonoidalCategoryStruct

attribute [local instance 10000] complexMonoidalStruct

@[no_expose]
private def chainLeftUnitor
    (P : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    (coefficientTotalTensor.{u, c, v} J R).obj
      (ringedTensorUnitComplex.{c, v, u} J R, P) ≅ P :=
  HomologicalComplex.leftUnitor P

private theorem comparison_exists :
    ∃ e : nativeTensor.{c, v, u, w} J R ≅ S.tensor,
      ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
        (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients),
        (RingedDerivedNative.tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).hom ≫
          e.hom.app (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q) =
            (T.iso J R S P Q hP hQ).hom := by
  let i := coefficientKFlatInclusion.{u, c, v} J R
  let L := i ⋙ DerivedCategory.Q.{w}
  let W := (HomologicalComplex.quasiIso (RingedTensorModules.{c, v, u} J R) (.up ℤ)).inverseImage i
  let := RingedDerivedNative.kFlatLocalization.{c, v, u, w} J R
  let e₀ := (RingedDerivedNative.comparison.{c, v, u, w} J R).symm ≪≫ T.comparison
  let ha : Localization.Lifting (L.prod L) (W.prod W)
      ((L.prod L) ⋙ nativeTensor.{c, v, u, w} J R) (nativeTensor.{c, v, u, w} J R) :=
    ⟨Iso.refl _⟩
  let hr : Localization.Lifting (L.prod L) (W.prod W)
      ((L.prod L) ⋙ S.tensor) S.tensor := ⟨Iso.refl _⟩
  let e := Localization.liftNatIso (L.prod L) (W.prod W)
    ((L.prod L) ⋙ nativeTensor.{c, v, u, w} J R) ((L.prod L) ⋙ S.tensor)
    (nativeTensor.{c, v, u, w} J R) S.tensor e₀
  refine ⟨e, ?_⟩
  intro P Q hP hQ
  change (RingedDerivedNative.tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).hom ≫
    e.hom.app ((L.prod L).obj (⟨P, hP⟩, ⟨Q, hQ⟩)) = _
  have heapp := Localization.liftNatTrans_app (L.prod L) (W.prod W)
    ((L.prod L) ⋙ nativeTensor.{c, v, u, w} J R) ((L.prod L) ⋙ S.tensor)
    (nativeTensor.{c, v, u, w} J R) S.tensor e₀.hom (⟨P, hP⟩, ⟨Q, hQ⟩)
  change (RingedDerivedNative.tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).hom ≫
    (Localization.liftNatTrans (L.prod L) (W.prod W)
      ((L.prod L) ⋙ nativeTensor.{c, v, u, w} J R) ((L.prod L) ⋙ S.tensor)
      (nativeTensor.{c, v, u, w} J R) S.tensor e₀.hom).app
        ((L.prod L).obj (⟨P, hP⟩, ⟨Q, hQ⟩)) = _
  rw [heapp]
  dsimp only [Localization.Lifting.iso, ha, hr, e₀, Iso.refl_hom, Iso.refl_inv,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [NatTrans.id_app, Category.id_comp, Category.comp_id]
  change (RingedDerivedNative.tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).hom ≫
    (RingedDerivedNative.tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).inv ≫
      (T.iso J R S P Q hP hQ).hom = _
  simp only [Iso.hom_inv_id_assoc]

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private theorem resolving_exists
    (U : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    ∃ (P : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) (p : P ⟶ U),
      P.IsKFlatIndependentCoefficients ∧
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)) ∧ QuasiIso p := by
  obtain ⟨P, p, hP, hf, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients U
  refine ⟨P, p, hP, ?_, hp⟩
  intro n
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (P.X n)).symm (hf n)

private theorem resolving_ext
    {F G : DerivedCategory.{w} (RingedTensorModules.{c, v, u} J R) ×
        DerivedCategory.{w} (RingedTensorModules.{c, v, u} J R) ⥤
        DerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)}
    (a b : F ⟶ G)
    (hab : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
      (_hP : P.IsKFlatIndependentCoefficients) (_hQ : Q.IsKFlatIndependentCoefficients),
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)) →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X n)) →
      a.app (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q) =
        b.app (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q)) : a = b := by
  apply Localization.natTrans_ext
    ((DerivedCategory.Q.{w} (C := RingedTensorModules.{c, v, u} J R)).prod
      (DerivedCategory.Q.{w} (C := RingedTensorModules.{c, v, u} J R)))
    ((HomologicalComplex.quasiIso (RingedTensorModules.{c, v, u} J R) (.up ℤ)).prod
      (HomologicalComplex.quasiIso (RingedTensorModules.{c, v, u} J R) (.up ℤ)))
  rintro ⟨U, V⟩
  obtain ⟨P, p, hP, hfP, hp⟩ := resolving_exists.{c, v, u} J R U
  obtain ⟨Q, q, hQ, hfQ, hq⟩ := resolving_exists.{c, v, u} J R V
  have : IsIso (DerivedCategory.Q.{w}.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  have : IsIso (DerivedCategory.Q.{w}.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
  apply (cancel_epi (F.map (X := (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q))
    (Y := (DerivedCategory.Q.{w}.obj U, DerivedCategory.Q.{w}.obj V))
    (DerivedCategory.Q.{w}.map p, DerivedCategory.Q.{w}.map q))).1
  change F.map (X := (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q))
      (Y := (DerivedCategory.Q.{w}.obj U, DerivedCategory.Q.{w}.obj V))
      (DerivedCategory.Q.{w}.map p, DerivedCategory.Q.{w}.map q) ≫
        a.app (DerivedCategory.Q.{w}.obj U, DerivedCategory.Q.{w}.obj V) =
    F.map (X := (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q))
      (Y := (DerivedCategory.Q.{w}.obj U, DerivedCategory.Q.{w}.obj V))
      (DerivedCategory.Q.{w}.map p, DerivedCategory.Q.{w}.map q) ≫
        b.app (DerivedCategory.Q.{w}.obj U, DerivedCategory.Q.{w}.obj V)
  rw [a.naturality (X := (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q))
    (Y := (DerivedCategory.Q.{w}.obj U, DerivedCategory.Q.{w}.obj V))
    (DerivedCategory.Q.{w}.map p, DerivedCategory.Q.{w}.map q)]
  rw [b.naturality (X := (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q))
    (Y := (DerivedCategory.Q.{w}.obj U, DerivedCategory.Q.{w}.obj V))
    (DerivedCategory.Q.{w}.map p, DerivedCategory.Q.{w}.map q)]
  rw [hab P Q hP hQ hfP hfQ]

private theorem comparison_unique
    (e e' : nativeTensor.{c, v, u, w} J R ≅ S.tensor)
    (he : Normalized.{c, v, u, w} J R S T e)
    (he' : Normalized.{c, v, u, w} J R S T e') : e = e' := by
  apply Iso.ext
  apply resolving_ext.{c, v, u, w} J R
  intro P Q hP hQ hfP hfQ
  apply (cancel_epi
    (RingedDerivedNative.tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).hom).1
  rw [he P Q hP hQ hfP hfQ, he' P Q hP hQ hfP hfQ]

private theorem comparison_oneKFlat
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (e : nativeTensor.{c, v, u, w} J R ≅ S.tensor)
    (he : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
      (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients),
      (RingedDerivedNative.tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).hom ≫
        e.hom.app (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q) =
          (T.iso J R S P Q hP hQ).hom)
    (U V : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (h : U.IsKFlatIndependentCoefficients ∨ V.IsKFlatIndependentCoefficients) :
    (RingedDerivedNative.tensorIso.{c, v, u, w} J R U V h).hom ≫
      e.hom.app (DerivedCategory.Q.{w}.obj U, DerivedCategory.Q.{w}.obj V) =
        (hc.tensorIso U V h).hom := by
  obtain ⟨P, p, hP, _, hp⟩ := resolving_exists.{c, v, u} J R U
  obtain ⟨Q, q, hQ, _, hq⟩ := resolving_exists.{c, v, u} J R V
  have : IsIso (DerivedCategory.Q.{w}.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  have : IsIso (DerivedCategory.Q.{w}.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
  let a := DerivedCategory.Q.{w}.map ((coefficientTotalTensor.{u, c, v} J R).map
    (X := (P, Q)) (Y := (U, V)) (p, q))
  have hn : a ≫ (RingedDerivedNative.tensorIso.{c, v, u, w} J R U V h).hom =
      (RingedDerivedNative.tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).hom ≫
        (nativeTensor.{c, v, u, w} J R).map
          (X := (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q))
          (Y := (DerivedCategory.Q.{w}.obj U, DerivedCategory.Q.{w}.obj V))
          (DerivedCategory.Q.{w}.map p, DerivedCategory.Q.{w}.map q) :=
    RingedDerivedNative.tensorIso_naturality.{c, v, u, w}
      J R P Q U V (Or.inl hP) h p q
  have hr := hc.tensorIso_naturality P Q U V (Or.inl hP) h p q
  have hi : IsIso (a ≫ (RingedDerivedNative.tensorIso.{c, v, u, w} J R U V h).hom) := by
    rw [hn]
    infer_instance
  have : IsIso a := IsIso.of_isIso_comp_right a
    (RingedDerivedNative.tensorIso.{c, v, u, w} J R U V h).hom
  apply (cancel_epi a).1
  have hen := e.hom.naturality
    (X := (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q))
    (Y := (DerivedCategory.Q.{w}.obj U, DerivedCategory.Q.{w}.obj V))
    (DerivedCategory.Q.{w}.map p, DerivedCategory.Q.{w}.map q)
  calc
    _ = (a ≫ (RingedDerivedNative.tensorIso.{c, v, u, w} J R U V h).hom) ≫
        e.hom.app (DerivedCategory.Q.{w}.obj U, DerivedCategory.Q.{w}.obj V) :=
      (Category.assoc _ _ _).symm
    _ = _ := by
      rw [hn, Category.assoc, hen]
      rw [← Category.assoc, he P Q hP hQ, ← hc.tensorIso_both P Q hP hQ]
      exact hr.symm

private theorem associator_model_native
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (P Q N : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (hN : N.IsKFlatIndependentCoefficients) :
    (hc.tensorIso ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) N (Or.inr hN)).hom ≫
      S.tensor.map
        (X := (DerivedCategory.Q.{w}.obj ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)),
          DerivedCategory.Q.{w}.obj N))
        (Y := (S.tensor.obj (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q),
          DerivedCategory.Q.{w}.obj N))
        ((T.iso J R S P Q hP hQ).hom, 𝟙 _) ≫
        (S.monoidal.associator (DerivedCategory.Q.{w}.obj P) (DerivedCategory.Q.{w}.obj Q)
          (DerivedCategory.Q.{w}.obj N)).hom =
      DerivedCategory.Q.{w}.map (CategoryTheory.ordinaryAssociator.{c, v, u} J R P Q N).hom ≫
        (hc.tensorIso P ((coefficientTotalTensor.{u, c, v} J R).obj (Q, N)) (Or.inl hP)).hom ≫
          S.tensor.map
            (X := (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj
              ((coefficientTotalTensor.{u, c, v} J R).obj (Q, N))))
            (Y := (DerivedCategory.Q.{w}.obj P,
              S.tensor.obj (DerivedCategory.Q.{w}.obj Q, DerivedCategory.Q.{w}.obj N)))
            (𝟙 _, (T.iso J R S Q N hQ hN).hom) := by
  obtain ⟨a, ha, he⟩ := hc.associator_model P Q N hP hQ hN
  have heq : a.hom = (CategoryTheory.ordinaryAssociator.{c, v, u} J R P Q N).hom :=
    CategoryTheory.ordinaryAssociator_unique.{c, v, u} J R P Q N a.hom ha
  exact he.trans (map_eq_comp DerivedCategory.Q.{w} _ heq)

private theorem leftUnitor_model_native
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (P : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) :
    (hc.tensorIso (ringedTensorUnitComplex.{c, v, u} J R) P (Or.inr hP)).hom ≫
      S.tensor.map
        (X := (DerivedCategory.Q.{w}.obj (ringedTensorUnitComplex.{c, v, u} J R),
          DerivedCategory.Q.{w}.obj P))
        (Y := (S.monoidal.tensorUnit, DerivedCategory.Q.{w}.obj P))
        (hc.unitIso.inv, 𝟙 _) ≫
        (S.monoidal.leftUnitor (DerivedCategory.Q.{w}.obj P)).hom =
      DerivedCategory.Q.{w}.map (chainLeftUnitor.{c, v, u} J R P).hom := by
  obtain ⟨l, hl, he⟩ := hc.leftUnitor_model P hP
  have heq : l.hom = (chainLeftUnitor.{c, v, u} J R P).hom := by
    apply HomologicalComplex.hom_ext
    intro k
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := ringedTensorUnitComplex.{c, v, u} J R) (K₂ := P)
      (F := curriedTensor (RingedTensorModules.{c, v, u} J R)) (c := .up ℤ)
    intro p q hpq
    change p + q = k at hpq
    by_cases hp : p = 0
    · subst p
      have hk : k = q := by omega
      subst q
      apply CategoryTheory.pure_ext.{c, v, u} J R
        ((ringedTensorUnitComplex.{c, v, u} J R).X 0) (P.X k) (P.X k)
      intro U a x
      exact (hl k (zero_add k) U a x).trans
        ((RingedDerivedNative.complexConstraints.{c, v, u} J R).leftUnitor
          P k (zero_add k) U a x).symm
    · apply IsZero.eq_of_src
      exact (tensorRight (P.X q)).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ p hp)
  exact he.trans (map_eq DerivedCategory.Q.{w} heq)

private theorem rightUnitor_model_native
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (P : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) :
    (hc.tensorIso P (ringedTensorUnitComplex.{c, v, u} J R) (Or.inl hP)).hom ≫
      S.tensor.map
        (X := (DerivedCategory.Q.{w}.obj P,
          DerivedCategory.Q.{w}.obj (ringedTensorUnitComplex.{c, v, u} J R)))
        (Y := (DerivedCategory.Q.{w}.obj P, S.monoidal.tensorUnit))
        (𝟙 _, hc.unitIso.inv) ≫
        (S.monoidal.rightUnitor (DerivedCategory.Q.{w}.obj P)).hom =
      DerivedCategory.Q.{w}.map (CategoryTheory.ordinaryRightUnitor.{c, v, u} J R P).hom := by
  obtain ⟨r, hr, he⟩ := hc.rightUnitor_model P hP
  have heq : r.hom = (CategoryTheory.ordinaryRightUnitor.{c, v, u} J R P).hom :=
    CategoryTheory.ordinaryRightUnitor_unique.{c, v, u} J R P r.hom hr
  exact he.trans (map_eq DerivedCategory.Q.{w} heq)

private theorem comparison_constraints
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (e : nativeTensor.{c, v, u, w} J R ≅ S.tensor)
    (he : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
      (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients),
      (RingedDerivedNative.tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).hom ≫
        e.hom.app (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q) =
          (T.iso J R S P Q hP hQ).hom) :
    Constraints (RingedDerivedNative.monoidal.{c, v, u, w} J R) S.monoidal
      (DerivedCategory.Q.{w}.obj (ringedTensorUnitComplex.{c, v, u} J R))
      (RingedDerivedNative.unitIso.{c, v, u, w} J R) hc.unitIso e := by
  let a := RingedDerivedNative.monoidal.{c, v, u, w} J R
  let i := coefficientKFlatInclusion.{u, c, v} J R
  let L := i ⋙ DerivedCategory.Q.{w}
  let W := (HomologicalComplex.quasiIso (RingedTensorModules.{c, v, u} J R) (.up ℤ)).inverseImage i
  let := RingedDerivedNative.kFlatLocalization.{c, v, u, w} J R
  have hone := comparison_oneKFlat.{c, v, u, w} J R S T β hc e he
  have hassoc : associatorLeft (a := a) (r := S.monoidal) e =
      associatorRight (a := a) (r := S.monoidal) e := by
    apply Localization.natTrans_ext (L.prod (L.prod L)) (W.prod (W.prod W))
    rintro ⟨P, Q, N⟩
    let PQ := (coefficientTotalTensor.{u, c, v} J R).obj (P.obj, Q.obj)
    let QN := (coefficientTotalTensor.{u, c, v} J R).obj (Q.obj, N.obj)
    refine associator_of_models (a := a) (r := S.monoidal) e (L.obj P) (L.obj Q) (L.obj N)
      (DerivedCategory.Q.{w}.obj PQ) (DerivedCategory.Q.{w}.obj QN)
      (DerivedCategory.Q.{w}.obj ((coefficientTotalTensor.{u, c, v} J R).obj (PQ, N.obj)))
      (DerivedCategory.Q.{w}.obj ((coefficientTotalTensor.{u, c, v} J R).obj (P.obj, QN)))
      (RingedDerivedNative.tensorIso.{c, v, u, w} J R P.obj Q.obj (Or.inl P.property))
      (RingedDerivedNative.tensorIso.{c, v, u, w} J R Q.obj N.obj (Or.inl Q.property))
      (RingedDerivedNative.tensorIso.{c, v, u, w} J R PQ N.obj (Or.inr N.property))
      (RingedDerivedNative.tensorIso.{c, v, u, w} J R P.obj QN (Or.inl P.property))
      (DerivedCategory.Q.{w}.map
        (CategoryTheory.ordinaryAssociator.{c, v, u} J R P.obj Q.obj N.obj).hom) ?_
      (T.iso J R S P.obj Q.obj P.property Q.property)
      (T.iso J R S Q.obj N.obj Q.property N.property)
      (hc.tensorIso PQ N.obj (Or.inr N.property))
      (hc.tensorIso P.obj QN (Or.inl P.property))
      (he P.obj Q.obj P.property Q.property)
      (he Q.obj N.obj Q.property N.property)
      (hone PQ N.obj (Or.inr N.property))
      (hone P.obj QN (Or.inl P.property)) ?_
    · exact RingedDerivedNative.associator_square.{c, v, u, w} J R
        P.obj Q.obj N.obj P.property Q.property N.property
    · exact associator_model_native.{c, v, u, w} J R S T β hc
        P.obj Q.obj N.obj P.property Q.property N.property
  let I := DerivedCategory.Q.{w}.obj (ringedTensorUnitComplex.{c, v, u} J R)
  have hleft : Functor.whiskerLeft (unitLeftInput I) e.hom ≫
      unitLeftPath S.monoidal hc.unitIso =
        unitLeftPath a (RingedDerivedNative.unitIso.{c, v, u, w} J R) := by
    apply Localization.natTrans_ext L W
    intro P
    exact unitLeft_of_models (a := a) (r := S.monoidal) e
      (RingedDerivedNative.unitIso.{c, v, u, w} J R) hc.unitIso
      (RingedDerivedNative.tensorIso.{c, v, u, w} J R
        (ringedTensorUnitComplex.{c, v, u} J R) P.obj (Or.inr P.property))
      (hc.tensorIso (ringedTensorUnitComplex.{c, v, u} J R) P.obj (Or.inr P.property))
      (DerivedCategory.Q.{w}.map (chainLeftUnitor.{c, v, u} J R P.obj).hom)
      (hone _ _ (Or.inr P.property))
      (RingedDerivedNative.leftUnitor_square.{c, v, u, w} J R P.obj P.property)
      (leftUnitor_model_native.{c, v, u, w} J R S T β hc P.obj P.property)
  have hright : Functor.whiskerLeft (unitRightInput I) e.hom ≫
      unitRightPath S.monoidal hc.unitIso =
        unitRightPath a (RingedDerivedNative.unitIso.{c, v, u, w} J R) := by
    apply Localization.natTrans_ext L W
    intro P
    exact unitRight_of_models (a := a) (r := S.monoidal) e
      (RingedDerivedNative.unitIso.{c, v, u, w} J R) hc.unitIso
      (RingedDerivedNative.tensorIso.{c, v, u, w} J R
        P.obj (ringedTensorUnitComplex.{c, v, u} J R) (Or.inl P.property))
      (hc.tensorIso P.obj (ringedTensorUnitComplex.{c, v, u} J R) (Or.inl P.property))
      (DerivedCategory.Q.{w}.map (CategoryTheory.ordinaryRightUnitor.{c, v, u} J R P.obj).hom)
      (hone _ _ (Or.inl P.property))
      (RingedDerivedNative.rightUnitor_square.{c, v, u, w} J R P.obj P.property)
      (rightUnitor_model_native.{c, v, u, w} J R S T β hc P.obj P.property)
  exact ⟨fun X Y Z ↦ congr_app hassoc (X, Y, Z),
    fun X ↦ congr_app hleft X, fun X ↦ congr_app hright X⟩

-- Preserve the recorded signature, whose second K-flat proof fixes the allowed model pairs.
end CategoryTheory.RingedKFlatModel
