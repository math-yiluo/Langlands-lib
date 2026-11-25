/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExternalRHom.ExternalRHomConePairingDefs
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantModuleFlat
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantModuleTensor
import WeilConjectures.Algebra.Homology.FlatTermKFlatFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # Flatness and K-flatness in constant-scalar coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ZeroObject
namespace AlgebraicGeometry.Etale.ExternalRHom
variable (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})

private theorem ringIso_eq :
    (realizationRingIso X.smallEtaleTopology A).hom =
      (constantModuleHomRingIso X.smallEtaleTopology A).inv := by
  simp only [realizationRingIso, constantModuleHomRingIso, constantCommuteCompose,
    Iso.app_hom, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.compConstIso]
  change _ ≫ (presheafToSheaf X.smallEtaleTopology RingCat.{u + 1}).map
    (𝟙 ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of A))) = _
  erw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

private theorem realization_eq :
    ringedRealization A X = Scheme.etaleSumTensorTestRealization X A := by
  unfold ringedRealization Scheme.etaleSumTensorTestRealization
  rw [ringIso_eq A X]
  rfl

private instance realizationColimits : PreservesColimitsOfShape ℤ (ringedRealization A X) := by
  rw [realization_eq A X]
  let := Scheme.etaleSumTensorTestRealization_isEquivalence X A
  infer_instance

/-- Flatness is invariant under the canonical scalar realization.
Source: Stacks Project, Tags 03CV, 03ER and 093J
(blueprint: lem-pur-etale-constant-module-flat).

Proof: the ring comparison in ExternalRHom is the inverse of the comparison
used by the constant-module tensor equivalence. Both are the sheafification
comparison for forgetting commutativity, followed by the identity constant
presheaf comparison. Thus the realizations agree. Apply the flatness equivalence
of the constant-module tensor realization. This includes the empty scheme and
zero coefficient ring. -/
private theorem ringedRealization_flat_iff (M : Modules A X) :
    SheafOfModules.IsFlatOnSite
      (J := X.smallEtaleTopology) (R := realizationRing X.smallEtaleTopology A)
      ((ringedRealization A X).obj M) ↔ ObjectProperty.flat M := by
  rw [realization_eq A X]
  exact (Scheme.etaleConstantModule_flat_iff X A M).symm

section Complexes

private local instance ringedMonoidal :
    MonoidalCategory (realizationModules X.smallEtaleTopology A) :=
  SheafOfModules.monoidalCategory (realizationRing X.smallEtaleTopology A)
private local instance ringedSymmetric :
    SymmetricCategory (realizationModules X.smallEtaleTopology A) :=
  SheafOfModules.symmetricCategory (realizationRing X.smallEtaleTopology A)
private local instance ringedPreadditive :
    MonoidalPreadditive (realizationModules X.smallEtaleTopology A) :=
  SheafOfModules.tensorPreadditive (realizationRing X.smallEtaleTopology A)
private local instance ringedClosed : MonoidalClosed (realizationModules X.smallEtaleTopology A) :=
  SheafOfModules.monoidalClosed_kfi
    (J := X.smallEtaleTopology) (R := realizationRing X.smallEtaleTopology A)
private local instance ringedGrothendieck :
    IsGrothendieckAbelian.{u + 1} (realizationModules X.smallEtaleTopology A) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
    X.smallEtaleTopology (realizationRing X.smallEtaleTopology A)).1
private local instance ringedFlatResolution :
    Abelian.HasFunctorialFlatResolution (realizationModules X.smallEtaleTopology A) :=
  SheafOfModules.hasFunctorialFlatResolution_kfi (realizationRing X.smallEtaleTopology A)

private theorem categorical_flat_iff (M : realizationModules X.smallEtaleTopology A) :
    ObjectProperty.flat M ↔ SheafOfModules.IsFlatOnSite
      (J := X.smallEtaleTopology) (R := realizationRing X.smallEtaleTopology A) M := by
  constructor
  · intro h
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (realizationRing X.smallEtaleTopology A) M).symm h.2
  · exact SheafOfModules.flat_to_cat (realizationRing X.smallEtaleTopology A) M

private instance realizationPreservesFlat : (ringedRealization A X).PreservesFlat where
  flat_obj {M} h := (categorical_flat_iff A X _).2
    ((ringedRealization_flat_iff A X M).2 h)

private theorem independent_of_categorical
    (P : CochainComplex (realizationModules X.smallEtaleTopology A) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    P.IsKFlatIndependentCoefficients := by
  intro Z hZ
  let T := tensorRight P
  let O : CochainComplex (realizationModules X.smallEtaleTopology A) ℤ := 0
  have hz : QuasiIso (0 : O ⟶ Z) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt _ i
      ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
  have hmap : QuasiIso (T.map (0 : O ⟶ Z)) := hP.2 _ hz
  have htzero : (T.obj O).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
  exact fun i ↦ (exactAt_iff_of_quasiIsoAt (T.map (0 : O ⟶ Z)) i).1 (htzero i)

/-- Flat-term native K-flat complexes remain K-flat in constant-scalar coordinates.
Source: Stacks Project, Tags 06YS, 0G7D and 0G7E
(blueprint: lem-pur-etale-scalar-flat-kflat-comparison).

Proof: scalar realization takes flat objects to flat module sheaves by the flat
comparison. As an additive functor preserving integer-indexed colimits and flat
objects, it takes flat-term K-flat complexes to categorical K-flat complexes.
Apply its right-tensor quasi-isomorphism test to the map from zero to any acyclic
complex. The tensor with zero is zero, hence the tensor with the test complex is
acyclic. This is precisely the independent-coefficients K-flat predicate. -/
theorem ringedComplex_flat_kFlat (P : Complexes A X)
    (hP : (HomologicalComplex.quasiIso (Modules A X) (.up ℤ)).kFlat P)
    (hf : ∀ n, ObjectProperty.flat (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients ((ringedComplex A X).obj P) ∧
      ∀ n, SheafOfModules.IsFlatOnSite
        (J := X.smallEtaleTopology) (R := realizationRing X.smallEtaleTopology A)
        ((ringedRealization A X).obj (P.X n)) := by
  exact ⟨independent_of_categorical A X _
    ((ringedRealization A X).kFlat_map_of_flat_terms P hP hf),
    fun n ↦ (ringedRealization_flat_iff A X _).2 (hf n)⟩

end Complexes

end AlgebraicGeometry.Etale.ExternalRHom
