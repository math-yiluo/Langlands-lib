/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicIntrinsicCompletion
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlat
import WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
/-! # K-flatness of the completed exterior Koszul complexes

Source: Stacks Project, Tags 06YQ and 0G7E.
(blueprint: lem-weil-pbc-completed-adic-koszul-kflat).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false in
private lemma koszulConstantOne_isIso (X : Scheme.{t}) (Λ : Type t) [CommRing Λ] :
    IsIso (koszulConstantOne X Λ) := by
  let := (koszulConstantUnit_local X Λ).1
  let := (koszulConstantUnit_local X Λ).2
  let R := adicModuleRing X Λ
  let α := koszulConstantUnit X Λ
  let P := (siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} Λ)).obj
    (ModuleCat.of (ULift.{t + 1} Λ) (ULift.{t + 1} Λ))
  let U : SheafOfModules.{t + 1} R := SheafOfModules.unit R
  let V := (PresheafOfModules.restrictScalars α).obj U.val
  let s : V.sections := V.sectionsMk (fun A ↦ (1 : R.obj.obj A)) (by
    intro A B h
    change R.obj.map h 1 = 1
    exact map_one _)
  let a : P ⟶ V := V.unitHomEquiv.symm s
  let b : (koszulConstantFunctor X Λ).obj
      (ModuleCat.of (ULift.{t + 1} Λ) (ULift.{t + 1} Λ)) ⟶ U :=
    (PresheafOfModules.sheafificationHomEquiv.{t + 1} α).symm a
  have hb (A : X.ProEtᵒᵖ) :
      b.val.app A ((toSheafify (ProEt.topology X) P.presheaf).app A
        (1 : ULift.{t + 1} Λ)) = (1 : R.obj.obj A) := by
    have h :=
      (PresheafOfModules.sheafificationHomEquiv.{t + 1} α (P := P) (F := U)).apply_symm_apply a
    have h' := congrArg (fun z ↦ (z.app A) (1 : ULift.{t + 1} Λ)) h
    change b.val.app A ((toSheafify (ProEt.topology X) P.presheaf).app A
      (1 : ULift.{t + 1} Λ)) = a.app A (1 : ULift.{t + 1} Λ) at h'
    have ha := congrArg (fun z ↦ z.val A) (V.unitHomEquiv.apply_symm_apply s)
    change a.app A (1 : ULift.{t + 1} Λ) = (1 : R.obj.obj A) at ha
    exact h'.trans ha
  have hu (A : X.ProEtᵒᵖ) :
      (koszulConstantOne X Λ).val.app A (1 : R.obj.obj A) =
        (toSheafify (ProEt.topology X) P.presheaf).app A
          (1 : ULift.{t + 1} Λ) :=
    (koszulConstantOne_exists X Λ).exists.choose_spec A
  have hub : koszulConstantOne X Λ ≫ b = 𝟙 U := by
    apply U.unitHomEquiv.injective
    apply Subtype.ext
    funext A
    change b.val.app A ((koszulConstantOne X Λ).val.app A
      (1 : R.obj.obj A)) = (1 : R.obj.obj A)
    rw [hu, hb]
  have hbu : b ≫ koszulConstantOne X Λ = 𝟙 _ := by
    apply (PresheafOfModules.sheafificationHomEquiv.{t + 1} α).injective
    apply PresheafOfModules.hom_ext
    intro A
    apply ModuleCat.hom_ext
    apply (LinearMap.ringLmapEquivSelf (ULift.{t + 1} Λ) ℤ _).injective
    change (koszulConstantOne X Λ).val.app A
      (b.val.app A ((toSheafify (ProEt.topology X) P.presheaf).app A (1 : ULift.{t + 1} Λ))) =
      (toSheafify (ProEt.topology X) P.presheaf).app A (1 : ULift.{t + 1} Λ)
    rw [hb, hu]
  exact ⟨b, hub, hbu⟩

private theorem constant_additive (X : Scheme.{t}) (A : Type t) [CommRing A] :
    (koszulConstantFunctor X A).Additive := by
  constructor
  intro M N f g
  apply (SheafOfModules.toSheaf.{t + 1} (adicModuleRing X A)).map_injective
  change (presheafToSheaf (ProEt.topology X) AddCommGrpCat.{t + 1}).map
    ((PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} A)).map
        (f + g))) = _
  have h : (PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} A)).map
        (f + g)) =
      (PresheafOfModules.toPresheaf _).map
        ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} A)).map f) +
      (PresheafOfModules.toPresheaf _).map
        ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} A)).map g) := rfl
  rw [h, Functor.map_add]
  rfl

private theorem tensorRight_coproduct_exact
    {B : Type*} [Category B] [Abelian B] [IsGrothendieckAbelian.{t + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B]
    {I : Type} (f : I → B) [Finite I]
    (hf : ∀ i, exactFunctor _ _ (tensorRight (f i))) :
    exactFunctor _ _ (tensorRight (∐ f)) := by
  let T := (curriedTensor B).flip
  have : T.Additive := by
    constructor
    intro X Y f g
    apply NatTrans.ext
    funext Z
    exact MonoidalPreadditive.whiskerLeft_add f g
  let G := (Discrete.functor f ⋙ T).flip
  have : PreservesFiniteLimits G := preservesFiniteLimits_of_evaluation _
    (fun i ↦ (hf i.as).1)
  have : PreservesFiniteColimits G := preservesFiniteColimits_of_evaluation _
    (fun i ↦ (hf i.as).2)
  let e : tensorRight (∐ f) ≅ G ⋙ colim :=
    preservesColimitIso T (Discrete.functor f) ≪≫
      colimitIsoFlipCompColim (Discrete.functor f ⋙ T)
  have : PreservesFiniteLimits (colim (J := Discrete I) (C := B)) := inferInstance
  have : PreservesFiniteLimits (G ⋙ colim) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (G ⋙ colim) := comp_preservesFiniteColimits _ _
  exact (exactFunctor _ _).prop_of_iso e.symm
    ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩)

set_option backward.isDefEq.respectTransparency false in
private theorem constant_exterior_free (X : Scheme.{t}) (A : Type t) [CommRing A]
    (r q : ℕ) :
    Nonempty ((koszulConstantFunctor X A).obj
      (ModuleCat.of (ULift.{t + 1} A) (⋀[ULift.{t + 1} A]^q (Fin r →₀ ULift.{t + 1} A))) ≅
        ∐ fun _ : Set.powersetCard (Fin r) q ↦ SheafOfModules.unit (adicModuleRing X A)) := by
  classical
  let := constant_additive X A
  let I := Set.powersetCard (Fin r) q
  let R := ULift.{t + 1} A
  let b := (Finsupp.basisSingleOne : Module.Basis (Fin r) R (Fin r →₀ R)).exteriorPower q
  let e : ModuleCat.of R (⋀[R]^q (Fin r →₀ R)) ≅
      ∐ fun _ : I ↦ ModuleCat.of R R :=
    (b.repr.trans (Finsupp.linearEquivFunOnFinite R R I)).toModuleIso ≪≫
      (ModuleCat.piIsoPi (fun _ : I ↦ ModuleCat.of R R)).symm ≪≫
        (biproduct.isoProduct _).symm ≪≫ biproduct.isoCoproduct _
  let := koszulConstantOne_isIso X A
  exact ⟨(koszulConstantFunctor X A).mapIso e ≪≫
    PreservesCoproduct.iso (koszulConstantFunctor X A) (fun _ : I ↦ ModuleCat.of R R) ≪≫
      Sigma.mapIso (fun _ : I ↦ (asIso (koszulConstantOne X A)).symm)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem constant_exterior_flat (X : Scheme.{t}) (A : Type t) [CommRing A]
    (r q : ℕ) :
    letI := SheafOfModules.monoidalCategory (adicConstantRing X A)
    exactFunctor _ _ (tensorRight ((koszulConstantFunctor X A).obj
      (ModuleCat.of (ULift.{t + 1} A) (⋀[ULift.{t + 1} A]^q (Fin r →₀ ULift.{t + 1} A))))) := by
  let R := adicConstantRing X A
  let B := SheafOfModules.{t + 1} (adicModuleRing X A)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive R
  let : IsGrothendieckAbelian.{t + 1} B :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{t + 1, t, t + 1, 0}
      (ProEt.topology X) (adicModuleRing X A)
  obtain ⟨e⟩ := constant_exterior_free X A r q
  have hunit : exactFunctor _ _ (tensorRight (SheafOfModules.unit (adicModuleRing X A))) :=
    (ObjectProperty.prop_unit ObjectProperty.flat).2
  exact (exactFunctor _ _).prop_of_iso ((curriedTensor B).flip.mapIso e.symm)
    (tensorRight_coproduct_exact
      (fun _ : Set.powersetCard (Fin r) q ↦ SheafOfModules.unit (adicModuleRing X A))
      (fun _ ↦ hunit))

set_option backward.isDefEq.respectTransparency false in
private theorem koszulPowerSheaf_flat_kflat (X : Scheme.{t}) (A : Type t) [CommRing A]
    (r : ℕ) (f : Fin r → A) (m : ℕ) :
    CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X A)
      (koszulPowerSheaf X A r f m) ∧
    letI := SheafOfModules.monoidalCategory (adicConstantRing X A)
    ∀ i : ℤ, exactFunctor _ _ (tensorRight ((koszulPowerSheaf X A r f m).X i)) := by
  let R := adicConstantRing X A
  let B := SheafOfModules.{t + 1} (adicModuleRing X A)
  let := constant_additive X A
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive R
  let F := koszulConstantFunctor X A
  let L := ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
    (fun j ↦ ULift.up (f j ^ (m + 1)))
  let K := koszulPowerSheaf X A r f m
  have hz (i : ℤ) (hi : 0 < i) : IsZero (K.X i) := by
    change IsZero (F.obj ((L.extend ComplexShape.embeddingDownNat).X i))
    apply F.map_isZero
    apply L.isZero_extend_X
    intro q
    change -(q : ℤ) ≠ i
    omega
  have hf (i : ℤ) : exactFunctor _ _ (tensorRight (K.X i)) := by
    by_cases hi : 0 < i
    · exact (ObjectProperty.flat_of_isZero (hz i hi)).2
    · obtain ⟨q, hq⟩ : ∃ q : ℕ, -(q : ℤ) = i := ⟨(-i).toNat, by omega⟩
      let e : K.X i ≅ F.obj (L.X q) :=
        F.mapIso (L.extendXIso ComplexShape.embeddingDownNat hq)
      exact (exactFunctor _ _).prop_of_iso ((curriedTensor B).flip.mapIso e.symm)
        (constant_exterior_flat X A r q)
  refine ⟨?_, hf⟩
  let : CochainComplex.IsStrictlyLE K 0 := (CochainComplex.isStrictlyLE_iff K 0).2 hz
  apply SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R K 0
  intro i
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (K.X i)).symm (hf i)

set_option backward.isDefEq.respectTransparency false in
/-- The recorded completed Koszul complex is K-flat, without a regularity assumption.
Source: Stacks Project, Tags 06YQ and 0G7E
(blueprint: lem-weil-pbc-completed-adic-koszul-kflat).

Proof: the constant functor is additive and sends the rank-one module to the unit,
as its sheafification Hom equivalence shows. The exterior-power basis presents
its Koszul terms as finite sums of that unit. Tensor with such a sum is a finite
sum of identity functors and is exact. Extension by zero to cochain indices is
bounded above, so the bounded flat criterion makes the constant Koszul complex
K-flat. The change-of-rings K-flat theorem applies to these flat terms. The
normalized scalar-extension witness identifies that changed complex with the
recorded completed Koszul complex, degree by degree and on differentials. -/
theorem completedAdicKoszul_isKFlat (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A) (m : ℕ) :
    CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d)
      (completedAdicKoszul T d r a m) := by
  let F := completedAdicScalarExtension T d
  let φ := completedAdicScalar T d
  let K := koszulPowerSheaf T A r a m
  let hobj := (completedAdicScalarExtensionData T d).choose_spec.choose
  let e : ((F.mapHomologicalComplex (.up ℤ)).obj K) ≅
      SheafOfModules.changeOfRingsComplex.{t + 1, t} φ K :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ eqToIso (hobj (K.X i))) (by
      intro i j hij
      symm
      change F.map (K.d i j) ≫ eqToHom (hobj (K.X j)) =
        eqToHom (hobj (K.X i)) ≫ SheafOfModules.changeOfRingsHom φ (K.X i) (K.d i j)
      have hm : F.map (K.d i j) = eqToHom (hobj (K.X i)) ≫
          SheafOfModules.changeOfRingsHom φ (K.X i) (K.d i j) ≫
            eqToHom (hobj (K.X j)).symm :=
        (completedAdicScalarExtensionData T d).choose_spec.choose_spec.choose (K.d i j)
      rw [hm]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
  have hK := koszulPowerSheaf_flat_kflat T A r a m
  have h := SheafOfModules.changeOfRings_isKFlat_of_flat_terms.{t + 1, t} φ K hK.1 hK.2
  let R := completedAdicCommRing T d
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro Z hZ i
  exact (h.1 Z hZ i).of_iso
    (((curriedTensor _).map₂CochainComplex.obj Z).mapIso e.symm)

end AlgebraicGeometry.Scheme
