/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
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
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
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
import Mathlib.CategoryTheory.Localization.Prod

/-! # Derived projection for extension from a ringed slice

Source: Stacks Project, Tags 0E8I and 06YN
(blueprint: lem-weil-pbc-ringed-open-derived-tensor-projection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules WeilConjectures
namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

-- Check the comparison diagram with abstract functors before specializing it.
private theorem projectionComparison
    {A B DA DB : Type*} [Category A] [Category B] [Category DA] [Category DB]
    (P : ObjectProperty A) (Q : ObjectProperty B)
    (Ec : A ⥤ B) (Fc : B ⥤ A)
    (hE : ∀ X : P.FullSubcategory, Q (Ec.obj X.obj))
    (hF : ∀ X : Q.FullSubcategory, P (Fc.obj X.obj))
    (qA : A ⥤ DA) (qB : B ⥤ DB) (Ed : DA ⥤ DB) (Fd : DB ⥤ DA)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (tA : DA × DA ⥤ DA) (tB : DB × DB ⥤ DB)
    (a : qA ⋙ Ed ≅ Ec ⋙ qB) (b : qB ⋙ Fd ≅ Fc ⋙ qA)
    (cA : (P.ι.prod P.ι) ⋙ TA ⋙ qA ≅
      ((P.ι ⋙ qA).prod (P.ι ⋙ qA)) ⋙ tA)
    (cB : (Q.ι.prod Q.ι) ⋙ TB ⋙ qB ≅
      ((Q.ι ⋙ qB).prod (Q.ι ⋙ qB)) ⋙ tB)
    (cp : ((𝟭 A).prod Fc) ⋙ TA ⋙ Ec ≅ (Ec.prod (𝟭 B)) ⋙ TB) :
    Nonempty (((P.ι ⋙ qA).prod (Q.ι ⋙ qB)) ⋙
      (((𝟭 DA).prod Fd) ⋙ tA ⋙ Ed) ≅
      ((P.ι ⋙ qA).prod (Q.ι ⋙ qB)) ⋙ ((Ed.prod (𝟭 DB)) ⋙ tB)) := by
  let eK := Q.lift (P.ι ⋙ Ec) hE
  let fK := P.lift (Q.ι ⋙ Fc) hF
  let ea : (P.ι ⋙ qA) ⋙ Ed ≅ eK ⋙ Q.ι ⋙ qB := Functor.isoWhiskerLeft P.ι a
  let fb : (Q.ι ⋙ qB) ⋙ Fd ≅ fK ⋙ P.ι ⋙ qA := Functor.isoWhiskerLeft Q.ι b
  let e₁ := Functor.isoWhiskerRight (NatIso.prod (Iso.refl (P.ι ⋙ qA)) fb) (tA ⋙ Ed)
  let e₂ := Functor.isoWhiskerLeft ((𝟭 _).prod fK)
    (Functor.isoWhiskerRight cA.symm Ed)
  let e₃ := Functor.isoWhiskerLeft ((P.ι.prod (Q.ι ⋙ Fc)) ⋙ TA) a
  let e₄ := Functor.isoWhiskerLeft (P.ι.prod Q.ι) (Functor.isoWhiskerRight cp qB)
  let e₅ := Functor.isoWhiskerLeft (eK.prod (𝟭 _)) cB
  let e₆ := (Functor.isoWhiskerRight (NatIso.prod ea (Iso.refl (Q.ι ⋙ qB))) tB).symm
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅ ≪≫ e₆⟩

private theorem projectionIsoType_eq
    {A B : Type*} [Category A] [Category B] (E : A ⥤ B) (F : B ⥤ A)
    {TA TA' : A × A ⥤ A} {TB TB' : B × B ⥤ B} (a : TA = TA') (b : TB = TB') :
    (((𝟭 A).prod F) ⋙ TA ⋙ E ≅ (E.prod (𝟭 B)) ⋙ TB) =
      (((𝟭 A).prod F) ⋙ TA' ⋙ E ≅ (E.prod (𝟭 B)) ⋙ TB') := by
  cases a
  cases b
  rfl

private theorem totalTensor_eq_curried :
    coefficientTotalTensor.{r, c, v} J R =
      Functor.uncurry.obj (ringedOpenTotalTensor.{c, v, r} R) := by
  rfl

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem chosenProjection_spec :
    type_of% ((ringedOpen_totalTensor_kFlat.{c, v, r} R U).1.choose_spec) :=
  (ringedOpen_totalTensor_kFlat.{c, v, r} R U).1.choose_spec

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem chosenProjection_naturality :
    type_of% ((chosenProjection_spec.{c, v, r} J R U).choose_spec.2) :=
  (chosenProjection_spec.{c, v, r} J R U).choose_spec.2

-- Descending the unbounded tensor comparison elaborates several localization functors.
private def complexProjection :
    ((𝟭 _).prod (ringedOpenRestrictionOnComplexes.{c, v, r} R U)) ⋙
        coefficientTotalTensor.{r, max c v, v} (J.over U) (R.over U) ⋙
          ringedOpenExtensionOnComplexes.{c, v, r} R U ≅
      ((ringedOpenExtensionOnComplexes.{c, v, r} R U).prod (𝟭 _)) ⋙
        coefficientTotalTensor.{r, c, v} J R := by
  refine cast (projectionIsoType_eq
    (ringedOpenExtensionOnComplexes.{c, v, r} R U)
    (ringedOpenRestrictionOnComplexes.{c, v, r} R U)
    (totalTensor_eq_curried.{max c v, v, r} (J.over U) (R.over U))
    (totalTensor_eq_curried.{c, v, r} J R)).symm ?_
  let Φ := (chosenProjection_spec.{c, v, r} J R U).choose
  refine NatIso.ofComponents (fun X ↦ Φ X.1 X.2) ?_
  intro X Y f
  simpa only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
    Functor.comp_map, Functor.prod_map, Functor.id_map,
    Functor.uncurry_obj_obj, Functor.uncurry_obj_map, ringedOpenTotalTensorMap] using
      chosenProjection_naturality.{c, v, r} J R U X.1 Y.1 X.2 Y.2 f.1 f.2

variable [HasDerivedCategory.{w} (RingedDerivedNative.Modules.{c, v, r} J R)]
  [HasDerivedCategory.{w}
    (RingedDerivedNative.Modules.{max c v, v, r} (J.over U) (R.over U))]

-- The unbounded derived comparisons require elaborating several functor structures.
attribute [local irreducible] complexProjection RingedDerivedNative.comparison
  coefficientTotalTensor in
/-- Extension from a slice satisfies the unbounded derived tensor projection formula,
naturally in the slice object and the ambient object.
Source: Stacks Project, Tags 0E8I and 06YN
(blueprint: lem-weil-pbc-ringed-open-derived-tensor-projection).

Proof: on complexes, extension of P tensor the restriction of Q is naturally
isomorphic to the tensor of the extension of P with Q. This is the sheafified
summand projection formula, totalized with the same cochain signs. Restriction
and extension both preserve K-flat complexes. On their K-flat presentations the
specified derived tensor comparisons, the exact-functor localization comparisons,
and the complex projection formula therefore give a natural isomorphism between
the two displayed derived functors. The product of the two K-flat localization
functors is a localization. Precomposition with it is fully faithful, so the
natural isomorphism descends uniquely. This treats unbounded complexes, empty
slices, and zero objects without finiteness hypotheses. -/
theorem ringedOpenDerived_tensorProjection :
    let F : RingedDerivedNative.Modules.{c, v, r} J R ⥤
        RingedDerivedNative.Modules.{max c v, v, r} (J.over U) (R.over U) :=
      localizedSystemRestriction.{c, v, r} R U
    let E : RingedDerivedNative.Modules.{max c v, v, r} (J.over U) (R.over U) ⥤
        RingedDerivedNative.Modules.{c, v, r} J R :=
      localizedSystemExtension.{c, v, r} R U
    letI : F.Additive := localizedSystemRestrictionAdditive.{c, v, r} R U
    letI : E.Additive := localizedSystemExtensionAdditive.{c, v, r} R U
    letI : PreservesFiniteLimits E := localizedSystemExtensionLimits.{c, v, r} R U
    letI : PreservesFiniteColimits E := localizedSystemExtensionColimits.{c, v, r} R U
    letI : PreservesFiniteLimits F := localizedSystemRestrictionLimits.{c, v, r} R U
    letI : PreservesFiniteColimits F := localizedSystemRestrictionColimits.{c, v, r} R U
    Nonempty (
      ((𝟭 _).prod F.mapDerivedCategory) ⋙
          @tensor _ _ (RingedDerivedNative.monoidal.{max c v, v, r, w}
            (J.over U) (R.over U)) ⋙
          E.mapDerivedCategory ≅
        ((E.mapDerivedCategory).prod (𝟭 _)) ⋙
          @tensor _ _ (RingedDerivedNative.monoidal.{c, v, r, w} J R)) := by
  let E : RingedDerivedNative.Modules.{max c v, v, r} (J.over U) (R.over U) ⥤
      RingedDerivedNative.Modules.{c, v, r} J R := localizedSystemExtension.{c, v, r} R U
  let F : RingedDerivedNative.Modules.{c, v, r} J R ⥤
      RingedDerivedNative.Modules.{max c v, v, r} (J.over U) (R.over U) :=
    localizedSystemRestriction.{c, v, r} R U
  let : E.Additive := localizedSystemExtensionAdditive.{c, v, r} R U
  let : F.Additive := localizedSystemRestrictionAdditive.{c, v, r} R U
  let : PreservesFiniteLimits E := localizedSystemExtensionLimits.{c, v, r} R U
  let : PreservesFiniteColimits E := localizedSystemExtensionColimits.{c, v, r} R U
  let : PreservesFiniteLimits F := localizedSystemRestrictionLimits.{c, v, r} R U
  let : PreservesFiniteColimits F := localizedSystemRestrictionColimits.{c, v, r} R U
  let Ec := E.mapHomologicalComplex (.up ℤ)
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let K := coefficientKFlatInclusion.{r, c, v} J R
  let KU := coefficientKFlatInclusion.{r, max c v, v} (J.over U) (R.over U)
  let L := K ⋙ DerivedCategory.Q.{w}
  let LU := KU ⋙ DerivedCategory.Q.{w}
  let W := (HomologicalComplex.quasiIso (RingedDerivedNative.Modules.{c, v, r} J R)
    (.up ℤ)).inverseImage K
  let WU := (HomologicalComplex.quasiIso
    (RingedDerivedNative.Modules.{max c v, v, r} (J.over U) (R.over U))
      (.up ℤ)).inverseImage KU
  have : L.IsLocalization W := RingedDerivedNative.kFlatLocalization.{c, v, r, w} J R
  have : LU.IsLocalization WU :=
    RingedDerivedNative.kFlatLocalization.{max c v, v, r, w} (J.over U) (R.over U)
  obtain ⟨e₀⟩ := projectionComparison
    (CochainComplex.IsKFlatIndependentCoefficients (J := J.over U) (R := R.over U))
    (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R))
    Ec Fc
    (fun P ↦ (ringedOpen_totalTensor_kFlat.{c, v, r} R U).2.1 P.obj P.property)
    (fun P ↦ (ringedSite_restriction_exact_kflat.{c, v, r} J R U).2.2 P.obj P.property)
    DerivedCategory.Q.{w} DerivedCategory.Q.{w}
    E.mapDerivedCategory F.mapDerivedCategory
    (coefficientTotalTensor.{r, max c v, v} (J.over U) (R.over U))
    (coefficientTotalTensor.{r, c, v} J R)
    (@tensor _ _ (RingedDerivedNative.monoidal.{max c v, v, r, w}
      (J.over U) (R.over U)))
    (@tensor _ _ (RingedDerivedNative.monoidal.{c, v, r, w} J R))
    E.mapDerivedCategoryFactors F.mapDerivedCategoryFactors
    (RingedDerivedNative.comparison.{max c v, v, r, w} (J.over U) (R.over U))
    (RingedDerivedNative.comparison.{c, v, r, w} J R)
    (complexProjection.{c, v, r} J R U)
  exact ⟨(Localization.fullyFaithfulWhiskeringLeft (LU.prod L) (WU.prod W)
    (DerivedCategory (RingedDerivedNative.Modules.{c, v, r} J R))).preimageIso e₀⟩

end CategoryTheory
