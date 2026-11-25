/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
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
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.AlgebraicGeometry.Restricted.RestrictedScalarCoefficientLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteUnderlyingModels
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteActionLocalModels
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRestrictedTensorFiniteLocalConstancySupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import Mathlib.Algebra.Homology.SingleHomology

/-! # Finite local models for restricted scalar-extension cohomology

Source: Stacks Project, sites-cohomology.tex, Tag 094H,
lemma-locally-constant-tensor-product; sites-modules.tex, Tag 093S,
lemma-morphism-locally-constant; blueprint scalar-extension proof (2)
(blueprint: lem-sp-restricted-scalar-cohomology-local-constancy).

The scalar-extension helper retains independent site and localization universes.
The theorem gives finite B-module models separately in each cohomological degree.
-/

@[expose] public section
set_option autoImplicit false
universe uC vC r u wA wB
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Constant-coefficient derived scalar extension, with the right-factor target action.
Source: Stacks Project, Tag 06YY
(blueprint: lem-sp-restricted-scalar-cohomology-local-constancy).
The universal left-derived pair determines the selected functor up to its canonical
counit-compatible isomorphism. Its ordinary functor is sheafified scalar extension,
and its counit computes the tensor on K-flat representatives. -/
noncomputable def constantCoefficientScalarExtensionOfUniverses
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wA} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
        ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of A))))]
    [HasDerivedCategory.{wB} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
        ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of B))))] :
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
        ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of A)))) ⥤
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
        ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of B)))) :=
  (Classical.choice (nonempty_derivedChangeOfRingsCochainModel
    ((constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom f)))).T

end SheafOfModules

namespace AlgebraicGeometry.Scheme

-- Select the fixed-size instances only while elaborating this theorem.
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientRingSheafify in
/-- Derived extension of finite coefficients has finite local target-module models
in every degree after any restriction satisfying the stated input hypotheses.

Source: Stacks Project, Tags 094H and 093S; blueprint scalar-extension proof (2)
(blueprint: lem-sp-restricted-scalar-cohomology-local-constancy).

Proof:
1. Choose a cochain representative of K and a K-flat resolution P. Localization
and quasi-isomorphism give Q(P) ≅ K. Compare the cohomology in the chosen source
localization universe with ordinary cochain homology of P.
2. The restricted coefficient complex L = Res(B_T)[0] has finite locally constant
cohomology after arbitrary pullback, by the constant coefficient calculation in
lem-sp-restricted-scalar-coefficient-local-constancy. It vanishes above degree zero.
Transport the hypotheses on K to P. Exact coefficient pullback transports the bounds.
3. Apply lem-pur-proetale-restricted-tensor-finite-local-constancy to P, L and the
identity K-flat resolution of P. This gives local constancy over A_X and finite stalks.
4. The K-flat counit, the underlying ordinary tensor comparison, and exactness of
forgetting to abelian sheaves identify scalar-extension and tensor cohomology.
Both coefficient pullbacks have the same underlying set inverse image. This is
lem-sp-restricted-scalar-tensor-cohomology-comparison, with independent localization
universes retained. Compose with the image of Q(P) ≅ K.
5. Apply lem-sp-proetale-finite-underlying-models to the tensor cohomology. Finite
stalks give finite local models, with empty covering members included; base change
gives covering presieves on every site object. Transport these set models by step 4.
6. Apply lem-sp-proetale-finite-action-local-models. The finite-operation theorem
refines the B-action to finite constant B-module models. The constant-scalar
comparison identifies restricted global constants with the required localized
module construction. Every argument is for fixed q, so no common cover or lower
cohomological bound is imposed. -/
theorem restrictedScalarCohomology_finiteLocalModels
    {T X : Scheme.{u}} (a : X ⟶ T)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (f : A →+* B)
    [HasDerivedCategory.{wA} (proEtaleRingModules.{u} T (proEtaleConstantRing T A))]
    [HasDerivedCategory.{wB} (proEtaleRingModules.{u} T (proEtaleConstantRing T B))]
    (K : DerivedCategory (proEtaleRingModules.{u} T (proEtaleConstantRing T A)))
    (hKb : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules.{u} T (proEtaleConstantRing T A)) j).obj K))
    (hK : ∀ j : ℤ,
      IsLocallyConstantProEtaleModuleSheafOfUniverses.{u, u} X A
        (proEtaleConstantModulePullback a A
          ((DerivedCategory.homologyFunctor
            (proEtaleRingModules.{u} T (proEtaleConstantRing T A)) j).obj K)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A)
          (proEtaleConstantModulePullback a A
            ((DerivedCategory.homologyFunctor
              (proEtaleRingModules.{u} T (proEtaleConstantRing T A)) j).obj K))))
    (q : ℤ) :
    IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses.{u, u} X B (fun M ↦ Finite M)
      (proEtaleConstantModulePullback a B
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules.{u} T (proEtaleConstantRing T B)) q).obj
            ((SheafOfModules.constantCoefficientScalarExtensionOfUniverses.{u + 1, u, u + 1, wA, wB}
              (ProEt.topology T)
              ((ULift.ringEquiv : ULift.{u + 1, u} B ≃+* B).symm.toRingHom.comp
                (f.comp (ULift.ringEquiv : ULift.{u + 1, u} A ≃+* A).toRingHom))).obj K))) := by
  classical
  let 𝒜 := proEtaleRingModules T (proEtaleConstantRing T A)
  let ℬ := proEtaleRingModules T (proEtaleConstantRing T B)
  let D := Classical.choice
    (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel.{u + 1, u, u + 1, wA, wB}
      (restrictedScalarRingMap T f))
  change IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses.{u, u}
    X B (fun M ↦ Finite M)
      (proEtaleConstantModulePullback a B
        ((DerivedCategory.homologyFunctor ℬ q).obj (D.T.obj K)))
  let G := DerivedCategory.Q.objPreimage K
  obtain ⟨P, p, hP, _hflat, hp, _hepi⟩ := CochainComplex.exists_isKFlatResolutionGeneral G
  have := hp
  let eK : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let HK (j : ℤ) := (DerivedCategory.homologyFunctor 𝒜 j).obj K
  let eH (j : ℤ) : P.homology j ≅ HK j :=
    ((DerivedCategory.homologyFunctorFactors 𝒜 j).app P).symm ≪≫
      (DerivedCategory.homologyFunctor 𝒜 j).mapIso eK
  let L := restrictedScalarCoefficientComplex T f
  have ht : IsLocallyConstantProEtaleModuleSheaf X A
      (proEtaleConstantModulePullback a A (restrictedScalarTensorCohomology T f P hP q)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A)
          (proEtaleConstantModulePullback a A
            (restrictedScalarTensorCohomology T f P hP q))) := by
    let := HasDerivedCategory.standard 𝒜
    let e (j : ℤ) := (DerivedCategory.homologyFunctorFactors 𝒜 j).app P ≪≫ eH j
    have hPb : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero
        ((DerivedCategory.homologyFunctor 𝒜 j).obj (DerivedCategory.Q.obj P)) := by
      obtain ⟨b, hb⟩ := hKb
      exact ⟨b, fun j hj ↦ (hb j hj).of_iso (e j)⟩
    have hLb : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero
        ((DerivedCategory.homologyFunctor 𝒜 j).obj (DerivedCategory.Q.obj L)) := by
      refine ⟨0, fun j hj ↦ ?_⟩
      exact (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 _ j
        (ne_of_gt hj)).of_iso ((DerivedCategory.homologyFunctorFactors 𝒜 j).app L)
    apply proEtale_restrictedTensor_finiteLocalConstancy a A P L P (𝟙 P)
      (by infer_instance) hP
      (proEtaleConstantModulePullback_boundedAbove a A P hPb)
      (proEtaleConstantModulePullback_boundedAbove a A L hLb)
    · intro j _
      let e' := (proEtaleConstantModulePullbackFunctor a A).mapIso (e j)
      obtain ⟨hl, hs⟩ := hK j
      refine ⟨locallyConstant_of_iso X A e'.symm ?_, fun Ω _ _ x ↦ ?_⟩
      · obtain ⟨I, U, g, hg, he⟩ := hl
        exact ⟨I, U, g, hg, fun i ↦ ⟨(he i).choose, (he i).choose_spec.2⟩⟩
      · let : Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A)
          ((proEtaleConstantModulePullbackFunctor a A).obj (HK j))) := hs Ω x
        exact finite_stalk_of_iso X A e'.symm x
    · intro j _
      exact restrictedScalarCoefficient_finiteLocalConstancy a f j
  have hl : IsLocallyConstantProEtaleModuleSheafOfUniverses.{u, u} X A
      (proEtaleConstantModulePullback a A (restrictedScalarTensorCohomology T f P hP q)) := by
    obtain ⟨I, U, g, hg, he⟩ := ht.1
    exact ⟨I, U, g, hg, fun i ↦ ⟨(he i).choose, trivial, (he i).choose_spec⟩⟩
  have hsets := proEtale_finiteUnderlyingModels_of_locallyConstant X A _ hl ht.2
  let V := sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let e := V.mapIso ((SheafOfModules.toSheaf _).mapIso
    ((proEtaleConstantModulePullbackFunctor a B).mapIso
      ((DerivedCategory.homologyFunctor ℬ q).mapIso (D.T.mapIso eK).symm))) ≪≫
        (restrictedScalarTensorCohomologyComparison a f D P hP q).some
  apply proEtale_finiteLocalModels_of_finiteUnderlying X B
  intro U
  obtain ⟨S, hS, hs⟩ := hsets U
  refine ⟨S, hS, fun W g hg ↦ ?_⟩
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := hs W g hg
  exact ⟨Z, hZ, ⟨((ProEt.topology X).overPullback (Type (u + 1)) W).mapIso e ≪≫ eZ⟩⟩

end AlgebraicGeometry.Scheme
