/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.SmoothPurity.Sf.SfCommonStageWeilCohomology
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientImmersionRestriction
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
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousIntegralCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientLocalization
import WeilConjectures.AlgebraicGeometry.Rational.RationalModuleLocalizationTransport
import WeilConjectures.AlgebraicGeometry.Rational.RationalModuleLocalModelsTransport
import Mathlib.Algebra.Field.ULift

/-!
# Construction and cohomology of rational module realization

The realization asserted below has no full-faithfulness or essential-image equivalence
requirement. Field linearity is expressed by the canonical constant scalar action.

## References

* Bhatt--Scholze, Lemma 6.8.2, Proposition 6.8.11(3), and the construction in Proposition 6.8.14(2)
* Bhatt--Scholze, Section 6.8
* Bhatt--Scholze, Definition 6.8.1 and Proposition 6.8.14(2)
* Bhatt--Scholze, Definitions 6.8.6 and 6.8.10
* Bhatt--Scholze, Lemma 6.8.2, Proposition 6.8.11(3), and Proposition 6.8.14(2)
* Bhatt--Scholze, Lemma 6.8.2, Definition 6.8.10, Proposition 6.8.11(3), and the construction of
  Proposition 6.8.14(2)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual lifted inclusion of the valuation ring into its field. -/
def rationalModuleIntegerInclusion : PbcIntegralRing l E →+* ULift.{u + 1} E :=
  RingHom.ulift (Padic.coefficientExtensionIntegers l E).subtype

/-- Constant field sections, extended through constant-sheaf sheafification. -/
def rationalModuleConstantMap (X : Scheme.{u}) :
    adicLisseConstantRing X (ULift.{u + 1} E) ⟶ rationalCoefficientSheaf l X E := by
  letI := coefficientExtensionNormedField l E
  exact ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    _ _).symm
      { app := fun _ ↦ CommRingCat.ofHom
          { toFun := fun a ↦ ContinuousMap.const _ a
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        naturality := fun _ _ _ ↦ rfl }

/-- The rational model `E_X ⊗_E V`, using the existing constant module and sheaf tensor. -/
def rationalModuleConstantModel (X : Scheme.{u}) :
    ModuleCat.{u + 1} (ULift.{u + 1} E) ⥤ pbcModules X (rationalCoefficientSheaf l X E) :=
  adicLisseConstantModules X (ULift.{u + 1} E) ⋙ pbcExtend (rationalModuleConstantMap l E X)

/-- The raw realization and its specified scalar-localization computations.
All coefficient maps are fixed by their section or quotient normalizations.
The model clause is an ordinary tensor identity for every finitely presented N,
including torsion N. Its inverse images give the same identity on all stratum covers. -/
structure RationalModuleRealization (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] where
  /-- The completion is the sheaf of continuous integral functions. -/
  integralIso : pbcAdicCompletion X (pbcIntegralDatum l E) ≅
    integralCoefficientSheaf l X E
  /-- The finite quotients retain the continuous-function presentation. -/
  finiteIso : ∀ n : ℕ,
    (pbcAdicRings X (pbcIntegralDatum l E)).obj (op n) ≅
      finiteContinuousCoefficientSheaf l X E n
  /-- Finite quotient comparisons preserve constant sections. -/
  finite_normalization : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (a : PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1))
      (x : U.unop.left),
    finiteContinuousCoefficientValue l E X n U
      ((finiteIso n).hom.hom.app U
        (pbcFunctionScalars X (pbcIntegralDatum l E) n |>.app U |>.hom <| a)) x =
      integralCoefficientULift l E n a
  /-- The inverse-limit comparison is specified by all quotient projections. -/
  integral_normalization : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (s : (integralCoefficientSheaf l X E).obj.obj U) (x : U.unop.left),
    (finiteContinuousCoefficientValue l E X n U
      ((integralIso.inv ≫ pbcAdicProjection X (pbcIntegralDatum l E) n ≫
        (finiteIso n).hom).hom.app U s) x).down =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (integralCoefficientValue l E X U s x)
  /-- Sheaf localization, rather than a global denominator condition. -/
  localizationIso : integralCoefficientLocalization l X E ≅
    rationalCoefficientSheaf l X E
  /-- The localization comparison is the map on integral numerators. -/
  localization_normalization :
    integralCoefficientLocalizationNormalized l E X localizationIso.hom
  /-- Scalar inclusion is the actual inclusion of continuous functions. -/
  inclusion : integralCoefficientSheaf l X E ⟶ rationalCoefficientSheaf l X E
  /-- Pointwise normalization fixes the scalar inclusion uniquely. -/
  inclusion_normalization : integralRationalCoefficientNormalized l E X inclusion
  /-- Locally closed restriction preserves both coefficient rings and their scalar map. -/
  restriction : ∀ (S : Scheme.{u}) (h : S ⟶ X) [IsImmersion h],
    ∃ (cA : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
        (integralCoefficientSheaf l X E) ≅ integralCoefficientSheaf l S E)
      (cE : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
        (rationalCoefficientSheaf l X E) ≅ rationalCoefficientSheaf l S E)
      (aS : integralCoefficientSheaf l S E ⟶ rationalCoefficientSheaf l S E),
      integralCoefficientRestrictionNormalized l E h cA.hom ∧
      rationalCoefficientRestrictionNormalized l E h cE.hom ∧
      integralRationalCoefficientNormalized l E S aS ∧
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map inclusion ≫ cE.hom =
        cA.hom ≫ aS
  /-- The module category carries the field action of constant sections. -/
  [moduleLinear : Linear E (pbcModules X (rationalCoefficientSheaf l X E))]
  /-- The field action is fixed on every module map by multiplication by a constant section. -/
  scalar_normalization : ∀ (M N : pbcModules X (rationalCoefficientSheaf l X E))
      (f : M ⟶ N) (a : E) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
    (a • f).val.app U x =
      (rationalModuleConstantMap l E X).hom.app U
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))).app U
            (ULift.up a)) • f.val.app U x
  /-- Ordinary scalar localization is exact on module sheaves. -/
  ordinary_exact : PreservesFiniteLimits (pbcExtend (integralIso.hom ≫ inclusion)) ∧
    PreservesFiniteColimits (pbcExtend (integralIso.hom ≫ inclusion))
  /-- The prescribed derived scalar extension is triangulated. -/
  derived_exact : ∃ (_ : (pbcDerivedExtend (integralIso.hom ≫ inclusion)).CommShift ℤ),
    (pbcDerivedExtend (integralIso.hom ≫ inclusion)).IsTriangulated
  /-- Cohomology commutes naturally with localization in every integer degree. -/
  cohomology : ∀ r : ℤ,
    pbcDerivedExtend (integralIso.hom ≫ inclusion) ⋙ DerivedCategory.homologyFunctor _ r ≅
      DerivedCategory.homologyFunctor _ r ⋙ pbcExtend (integralIso.hom ≫ inclusion)
  /-- Bounded integral objects have bounded, stratified locally finite free rational cohomology. -/
  constructible : ∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
    (∃ a b : ℤ,
      ((pbcDerivedExtend (integralIso.hom ≫ inclusion)).obj K.obj).IsGE a ∧
      ((pbcDerivedExtend (integralIso.hom ≫ inclusion)).obj K.obj).IsLE b) ∧
    ∀ r : ℤ, ∃ s : FiniteLocallyClosedStratification X, ∀ i : Fin s.n,
      ((proEtaleModuleInverseImage (s.immersion i)
        (rationalCoefficientSheaf l X E)).obj
          ((DerivedCategory.homologyFunctor _ r).obj
            ((pbcDerivedExtend (integralIso.hom ≫ inclusion)).obj K.obj))).IsFiniteLocallyFree
  /-- The raw rationalization has its unchanged integral objects. -/
  J : PbcRationalCategory X (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
    DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))
  /-- Addition and the canonical E-action are preserved. -/
  [additive : J.Additive]
  /-- E-linearity for the canonical localization action and constant field sections. -/
  [linear : J.Linear E]
  /-- Integer shifts commute with realization. -/
  [shift : J.CommShift ℤ]
  /-- Distinguished triangles are preserved. -/
  triangulated : J.IsTriangulated
  /-- The displayed formula on QK is literal equality of objects. -/
  objects : ∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
    J.obj ((pbcRationalization X (pbcIntegralDatum l E)
      (pbcUniformizer l E)).obj K) =
        (pbcDerivedExtend (integralIso.hom ≫ inclusion)).obj K.obj
  /-- The displayed formula on every fraction, with transports for the object equalities. -/
  fractions : ∀ (K L : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
      (f : K ⟶ L) (n : ℕ),
    J.map (((pbcRationalCoefficientEquiv l E).symm
      (((pbcUniformizer l E).down.val ^ n)⁻¹)) •
        (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
      eqToHom (objects K) ≫
        (((pbcUniformizer l E).down.val ^ n)⁻¹ •
          (pbcDerivedExtend (integralIso.hom ≫ inclusion)).map f.hom) ≫
            eqToHom (objects L).symm
  /-- The integral model localizes to E_X tensor the finite-dimensional space E tensor N. -/
  models : ∀ (N : ModuleCat.{u + 1} (PbcIntegralRing l E)),
    Module.FinitePresentation (PbcIntegralRing l E) N →
      Nonempty ((pbcExtend (integralIso.hom ≫ inclusion)).obj
        ((integralConstantModule X (pbcIntegralDatum l E)).obj N) ≅
          (rationalModuleConstantModel l E X).obj
            ((ModuleCat.extendScalars (rationalModuleIntegerInclusion l E)).obj N)) ∧
      Module.Finite (ULift.{u + 1} E)
        ((ModuleCat.extendScalars (rationalModuleIntegerInclusion l E)).obj N) ∧
      Module.Free (ULift.{u + 1} E)
        ((ModuleCat.extendScalars (rationalModuleIntegerInclusion l E)).obj N)

private theorem rationalFiniteScalars_constantUnit
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (W : Scheme.{u}) (n : ℕ) :
    pbcFunctionScalars W d n = Functor.whiskerRight
      (toSheafify (ProEt.topology W)
          ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient d n))) ≫
        (pbcLevelConstantComparison W d n).hom.hom)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  let e := AdicCoefficients.finiteRingComparison W (ProEtale.PbcQuotient d n)
  have he : Functor.whiskerRight (toSheafify (ProEt.topology W)
        (AdicCoefficients.functionPresheaf W (ProEtale.PbcQuotient d n)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫ e.hom.hom =
        AdicCoefficients.finiteRingUnit W (ProEtale.PbcQuotient d n) :=
    (AdicCoefficients.finiteRingComparison_exists W
      (ProEtale.PbcQuotient d n)).choose_spec.1.2
  have hconst : toSheafify (ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient d n))) ≫
      (pbcLevelConstantComparison W d n).hom.hom =
        AdicCoefficients.constants W (ProEtale.PbcQuotient d n) ≫
          toSheafify (ProEt.topology W)
            (AdicCoefficients.functionPresheaf W (ProEtale.PbcQuotient d n)) := by
    ext U b
    exact (pbcLevelConstantComparison_exists W d n).exists.choose_spec U b
  rw [hconst]
  apply (cancel_mono e.hom.hom).1
  have hi : e.inv.hom ≫ e.hom.hom = 𝟙 _ := congrArg
    (fun f : AdicCoefficients.finiteRingPresentation W (ProEtale.PbcQuotient d n) ⟶
      AdicCoefficients.finiteRingPresentation W (ProEtale.PbcQuotient d n) ↦ f.hom)
    e.inv_hom_id
  change (ProEtale.finiteCoefficientScalarMap W (ProEtale.PbcQuotient d n) ≫
    e.inv.hom) ≫ e.hom.hom = _
  rw [Category.assoc, hi]
  erw [Category.comp_id]
  rw [Functor.whiskerRight_comp, Category.assoc, he]
  rfl

attribute [local irreducible] pbcRationalCoefficientEquiv pbcIntegralDatum
  reductionDerivedChange completedAdicDerivedChange

attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory in
/-- Scalar localization induces the raw rational module realization, with its
coefficient, cohomology, constructibility and local-model normalizations. -/
theorem rationalModuleRealizationFunctor (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] :
    Nonempty (RationalModuleRealization l E X) := by
  classical
  let d := pbcIntegralDatum l E
  let C := constantSheaf (ProEt.topology X) CommRingCat.{u + 1}
  let b := AlgebraicGeometry.ProEtale.completedIso X l E
  obtain ⟨c, hc⟩ := continuousCoefficientCompletion l E X
  choose q hq hqn using hc
  let i := b ≪≫ c.symm
  let e (n : ℕ) := (pbcLevelConstantComparison X d n).symm ≪≫
    C.mapIso (integralCoefficientULift l E n).toCommRingCatIso ≪≫ q n
  have hb (n : ℕ) : b.hom ≫ limit.π (finiteCoefficientTower l X E) (op n) =
      pbcAdicProjection X d n ≫ (pbcLevelConstantComparison X d n).inv ≫
        C.map (integralCoefficientULift l E n).toCommRingCatIso.hom := by
    dsimp only [b, AlgebraicGeometry.ProEtale.completedIso, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π]
    change (pbcCompletedComparison X d).inv ≫
      (limit.π (adicLisseRingSystem X d.ideal) (op n) ≫
        C.map (integralCoefficientULift l E n).toCommRingCatIso.hom) = _
    simp only [pbcCompletedComparison, HasLimit.isoOfNatIso_inv_π_assoc]
    rfl
  have hi (n : ℕ) : i.inv ≫ pbcAdicProjection X d n ≫ (e n).hom =
      c.hom ≫ limit.π (finiteCoefficientTower l X E) (op n) ≫ (q n).hom := by
    dsimp only [i, Iso.trans_inv, Iso.symm_inv, e, Iso.trans_hom, Iso.symm_hom]
    calc
      _ = c.hom ≫ b.inv ≫
          (pbcAdicProjection X d n ≫ (pbcLevelConstantComparison X d n).inv ≫
            C.map (integralCoefficientULift l E n).toCommRingCatIso.hom) ≫ (q n).hom := by
        simp only [Functor.mapIso_hom, Category.assoc]
      _ = _ := by
        rw [← hb]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hf (n : ℕ) (U : X.ProEtᵒᵖ)
      (a : PbcIntegralRing l E ⧸ d.ideal ^ (n + 1)) :
      (e n).hom.hom.app U ((pbcFunctionScalars X d n).app U a) =
        (q n).hom.hom.app U
          ((toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (finiteCoefficientRing l E n))).app U
              (integralCoefficientULift l E n a)) := by
    have hu := congrArg (fun z ↦ z.app U) (rationalFiniteScalars_constantUnit d X n)
    have hu' := ConcreteCategory.congr_hom hu a
    change (pbcFunctionScalars X d n).app U a =
      (pbcLevelConstantComparison X d n).hom.hom.app U
        ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (PbcIntegralRing l E ⧸ d.ideal ^ (n + 1))))).app U a) at hu'
    rw [hu']
    change (((pbcLevelConstantComparison X d n).hom ≫ (e n).hom).hom.app U) _ = _
    dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    simp only [Iso.hom_inv_id_assoc, Functor.mapIso_hom]
    have hn := ConcreteCategory.congr_hom
      (congr_app (toSheafify_naturality (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).map
          (integralCoefficientULift l E n).toCommRingCatIso.hom)) U) a
    exact congrArg ((q n).hom.hom.app U) hn.symm
  have hs : pbcCompletedScalar X d ≫ i.hom =
      (letI := coefficientExtensionNormedField l E
       continuousCoefficientConstantComparison X (PbcIntegralRing l E)) := by
    let := coefficientExtensionNormedField l E
    apply (cancel_mono c.hom).mp
    change (pbcCompletedScalar X d ≫ (b.hom ≫ c.inv)) ≫ c.hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply limit.hom_ext
    intro n
    dsimp only [b]
    simp only [Category.assoc]
    rw [ProEtale.completedIso_scalar X l E n.unop]
    apply (cancel_mono (q n.unop).hom).mp
    apply ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (PbcIntegralRing l E))) _).injective
    simp only [← Functor.map_comp, constantSheaf, Functor.comp_map, Category.assoc]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    have hη : ((sheafificationAdjunction (ProEt.topology X)
        CommRingCat.{u + 1}).homEquiv
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (PbcIntegralRing l E)))
          (integralCoefficientSheaf l X E))
          (continuousCoefficientConstantComparison X (PbcIntegralRing l E)) =
        continuousCoefficientConstants X (PbcIntegralRing l E) :=
      Equiv.apply_symm_apply
        ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (PbcIntegralRing l E)))
          (continuousCoefficientSheaf X (PbcIntegralRing l E))) _
    erw [hη]
    apply NatTrans.ext
    funext V
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    let : TopologicalSpace (finiteCoefficientRing l E n.unop) := ⊥
    let : DiscreteTopology (finiteCoefficientRing l E n.unop) := ⟨rfl⟩
    apply ContinuousMap.ext
    intro x
    change finiteContinuousCoefficientValue l E X n.unop V
      ((q n.unop).hom.hom.app V ((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (finiteCoefficientRing l E n.unop))).app V _)) x = _
    rw [hq]
    change integralCoefficientULift l E n.unop (Ideal.Quotient.mk _ a) = _
    have hu : integralCoefficientULift l E n.unop (Ideal.Quotient.mk _ a) =
        ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1))
          a.down) :=
      (integralCoefficientULift_exists l E n.unop).exists.choose_spec a
    erw [hu]
    apply ULift.ext
    exact (hqn n.unop V ((continuousCoefficientConstants X (PbcIntegralRing l E)).app V a)
      x).symm
  obtain ⟨κ, hκ, hex, hdex, hcoh, J, hJadd, hJlin, hJshift, hJtri, hobj, hfrac⟩ :=
    rationalModuleLocalizationTransport l E X i hs
  obtain ⟨hlocal, hmodels⟩ := rationalModuleLocalModelsTransport l E X i hs
  obtain ⟨loc, hloc⟩ := continuousCoefficientLocalization l E X
  let := κ
  let := hJadd
  let := hJlin
  let := hJshift
  let := hex.1
  let := hex.2
  refine ⟨{
    integralIso := i
    finiteIso := e
    finite_normalization := ?_
    integral_normalization := ?_
    localizationIso := loc
    localization_normalization := hloc
    inclusion := integralRationalCoefficientMap l E X
    inclusion_normalization := integralRationalCoefficientMap_normalized l E X
    restriction := ?_
    moduleLinear := κ
    scalar_normalization := ?_
    ordinary_exact := hex
    derived_exact := hdex
    cohomology := fun r ↦ Classical.choice (hcoh r)
    constructible := ?_
    J := J
    additive := hJadd
    linear := hJlin
    shift := hJshift
    triangulated := hJtri
    objects := hobj
    fractions := hfrac
    models := ?_
  }⟩
  · intro n U a x
    rw [hf]
    exact hq n U (integralCoefficientULift l E n a) x
  · intro n U s x
    rw [hi]
    exact hqn n U s x
  · intro S h _
    obtain ⟨_, _, cA, cE, _, _, hnA, hnE, ⟨aX, aS, haX, haS, hsq⟩, _⟩ :=
      continuousCoefficientImmersionRestriction l E X h
    have heq : aX = integralRationalCoefficientMap l E X := by
      let := coefficientExtensionNormedField l E
      apply Sheaf.hom_ext
      ext V s
      apply ContinuousMap.ext
      intro x
      apply ULift.down_injective
      exact (haX V.unop s x).trans
        ((integralRationalCoefficientMap_normalized l E X) V.unop s x).symm
    exact ⟨cA, cE, aS, hnA, hnE, haS, heq ▸ hsq⟩
  · intro M N f a U x
    let := coefficientExtensionNormedField l E
    have hn : (rationalModuleConstantMap l E X).hom.app U
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))).app U
            (ULift.up a)) =
        (show (rationalCoefficientSheaf l X E).obj.obj U from
          ContinuousMap.const _ (ULift.up a)) := by
      change (((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))) ≫
          (rationalModuleConstantMap l E X).hom).app U) (ULift.up a) = _
      change ((((sheafificationAdjunction (ProEt.topology X)
        CommRingCat.{u + 1}).homEquiv _ _)
          (rationalModuleConstantMap l E X)).app U) (ULift.up a) = _
      rw [rationalModuleConstantMap, Equiv.apply_symm_apply]
      rfl
    rw [hn]
    exact hκ M N f a U x
  · intro K
    have hl : IsUnit (l : Γ(X, ⊤)) := by
      apply X.toRingedSpace.isUnit_of_isUnit_germ
      intro x hx
      simpa only [map_natCast] using
        (Fact.out : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) x
    have hk := integralStratifiedPerfectCharacterization X l E Fact.out hl K.obj
    obtain ⟨⟨a, b, _, ha, hb⟩, hpres⟩ := hk.2.mp (hk.1.mp K.property)
    constructor
    · refine ⟨a, b, (DerivedCategory.isGE_iff _ a).mpr ?_,
        (DerivedCategory.isLE_iff _ b).mpr ?_⟩
      · intro r hr
        exact ((pbcExtend (i.hom ≫ integralRationalCoefficientMap l E X)).map_isZero
          ((DerivedCategory.isGE_iff _ a).mp ha r hr)).of_iso
            ((Classical.choice (hcoh r)).app K.obj)
      · intro r hr
        exact ((pbcExtend (i.hom ≫ integralRationalCoefficientMap l E X)).map_isZero
          ((DerivedCategory.isLE_iff _ b).mp hb r hr)).of_iso
            ((Classical.choice (hcoh r)).app K.obj)
    · intro r
      obtain ⟨s, hsf⟩ := hlocal _ (hpres r)
      refine ⟨s, fun k ↦ ?_⟩
      exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1}
        (h := hsf k)
        ((proEtaleModuleInverseImage (s.immersion k) (rationalCoefficientSheaf l X E)).mapIso
          ((Classical.choice (hcoh r)).app K.obj)).symm
  · intro N hN
    let := hN
    let := (rationalModuleIntegerInclusion l E).toAlgebra
    refine ⟨?_, ?_, ?_⟩
    · exact hmodels N hN
    · change Module.Finite (ULift.{u + 1} E)
        (TensorProduct (PbcIntegralRing l E) (ULift.{u + 1} E) N)
      infer_instance
    · infer_instance

end AlgebraicGeometry.Scheme
