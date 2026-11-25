/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalScalarBalancedLocalization
public import WeilConjectures.AlgebraicGeometry.Rational.RationalScalarCompletionUnitSquare
public import WeilConjectures.AlgebraicGeometry.Rational.RationalPullbackCompositionCoherence
public import WeilConjectures.CategoryTheory.ProperBaseChange.LocalizationInverseImageCoherence
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Rational.RationalScalarMixedIntegralGeometric
import WeilConjectures.AlgebraicGeometry.Rational.RationalScalarMixedIntegralTower
import WeilConjectures.AlgebraicGeometry.Rational.RationalScalarMixedNormalizationAssoc
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalAdjunctionUnit
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.Rational.RationalPullbackFlatComputationCounit
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleRationalHomComparison

/-! # Cancellation in the specified mixed rational realization square

Theta and D below are rationalBalancedTheta and extension along
rationalBalancedCoefficient. The completed comparison is rationalScalarStrictBeta.
The pullback alpha is the supplied, generator-normalized dependency record's alpha.
The ordinary zeta is normalized on tensor generators and derived computation counits.

## References

* Bhatt--Scholze, Remark 6.8.15, pp. 61--62
* Stacks 0D6D, 0A0E and 0A0G
* Stacks 0D6D, 099N
* Stacks 0G7E, 0D6D and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
variable (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- The specified strict beta, restricted and rationalized, on every unchanged raw object. -/
def rationalMixedBetaComponent (g : X ⟶ Y)
    (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
    (sXF : RationalModuleRealization l F X) (sYF : RationalModuleRealization l F Y)
    (aE : RationalRealizationPullbackComparison l E g sXE sYE)
    (aF : RationalRealizationPullbackComparison l F g sXF sYF)
    (K : PbcRationalDerivedCategory l E Y Fact.out Fact.out) :
    (pbcRationalScalarExtension l E F i X Fact.out Fact.out).obj (aE.rawPull.obj K) ≅
      aF.rawPull.obj ((pbcRationalScalarExtension l E F i Y Fact.out Fact.out).obj K) :=
  (pbcRationalScalarExtension l E F i X Fact.out Fact.out).mapIso
      (eqToIso (aE.raw_objects K.obj)) ≪≫
    (pbcRationalization X (pbcIntegralDatum l F) (pbcUniformizer l F)).mapIso
      (ObjectProperty.isoMk _
        (X := (pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj
          ((aE.integral.completedFunctor l E).obj K.obj))
        (Y := (aF.integral.completedFunctor l F).obj
          ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K.obj))
        ((rationalScalarStrictBeta l E F i g).app K.obj.obj)) ≪≫
    (eqToIso (aF.raw_objects
      ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K.obj))).symm

/-- The mixed square for the specific alpha and the specified scalar/pullback comparison.
The ordinary comparison is fixed on tensor units and on derived computation counits;
its section formula determines the balanced map, including all coefficient factors. -/
structure RationalScalarMixedUnitCancellation (g : X ⟶ Y)
    (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
    (sXF : RationalModuleRealization l F X) (sYF : RationalModuleRealization l F Y)
    (aE : RationalRealizationPullbackComparison l E g sXE sYE)
    (aF : RationalRealizationPullbackComparison l F g sXF sYF)
    where
  /-- The localized finite-quotient coefficient square. -/
  coefficient_square : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      (rationalBalancedCoefficient l E F i Y) ≫ aF.rationalCoefficient = aE.rationalCoefficient ≫
      (rationalBalancedCoefficient l E F i X)
  /-- The ordinary scalar/pullback comparison. -/
  ordinary : pbcExtend (rationalBalancedCoefficient l E F i Y) ⋙ rationalPullModule l F g
      aF.rationalCoefficient ≅
    rationalPullModule l E g aE.rationalCoefficient ⋙ pbcExtend (rationalBalancedCoefficient l E F
      i X)
  /-- Inserting tensor units gives the same pulled-back generator on both sides.
  Scalar linearity then gives l' tensor b' tensor k ↦ l'b' tensor g⁻¹k. -/
  ordinary_units : ∀ (M : pbcModules Y (rationalCoefficientSheaf l Y E))
      (V : Y.ProEt) (m : M.val.obj (op V)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (pbcTensorSection aF.rationalCoefficient
        ((proEtaleRingModulePullback g (rationalCoefficientSheaf l Y F)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y F)) (Iso.refl _)).obj
              ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M))
        (op ((proEtaleBaseChange g).obj V)) 1
        (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l Y F)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y F)) (Iso.refl _)
          ((pbcExtend (rationalBalancedCoefficient l E F i Y)).obj M) V
          (pbcTensorSection (rationalBalancedCoefficient l E F i Y) M (op V) 1 m))) =
    pbcTensorSection (rationalBalancedCoefficient l E F i X)
      ((rationalPullModule l E g aE.rationalCoefficient).obj M)
      (op ((proEtaleBaseChange g).obj V)) 1
      (pbcTensorSection aE.rationalCoefficient
        ((proEtaleRingModulePullback g (rationalCoefficientSheaf l Y E)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y E)) (Iso.refl _)).obj M)
        (op ((proEtaleBaseChange g).obj V)) 1
        (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l Y E)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y E)) (Iso.refl _) M V m))
  /-- Its derived comparison. -/
  zeta : rationalPullDerived l E g aE.rationalCoefficient ⋙
      pbcDerivedExtend (rationalBalancedCoefficient l E F i X) ≅
    pbcDerivedExtend (rationalBalancedCoefficient l E F i Y) ⋙
      rationalPullDerived l F g aF.rationalCoefficient
  /-- The ordinary balanced map is the computation of that derived comparison. -/
  ambient_normalization : ∀ P : CochainComplex
      (pbcModules Y (rationalCoefficientSheaf l Y E)) ℤ,
    zeta.inv.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
          (rationalPullComplexCounit l E g aE.rationalCoefficient P) ≫
        pbcComplexCounit (rationalBalancedCoefficient l E F i X)
          (((rationalPullModule l E g aE.rationalCoefficient).mapHomologicalComplex
            (.up ℤ)).obj P) =
      (rationalPullDerived l F g aF.rationalCoefficient).map
          (pbcComplexCounit (rationalBalancedCoefficient l E F i Y) P) ≫
        rationalPullComplexCounit l F g aF.rationalCoefficient
          (((pbcExtend (rationalBalancedCoefficient l E F i Y)).mapHomologicalComplex (.up ℤ)).obj
      P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
  /-- The raw comparison, given by `rationalScalarStrictBeta`. -/
  beta : aE.rawPull ⋙ pbcRationalScalarExtension l E F i X Fact.out Fact.out ≅
    pbcRationalScalarExtension l E F i Y Fact.out Fact.out ⋙ aF.rawPull
  /-- All components, not just their endpoint isomorphism classes, are fixed. -/
  beta_normalization : ∀ K : PbcRationalDerivedCategory l E Y Fact.out Fact.out,
    beta.app K = rationalMixedBetaComponent l E F i g sXE sYE sXF sYF aE aF K
  /-- The mixed realization square commutes on every raw rational object. -/
  compatibility : ∀ K : PbcRationalDerivedCategory l E Y Fact.out Fact.out,
    (rationalBalancedTheta l E F i X sXE sXF).hom.app (aE.rawPull.obj K) ≫
        (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
          (aE.alpha.hom.app K) ≫ zeta.hom.app (sYE.J.obj K) =
      sXF.J.map (beta.hom.app K) ≫
        aF.alpha.hom.app
          ((pbcRationalScalarExtension l E F i Y Fact.out Fact.out).obj K) ≫
        (rationalPullDerived l F g aF.rationalCoefficient).map
          ((rationalBalancedTheta l E F i Y sYE sYF).hom.app K)

variable (g : X ⟶ Y)
  (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
  (sXF : RationalModuleRealization l F X) (sYF : RationalModuleRealization l F Y)
  (aE : RationalRealizationPullbackComparison l E g sXE sYE)
  (aF : RationalRealizationPullbackComparison l F g sXF sYF)

/-- The mixed equation uses exactly the owning dependencies' theta, D, strict beta and alpha. -/
theorem rationalScalarMixedUnitCancellation :
    Nonempty (RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF) := by
  sorry

section GeometricHelpers
variable {Z : Scheme.{u}} [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]
variable (h : Z ⟶ X) (sZE : RationalModuleRealization l E Z)
  (ahE : RationalRealizationPullbackComparison l E h sZE sXE)
  (acE : RationalRealizationPullbackComparison l E (h ≫ g) sZE sYE)

/-- The ambient compositor extracted from the full normalized dependency theorem.
Its tensor-generator, inverse-image-pasting, computation-counit and strict-unit equations
fix its maps; this does not select from an unnormalized endpoint-isomorphism existence. -/
def rationalMixedGeometricCompositor :
    rationalPullDerived l E g aE.rationalCoefficient ⋙
      rationalPullDerived l E h ahE.rationalCoefficient ≅
    rationalPullDerived l E (h ≫ g) acE.rationalCoefficient := by
  have hc := rationalPullbackCompositionCoherence l E g h sYE sXE sZE aE ahE acE
  unfold HasRationalPullbackCompositionCoherence at hc
  exact hc.2.2.2.2.choose_spec.2.choose

end GeometricHelpers

section IdentityHelpers
variable (a : RationalRealizationPullbackComparison l E (𝟙 X) sXE sXE)

end IdentityHelpers

section GeometricCoherence
variable {Z : Scheme.{u}} [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]
variable (h : Z ⟶ X) (sZE : RationalModuleRealization l E Z)
  (sZF : RationalModuleRealization l F Z)
  (ahE : RationalRealizationPullbackComparison l E h sZE sXE)
  (acE : RationalRealizationPullbackComparison l E (h ≫ g) sZE sYE)
  (ahF : RationalRealizationPullbackComparison l F h sZF sXF)
  (acF : RationalRealizationPullbackComparison l F (h ≫ g) sZF sYF)
  (mg : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
  (mh : RationalScalarMixedUnitCancellation l E F i h sZE sXE sZF sXF ahE ahF)
  (mc : RationalScalarMixedUnitCancellation l E F i (h ≫ g) sZE sYE sZF sYF acE acF)

/-- The same zeta comparisons commute with geometric composition. -/
theorem rationalMixedGeometricComposition
    (K : DerivedCategory (pbcModules Y (rationalCoefficientSheaf l Y E))) :
    mh.zeta.hom.app ((rationalPullDerived l E g aE.rationalCoefficient).obj K) ≫
        (rationalPullDerived l F h ahF.rationalCoefficient).map (mg.zeta.hom.app K) =
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i Z)).map
          ((rationalMixedGeometricCompositor l E g sXE sYE aE h sZE ahE acE).hom.app K) ≫
        mc.zeta.hom.app K ≫
        (rationalMixedGeometricCompositor l F g sXF sYF aF h sZF ahF acF).inv.app
          ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj K) := by
  sorry

end GeometricCoherence

section CoefficientCoherence
variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)
  (sXG : RationalModuleRealization l G X) (sYG : RationalModuleRealization l G Y)
  (aG : RationalRealizationPullbackComparison l G g sXG sYG)
  (mEF : RationalScalarMixedUnitCancellation l E F i g sXE sYE sXF sYF aE aF)
  (mFG : RationalScalarMixedUnitCancellation l F G j g sXF sYF sXG sYG aF aG)
  (mEG : RationalScalarMixedUnitCancellation l E G (j.comp i) g
    sXE sYE sXG sYG aE aG)

/-- The same zeta comparisons respect the specified coefficient associators. -/
theorem rationalMixedCoefficientTower
    (K : DerivedCategory (pbcModules Y (rationalCoefficientSheaf l Y E))) :
    (pbcDerivedExtend (rationalBalancedCoefficient l F G j X)).map (mEF.zeta.hom.app K) ≫
      mFG.zeta.hom.app ((pbcDerivedExtend (rationalBalancedCoefficient l E F i Y)).obj K) ≫
      (rationalPullDerived l G g aG.rationalCoefficient).map
        ((pbcReductionNormalization (rationalBalancedCoefficient l E F i Y)
          (rationalBalancedCoefficient l F G j Y)
          (rationalBalancedCoefficient l E G (j.comp i) Y)
          (rationalBalancedCoefficient_comp l E F i Y G j) K).hom) =
    (pbcReductionNormalization (rationalBalancedCoefficient l E F i X)
      (rationalBalancedCoefficient l F G j X)
      (rationalBalancedCoefficient l E G (j.comp i) X)
      (rationalBalancedCoefficient_comp l E F i X G j)
      ((rationalPullDerived l E g aE.rationalCoefficient).obj K)).hom ≫
        mEG.zeta.hom.app K := by
  sorry

end CoefficientCoherence

section Pentagon
variable (G H : Type u) [Field G] [Field H]
  [Algebra ℚ_[l] G] [Algebra ℚ_[l] H]
  [FiniteDimensional ℚ_[l] G] [FiniteDimensional ℚ_[l] H]
  (j : F →ₐ[ℚ_[l]] G) (k : G →ₐ[ℚ_[l]] H)
  (sXH : RationalModuleRealization l H X) (sYH : RationalModuleRealization l H Y)
  (aH : RationalRealizationPullbackComparison l H g sXH sYH)
  (mEH : RationalScalarMixedUnitCancellation l E H (k.comp (j.comp i)) g
    sXE sYE sXH sYH aE aH)

end Pentagon

end AlgebraicGeometry.Scheme
