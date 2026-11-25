/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import WeilConjectures.AlgebraicGeometry.Rational.RationalScalarBalancedLocalization
import WeilConjectures.AlgebraicGeometry.Rational.RationalPullbackCompositionCoherence
import WeilConjectures.AlgebraicGeometry.Rational.RationalScalarMixedUnitCancellation
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalAdjunctionUnit
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import WeilConjectures.AlgebraicGeometry.Rational.RationalPullbackFlatComputationCounit

/-!
# Finite coefficient extension and mixed rational-realization coherence

The comparisons use the actual raw rationalizations, coefficient inclusions and
strict quotient-tower units. The scalar, tower and mixed records retain the
normalizations that specify the comparisons, rather than just their isomorphism classes.

## References

* Bhatt--Scholze, Lemma 6.8.2, Proposition 6.8.14 and Remark 6.8.15
* Stacks Tags 0G7E, 0D6D, 0A0E and 0A0G
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

attribute [local irreducible] HasDerivedCategory.standard
  Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
variable (i : E →ₐ[ℚ_[l]] F)
variable (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- Finite-extension balancing with its actual continuous and completed coefficient maps.
The component equation is the identification through `F_X ⊗^L_{B_E,X} K`.
The existing `pbcReductionNormalization` is the adjunction-normalized flattening
on K-flat representatives, with inverse inserting one. -/
structure RationalRealizationScalarComparison
    (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X) where
  /-- Postcomposition of continuous functions by the field inclusion. -/
  coefficient : rationalCoefficientSheaf l X E ⟶ rationalCoefficientSheaf l X F
  /-- This equation specifies that postcomposition on all sections. -/
  coefficient_normalization : ∀ (U : X.ProEtᵒᵖ)
      (b : (rationalCoefficientSheaf l X E).obj.obj U) (x : U.unop.left),
    rationalCoefficientValue l F X U (coefficient.hom.app U b) x =
      i (rationalCoefficientValue l E X U b x)
  /-- The integral inclusion is the recorded finite-quotient-normalized inclusion. -/
  coefficient_square : pbcScalarCoefficientMap l E F i X ≫ rationalPullScalar l F sF =
    rationalPullScalar l E sE ≫ coefficient
  /-- The required isomorphism, natural on every raw fraction morphism. -/
  theta : pbcRationalScalarExtension l E F i X Fact.out Fact.out ⋙ sF.J ≅
    sE.J ⋙ pbcDerivedExtend coefficient
  /-- Both routes flatten to the same actual single derived tensor on an integral object. -/
  integral_normalization : ∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
    theta.hom.app ((pbcRationalization X (pbcIntegralDatum l E)
        (pbcUniformizer l E)).obj K) ≫
      (pbcDerivedExtend coefficient).map (eqToHom (sE.objects K)) ≫
      (pbcReductionNormalization (rationalPullScalar l E sE) coefficient
        (rationalPullScalar l E sE ≫ coefficient) rfl K.obj).hom =
    eqToHom (sF.objects
        ((pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj K)) ≫
      (pbcReductionNormalization (pbcScalarCoefficientMap l E F i X)
        (rationalPullScalar l F sF) (rationalPullScalar l E sE ≫ coefficient)
        coefficient_square K.obj).hom

private theorem rationalScalarCoefficient_eq
    (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X)
    (b : RationalRealizationScalarComparison l E F i X sE sF) :
    b.coefficient = rationalBalancedCoefficient l E F i X := by
  let := coefficientExtensionNormedField l F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  ext a : 1
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  change rationalCoefficientValue l F X U (b.coefficient.hom.app U a) x =
    rationalCoefficientValue l F X U
      ((rationalBalancedCoefficient l E F i X).hom.app U a) x
  rw [b.coefficient_normalization, (rationalBalancedCoefficient_sections l E F i X).1]

private theorem rationalScalarComparison_unique
    (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X)
    (b₁ b₂ : RationalRealizationScalarComparison l E F i X sE sF) : b₁ = b₂ := by
  have hc := (rationalScalarCoefficient_eq l E F i X sE sF b₁).trans
    (rationalScalarCoefficient_eq l E F i X sE sF b₂).symm
  cases b₁ with
  | mk c₁ cn₁ cs₁ t₁ n₁ =>
    cases b₂ with
    | mk c₂ cn₂ cs₂ t₂ n₂ =>
      dsimp only at hc
      subst c₂
      have ht : t₁ = t₂ := by
        apply Iso.ext
        apply NatTrans.ext
        funext K
        cases K with
        | mk K =>
          change t₁.hom.app
              ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
            t₂.hom.app
              ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K)
          apply (cancel_mono
            ((pbcDerivedExtend c₁).map (eqToHom (sE.objects K)) ≫
              (pbcReductionNormalization (rationalPullScalar l E sE) c₁
                (rationalPullScalar l E sE ≫ c₁) rfl K.obj).hom)).1
          simpa only [Category.assoc] using (n₁ K).trans (n₂ K).symm
      subst t₂
      rfl

private def rationalScalarCanonical
    (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X) :
    RationalRealizationScalarComparison l E F i X sE sF := by
  refine {
    coefficient := rationalBalancedCoefficient l E F i X
    coefficient_normalization := (rationalBalancedCoefficient_sections l E F i X).1
    coefficient_square := rationalBalancedCoefficient_square l E F i X sE sF
    theta := rationalBalancedTheta l E F i X sE sF
    integral_normalization := ?_ }
  intro K
  simp only [rationalBalancedTheta, NatIso.ofComponents_hom_app,
    rationalBalancedComponent, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    eqToIso.hom, eqToIso.inv, rationalBalancedS, rationalBalancedT]
  simp only [Category.assoc]
  change eqToHom (sF.objects
      ((pbcEmbeddingIntegralTensor l E F i X Fact.out Fact.out).obj K)) ≫
      (rationalBalancedS l E F i X sE sF K.obj).hom ≫
      (rationalBalancedT l E F i X sE K.obj).inv ≫
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
        (eqToHom (sE.objects K).symm) ≫
      (pbcDerivedExtend (rationalBalancedCoefficient l E F i X)).map
        (eqToHom (sE.objects K)) ≫
      (rationalBalancedT l E F i X sE K.obj).hom = _
  rw [← Functor.map_comp_assoc, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  rfl

variable {X}
variable {Y : Scheme.{u}} [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
variable (j : F →ₐ[ℚ_[l]] G)

/-- The successive-extension diagram with exactly the raw tensor associators. -/
structure RationalRealizationScalarTower
    (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X)
    (sG : RationalModuleRealization l G X)
    (bEF : RationalRealizationScalarComparison l E F i X sE sF)
    (bFG : RationalRealizationScalarComparison l F G j X sF sG)
    (bEG : RationalRealizationScalarComparison l E G (j.comp i) X sE sG) : Prop where
  /-- The continuous coefficient maps compose as the field inclusions. -/
  coefficient : bEF.coefficient ≫ bFG.coefficient = bEG.coefficient
  /-- Flattening the two scalar factors agrees with direct extension. -/
  compatibility : ∀ K,
    sG.J.map ((pbcRationalScalarComp l E F G i j X Fact.out Fact.out).hom.app K) ≫
        bEG.theta.hom.app K =
      bFG.theta.hom.app
          ((pbcRationalScalarExtension l E F i X Fact.out Fact.out).obj K) ≫
        (pbcDerivedExtend bFG.coefficient).map (bEF.theta.hom.app K) ≫
        (pbcReductionNormalization bEF.coefficient bFG.coefficient bEG.coefficient
          coefficient (sE.J.obj K)).hom

/-- The successive-extension comparison is coherent, including repeated fields. -/
theorem rationalRealizationScalarTower
    (sE : RationalModuleRealization l E X) (sF : RationalModuleRealization l F X)
    (sG : RationalModuleRealization l G X)
    (bEF : RationalRealizationScalarComparison l E F i X sE sF)
    (bFG : RationalRealizationScalarComparison l F G j X sF sG)
    (bEG : RationalRealizationScalarComparison l E G (j.comp i) X sE sG) :
    RationalRealizationScalarTower l E F i G j sE sF sG bEF bFG bEG := by
  rw [rationalScalarComparison_unique l E F i X sE sF bEF
    (rationalScalarCanonical l E F i X sE sF),
    rationalScalarComparison_unique l F G j X sF sG bFG
      (rationalScalarCanonical l F G j X sF sG),
    rationalScalarComparison_unique l E G (j.comp i) X sE sG bEG
      (rationalScalarCanonical l E G (j.comp i) X sE sG)]
  exact ⟨rationalBalancedCoefficient_comp l E F i X G j,
    rationalBalancedTower l E F i X sE sF G j sG⟩

/-- Tensor multiplication is the identity-field comparison, on ordinary modules,
complexes, derived objects and raw rationalizations. -/
structure RationalRealizationScalarUnit (s : RationalModuleRealization l E X)
    (b : RationalRealizationScalarComparison l E E (AlgHom.id ℚ_[l] E) X s s) where
  /-- Identity field inclusion induces the identity continuous coefficient map. -/
  coefficient : b.coefficient = 𝟙 _
  /-- The ordinary multiplication unitor. -/
  ordinary : pbcExtend b.coefficient ≅ 𝟭 _
  /-- It multiplies the coefficient into the module section. -/
  sections : ∀ (M : pbcModules X (rationalCoefficientSheaf l X E))
      (U : X.ProEtᵒᵖ) (a : (rationalCoefficientSheaf l X E).obj.obj U) (m : M.val.obj U),
    (ordinary.hom.app M).val.app U (pbcTensorSection b.coefficient M U a m) = a • m
  /-- The corresponding derived unitor. -/
  ambient : pbcDerivedExtend b.coefficient ≅ 𝟭 _
  /-- Its computation is that ordinary multiplication, degree by degree. -/
  normalization : ∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
    ambient.hom.app (DerivedCategory.Q.obj P) =
      pbcComplexCounit b.coefficient P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
  /-- Theta for the identity is exactly the specified raw tensor unitor. -/
  compatibility : ∀ K,
    b.theta.hom.app K ≫ ambient.hom.app (s.J.obj K) =
      s.J.map ((pbcRationalScalarUnit l E X Fact.out Fact.out).hom.app K)

/-- Identity coefficients give the multiplication unitors. -/
theorem rationalRealizationScalarUnit (s : RationalModuleRealization l E X)
    (b : RationalRealizationScalarComparison l E E (AlgHom.id ℚ_[l] E) X s s) :
    Nonempty (RationalRealizationScalarUnit l E s b) := by
  rw [rationalScalarComparison_unique l E E (AlgHom.id ℚ_[l] E) X s s b
    (rationalScalarCanonical l E E (AlgHom.id ℚ_[l] E) X s s)]
  obtain ⟨hc, o, d, hs, hn, ht⟩ := rationalBalancedIdentity l E X s
  exact ⟨⟨hc, o, hs, d, hn, ht⟩⟩

private def rationalScalarNormalizationIso {T : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c) :
    pbcDerivedExtend a ⋙ pbcDerivedExtend b ≅ pbcDerivedExtend c :=
  Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
    (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction c)
    (pbcDerivedRestrictComp a b c h)

private theorem rationalScalarNormalizationIso_hom {T : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c)
    (K : DerivedCategory (pbcModules T R)) :
    (rationalScalarNormalizationIso a b c h).hom.app K =
      (pbcReductionNormalization a b c h K).hom := by
  dsimp only [rationalScalarNormalizationIso, pbcReductionNormalization, asIso_hom,
    pbcReductionNormalizationHom, pbcReductionTransition]
  simp only [Adjunction.leftAdjointCompIso_hom_app, Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc]

variable {Z : Scheme.{u}} [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]

end AlgebraicGeometry.Scheme
