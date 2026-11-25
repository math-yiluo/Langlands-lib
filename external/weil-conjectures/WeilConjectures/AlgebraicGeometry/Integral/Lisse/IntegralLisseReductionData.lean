/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSized
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Integral lisse modules and their normalized reduction towers

The finite coefficient sheaves are first presented as continuous functions into the quotient
rings, with their quotient topology. The statement identifies these with constant sheaves.
Towers are written in the integral module category by restriction of scalars. Normalization
is the cokernel universal property for multiplication by the relevant power of the uniformizer;
this is precisely the induced sheaf tensor quotient, not invertibility of the transition itself.

## References

* Bhatt--Scholze, Lemma 6.8.2, Definition 6.8.3 and Proposition 6.8.4(1), pp. 58--59
* Bhatt--Scholze, Definition 6.8.1
* Bhatt--Scholze, Lemma 6.8.2(1)
* Bhatt--Scholze, Proposition 6.8.4(1)
* Stacks, Tag 03EK
* Bhatt--Scholze, Definition 6.8.3
* Bhatt--Scholze, Definition 6.8.3 and Proposition 6.8.4(1)
* Bhatt--Scholze, Lemma 6.8.2
* Bhatt--Scholze, Lemma 6.8.2(2)
* Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.4(1)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The integral module ring, forgetting only commutativity. -/
abbrev integralLisseRing : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} :=
  (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseIntegerSheafSized l E X)

/-- Positive finite coefficient levels; index `n` denotes exponent `n+1`. -/
def integralLisseFiniteRing (n : ℕ) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  lisseContinuousCommRingSheafSized X (Padic.coefficientExtensionRing l E (n + 1))

/-- The pointwise quotient map to finite coefficients, with its quotient topology. -/
def integralLisseReduction (n : ℕ) :
    lisseIntegerSheafSized l E X ⟶ integralLisseFiniteRing l E X n :=
  letI := spectralNorm.normedField ℚ_[l] E
  ⟨{ app := fun _ ↦ CommRingCat.ofHom
       (ULift.ringEquiv.symm.toRingHom.comp
         (((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).compLeftContinuous
           _ continuous_quot_mk).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The constant residue section in the quotient topology. -/
def integralLisseFiniteConstant (n : ℕ) (U : X.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionRing l E (n + 1)) :
    (integralLisseFiniteRing l E X n).obj.obj U :=
  letI := spectralNorm.normedField ℚ_[l] E
  ULift.up (ContinuousMap.const U.unop.left a)

/-- Adjacent reduction of continuous finite coefficients. -/
def integralLisseFiniteTransition (n : ℕ) :
    integralLisseFiniteRing l E X (n + 1) ⟶ integralLisseFiniteRing l E X n :=
  letI := spectralNorm.normedField ℚ_[l] E
  ⟨{ app := fun _ ↦ CommRingCat.ofHom
       (ULift.ringEquiv.symm.toRingHom.comp
         (((Padic.coefficientExtensionTransition l E (n + 1)).compLeftContinuous _
           ((QuotientRing.isOpenQuotientMap_mk
             (Padic.coefficientExtensionIdeal l E (n + 2))).isQuotientMap.continuous_iff.mpr
               continuous_quot_mk)).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The finite coefficient diagram, with all positive powers represented. -/
def integralLisseFiniteDiagram :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  Functor.ofOpSequence (integralLisseFiniteTransition l E X)

/-- Restrict scalars along the actual pointwise coefficient reduction. -/
def integralLisseFiniteRestriction (n : ℕ) :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (integralLisseReduction l E X n))

/-- Multiplication by a constant integral section on a module sheaf. -/
def integralLisseScalar (M : ringedSiteModules.{u + 1} (integralLisseRing l E X))
    (a : Padic.coefficientExtensionIntegers l E) : M ⟶ M :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom
       { toFun := fun x ↦ lisseIntegerConstantSized l E X U a • x
         map_add' := smul_add _
         map_smul' := fun r x ↦ by
           change _ • (r • x) = r • (_ • x)
           rw [smul_smul, smul_smul]
           exact congrArg (fun c : (lisseIntegerSheafSized l E X).obj.obj U ↦ c • x)
             (mul_comm _ _) }
     naturality := fun {U V} f ↦ by
       ext x
       exact (M.val.map_smul f (lisseIntegerConstantSized l E X U a) x).symm }⟩

/-- Quotient by a scalar, specified by its sheaf cokernel universal property. -/
def IsIntegralLisseQuotient {M N : ringedSiteModules.{u + 1} (integralLisseRing l E X)}
    (a : Padic.coefficientExtensionIntegers l E) (q : M ⟶ N) : Prop :=
  ∃ h : integralLisseScalar l E X M a ≫ q = 0,
    Nonempty (IsColimit (CokernelCofork.ofπ q h))

/-- Integral lisse objects form the full subcategory with locally varying finite rank. -/
abbrev IntegralLisseModule :=
  (SheafOfModules.isFiniteLocallyFree (integralLisseRing l E X)).FullSubcategory

/-- The normalized tower property in the integral module category. Each level is the
restriction of an actual finite locally free finite-coefficient module. Normalization says
that its transition is the quotient by the appropriate scalar, equivalently that the induced
sheaf tensor map is invertible. -/
def IsIntegralReductionTower
    (F : ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (integralLisseRing l E X)) : Prop :=
  (∀ n : ℕ, ∃ N : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (integralLisseFiniteRing l E X n)),
    N.IsFiniteLocallyFree ∧
      Nonempty ((integralLisseFiniteRestriction l E X n).obj N ≅ F.obj (op n))) ∧
  ∀ n : ℕ, IsIntegralLisseQuotient l E X
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1))
    (F.map (homOfLE (Nat.le_succ n)).op)

/-- Normalized towers, with compatible families of module maps as morphisms. -/
abbrev IntegralReductionTower :=
  ObjectProperty.FullSubcategory (IsIntegralReductionTower l E X)

/-- The ring unit mapped along a ring-sheaf homomorphism, regarded as an integral-linear map. -/
def integralLisseRingMap {S : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}}
    (f : integralLisseRing l E X ⟶ S) :
    SheafOfModules.unit (integralLisseRing l E X) ⟶
      (SheafOfModules.restrictScalars f).obj (SheafOfModules.unit S) :=
  SheafOfModules.unitHomEquiv _ |>.symm
    ⟨fun U ↦ (1 : S.obj.obj U), fun {_U _V} g ↦ (S.obj.map g).hom.map_one⟩

/-- The fraction map at the `n`th stage of localization by `l`. -/
def integralLisseFraction (n : ℕ) :
    SheafOfModules.unit (integralLisseRing l E X) ⟶
      (SheafOfModules.restrictScalars
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (lisseIntegerToFieldSized l E X))).obj
        (SheafOfModules.unit ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (lisseFieldSheafSized l E X))) :=
  SheafOfModules.unitHomEquiv _ |>.symm
    ⟨fun U ↦ lisseFieldConstantSized l E X U ((l : E)⁻¹ ^ n), fun _ ↦ rfl⟩

/-- All the coefficient identifications and the canonical reduction equivalence.
Quotient and limit universal properties fix both functors and the displayed unit/counit maps.
The two naturality equations quantify over all module and tower morphisms, at every level. -/
structure IntegralLisseReductionEquivalence where
  finiteConstant : ∀ n : ℕ,
    (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
      (CommRingCat.of (Padic.coefficientExtensionRing l E (n + 1))) ≅
        integralLisseFiniteRing l E X n
  finiteConstant_sections : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (a : Padic.coefficientExtensionRing l E (n + 1)),
    ((finiteConstant n).hom.hom.app U)
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (Padic.coefficientExtensionRing l E (n + 1))))).app U a) =
      integralLisseFiniteConstant l E X n U a
  coefficientCone : (Functor.const ℕᵒᵖ).obj (lisseIntegerSheafSized l E X) ⟶
    integralLisseFiniteDiagram l E X
  coefficientCone_app : ∀ n : ℕ, coefficientCone.app (op n) = integralLisseReduction l E X n
  coefficientLimit : IsLimit (Cone.mk _ coefficientCone)
  coefficientQuotient : ∀ n : ℕ, IsIntegralLisseQuotient l E X
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1))
    (integralLisseRingMap l E X
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (integralLisseReduction l E X n)))
  localizationCocone : Cocone (Functor.ofSequence (fun _ : ℕ ↦
    integralLisseScalar l E X (SheafOfModules.unit (integralLisseRing l E X))
      (l : Padic.coefficientExtensionIntegers l E)))
  localizationPoint : localizationCocone.pt ≅
    (SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (lisseIntegerToFieldSized l E X))).obj
      (SheafOfModules.unit ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (lisseFieldSheafSized l E X)))
  localization_app : ∀ n : ℕ,
    localizationCocone.ι.app n ≫ localizationPoint.hom = integralLisseFraction l E X n
  localizationColimit : IsColimit localizationCocone
  equivalence : IntegralLisseModule l E X ≌ IntegralReductionTower l E X
  reduction : ∀ M : IntegralLisseModule l E X,
    (Functor.const ℕᵒᵖ).obj M.obj ⟶ (equivalence.functor.obj M).obj
  reductionQuotient : ∀ (M : IntegralLisseModule l E X) (n : ℕ),
    IsIntegralLisseQuotient l E X (Padic.coefficientExtensionUniformizer l E ^ (n + 1))
      ((reduction M).app (op n))
  reduction_natural : ∀ {M N : IntegralLisseModule l E X} (f : M ⟶ N) (n : ℕ),
    f.hom ≫ (reduction N).app (op n) =
      (reduction M).app (op n) ≫ (equivalence.functor.map f).hom.app (op n)
  completion : ∀ F : IntegralReductionTower l E X,
    (Functor.const ℕᵒᵖ).obj (equivalence.inverse.obj F).obj ⟶ F.obj
  completionLimit : ∀ F : IntegralReductionTower l E X,
    IsLimit (Cone.mk _ (completion F))
  completion_natural : ∀ {F G : IntegralReductionTower l E X} (f : F ⟶ G) (n : ℕ),
    (equivalence.inverse.map f).hom ≫ (completion G).app (op n) =
      (completion F).app (op n) ≫ f.hom.app (op n)
  unit_projection : ∀ (M : IntegralLisseModule l E X) (n : ℕ),
    (equivalence.unitIso.hom.app M).hom ≫
      (completion (equivalence.functor.obj M)).app (op n) = (reduction M).app (op n)
  counit_projection : ∀ (F : IntegralReductionTower l E X) (n : ℕ),
    (reduction (equivalence.inverse.obj F)).app (op n) ≫
      (equivalence.counitIso.hom.app F).hom.app (op n) = (completion F).app (op n)

end AlgebraicGeometry.ProEtale
