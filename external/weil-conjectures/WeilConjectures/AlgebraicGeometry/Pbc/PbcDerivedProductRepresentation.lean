/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Products of evaluated strict towers

## References

* Stacks 07KC
* Stacks 015F
* Stacks 05RU
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) {A : Type u} [CommRing A]

/-- Evaluation of a tower complex as a tower of complexes, then localization at each level. -/
def pbcComplexEvaluation (d : Scheme.AdicCoefficientDatum A) :
    CochainComplex (Scheme.CompletedAdicTowers T d) ℤ ⥤ (ℕᵒᵖ ⥤
    DerivedCategory (Scheme.CompletedAdicModules T d)) :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (Functor.whiskeringRight ℕᵒᵖ (CochainComplex (Scheme.CompletedAdicModules T d) ℤ)
      (DerivedCategory (Scheme.CompletedAdicModules T d))).obj DerivedCategory.Q

/-- Evaluation is exact levelwise, so this functor inverts tower quasi-isomorphisms. -/
theorem pbcComplexEvaluation_inverts (d : Scheme.AdicCoefficientDatum A) :
    (HomologicalComplex.quasiIso (Scheme.CompletedAdicTowers T d) (ComplexShape.up ℤ)).IsInvertedBy
      (pbcComplexEvaluation T d) := by
  let : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  intro C D f hf
  have : QuasiIso f := hf
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro n
  change IsIso (DerivedCategory.Q.map
    ((((evaluation ℕᵒᵖ (Scheme.CompletedAdicModules T d)).obj n).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f))
  infer_instance

/-- The canonical evaluated derived tower, obtained by the localization universal property. -/
def pbcDerivedEvaluation (d : Scheme.AdicCoefficientDatum A) :
    DerivedCategory (Scheme.CompletedAdicTowers T d) ⥤ (ℕᵒᵖ ⥤
    DerivedCategory (Scheme.CompletedAdicModules T d)) :=
  Localization.lift (pbcComplexEvaluation T d) (pbcComplexEvaluation_inverts T d)
    DerivedCategory.Q

/-- The localization comparison, so evaluation retains the representative's transition maps. -/
def pbcEvaluationFactors (d : Scheme.AdicCoefficientDatum A) :
    DerivedCategory.Q ⋙ pbcDerivedEvaluation T d ≅ pbcComplexEvaluation T d :=
  Localization.fac _ (pbcComplexEvaluation_inverts T d) DerivedCategory.Q

/-- The product fan supplied by a representative tower complex. Its projections are
localized complex projections followed by the specified representative isomorphism. -/
def pbcRepresentativeProductFan (d : Scheme.AdicCoefficientDatum A)
    (M : DerivedCategory (Scheme.CompletedAdicTowers T d))
    (I : CochainComplex (Scheme.CompletedAdicTowers T d) ℤ)
    (e : DerivedCategory.Q.obj I ≅ M) :
    Fan (fun n : ℕ ↦ ((pbcDerivedEvaluation T d).obj M).obj (op n)) :=
  Fan.mk (DerivedCategory.Q.obj (∏ᶜ fun n : ℕ ↦ I.asFunctor.obj (op n))) (fun n ↦
    DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ I.asFunctor.obj (op n)) n) ≫
      ((pbcEvaluationFactors T d).inv.app I).app (op n) ≫
      ((pbcDerivedEvaluation T d).map e.hom).app (op n))

/-- Countable products in the completed-coefficient derived category exist, and every
K-injective tower resolution represents their product by its termwise product.
A resolution C → I and a representative Q(C) ≅ M supply e by inverting Q(C → I). -/
theorem pbcDerivedProductRepresentation (d : Scheme.AdicCoefficientDatum A) :
    HasCountableProducts (DerivedCategory (Scheme.CompletedAdicModules T d)) ∧
    ∀ (M : DerivedCategory (Scheme.CompletedAdicTowers T d))
      (I : CochainComplex (Scheme.CompletedAdicTowers T d) ℤ)
      (_hI : I.IsKInjective) (e : DerivedCategory.Q.obj I ≅ M),
      Nonempty (IsLimit (pbcRepresentativeProductFan T d M I e)) := by
  let : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  have : HasFiniteBiproducts (Scheme.CompletedAdicModules T d) :=
    Abelian.hasFiniteBiproducts
  have : CountableAB4Star (Scheme.CompletedAdicModules T d) := by
    have : (lim (J := Discrete ℕ)
        (C := Scheme.CompletedAdicModules T d)).PreservesEpimorphisms :=
      { preserves := by
          intro F G f hf
          have h := (Scheme.ProEt.countableProducts_exact.{u, u, 0} T
            (Scheme.completedAdicCommRing T d)).2.2
            ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
            (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
          have he : lim.map f = (Pi.isoLimit _).inv ≫
              Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
            apply limit.hom_ext
            intro ⟨n⟩
            simp
          rw [he]
          infer_instance }
    have := hasExactLimitsOfShape_of_preservesEpi
      (Scheme.CompletedAdicModules T d) (Discrete ℕ)
    exact CountableAB4Star.of_hasExactLimitsOfShape_nat _
  obtain ⟨hP, hprops⟩ := derivedCategory_countableProducts_core.{0, u + 2, u + 1, u + 2}
    (Scheme.CompletedAdicModules T d)
  refine ⟨hP, ?_⟩
  intro M I hI e
  let C : ℕ → CochainComplex (Scheme.CompletedAdicModules T d) ℤ :=
    fun n ↦ I.asFunctor.obj (op n)
  let hc := (Fan.isLimitMapConeEquiv DerivedCategory.Q C
    (limit.cone (Discrete.functor C))) (hprops.1 ℕ C).some
  let α : Discrete.functor (fun n ↦ DerivedCategory.Q.obj (C n)) ≅
      Discrete.functor (fun n : ℕ ↦ ((pbcDerivedEvaluation T d).obj M).obj (op n)) :=
    Discrete.natIso (fun n ↦
      ((pbcEvaluationFactors T d).symm.app I).app (op n.as) ≪≫
        ((pbcDerivedEvaluation T d).mapIso e).app (op n.as))
  let hc' := (IsLimit.postcomposeHomEquiv α _).symm hc
  refine ⟨IsLimit.ofIsoLimit hc' (Fan.ext (Iso.refl _) ?_)⟩
  intro n
  dsimp [α, pbcRepresentativeProductFan, Fan.proj, Cone.postcompose]
  simp only [Category.id_comp, Discrete.natIso_hom_app]
  rfl

/-- The countable-product existence part of the representation statement. -/
instance pbcDerived_hasCountableProducts (d : Scheme.AdicCoefficientDatum A) :
    HasCountableProducts (DerivedCategory (Scheme.CompletedAdicModules T d)) :=
  (pbcDerivedProductRepresentation T d).1

end AlgebraicGeometry.ProEtale
