/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModelOpenClosedPieces
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientImmersionRestriction
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Explicit stratum integral-model constructions

## References

* Bhatt--Scholze, Definitions 6.8.6 and 6.8.10, Proposition 6.8.11(3), Lemma 6.8.13 and Proposition
  6.8.14(2), pp. 60--62
* Bhatt--Scholze, Lemma 6.8.13
* Stacks Tag 03EK
* Bhatt--Scholze, Lemma 6.8.2
* Bhatt--Scholze, Lemma 6.8.2(1)
* Bhatt--Scholze, Proposition 6.8.11(3)
* Bhatt--Scholze, Lemmas 6.8.2(2) and 6.8.13
* Stacks Tags 03DI and 03DJ
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale.RationalStratum

/-- The actual closed direct image followed by open extension by zero. -/
def piece {X S : Scheme.{u}} (U : X.ProEt) (t : S ⟶ U.left)
    (A : Type u) [TopologicalSpace A] [CommRing A] [IsTopologicalRing A] :=
  continuousModuleDirectImage t A ⋙ continuousModuleExtensionByZero U A

open Classical in
/-- The generator indexed by a factorization through the open, followed by the actual
module-sheafification unit. Closed direct image evaluates on the base change. -/
def generator {X S : Scheme.{u}} (U : X.ProEt) (t : S ⟶ U.left)
    (A : Type u) [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    (N : SheafOfModules.{u + 1} (latticeModuleRing S A))
    (W : X.ProEt) (φ : W ⟶ U)
    (s : N.val.obj (op ((Scheme.proEtaleBaseChange t).obj
      ((Scheme.ProEt.sliceTo X U).obj (Over.mk φ))))) :
    ((piece U t A).obj N).val.obj (op W) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (latticeModuleRing X A).obj)).unit.app
      ((SheafOfModules.extensionByZeroPresheaf (latticeModuleRing X A) U).obj
        ((openSliceModules U A).obj ((continuousModuleDirectImage t A).obj N)))).app
          (op W) (DirectSum.of _ φ s)

/-- A pure tensor in ordinary integral-to-field change of rings, followed by
sheafification. -/
def tensorSection (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (N : SheafOfModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E)))
    (W : X.ProEt) (a : WithAbs (Padic.coefficientExtensionAbsoluteValue l E))
    (s : N.val.obj (op W)) : (integralModelRationalize l E X N).val.obj (op W) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj)
      ).unit.app (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
        (integralLatticeCoefficientMap X l E) N)).app (op W)
          ((ULift.up (ContinuousMap.const W.left a)) ⊗ₜ[
            (latticeCoefficientSheaf X (latticeCoefficientIntegers l E)).obj.obj (op W),
              ((integralLatticeCoefficientMap X l E).hom.app (op W)).hom] s)

/-- The actual finite-level coefficient comparison, normalized on residue representatives. -/
def finiteComparison (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) (n : ℕ) :=
  (Scheme.pbcLevelConstantComparison X (Scheme.pbcIntegralDatum l E) n).symm ≪≫
    (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).mapIso
      (Scheme.integralCoefficientULift l E n).toCommRingCatIso ≪≫
    (Scheme.discreteContinuousCoefficientIso X).app (Scheme.finiteCoefficientRing l E n)

/-- Completed membership in degree zero, with the coefficient identification fixed by
all finite residue maps. The predicate used is the three-clause predicate,
including compatible etale origins. No completion or model is substituted for N. -/
def IsCompletedModel (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (N : SheafOfModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E))) :
    Prop :=
  ∃ b : Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E) ≅
      latticeCoefficientSheaf X (latticeCoefficientIntegers l E),
    (∀ (n : ℕ) (W : X.ProEt) (s : (latticeCoefficientSheaf X
        (latticeCoefficientIntegers l E)).obj.obj (op W)) (x : W.left),
      (Scheme.finiteContinuousCoefficientValue l E X n (op W)
        ((b.inv ≫ Scheme.pbcAdicProjection X (Scheme.pbcIntegralDatum l E) n ≫
          (finiteComparison l E X n).hom).hom.app (op W) s) x).down =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
          ⟨WithAbs.ofAbs (s.down x).val, (s.down x).property⟩) ∧
    Scheme.PbcIsBoundedConstructibleComplete X (Scheme.pbcIntegralDatum l E)
      ((DerivedCategory.singleFunctor _ 0).obj ((Scheme.pbcRestrict b.hom).obj N))

/-- The chosen uniformizer viewed in the continuous field coefficient type. -/
def uniformizer (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    WithAbs (Padic.coefficientExtensionAbsoluteValue l E) :=
  (WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E)).symm
    (Padic.coefficientExtensionUniformizer l E).val

/-- The ordinary scalar comparison is fixed on all sequential-localization fractions
of all extension-by-zero generators. The underlying closed direct-image section is
on the actual base change. The formula is precisely h/varpi^n mapped to its image
under the two exact module functors, and determines the comparison by sheafification
and the localization colimit universal property. -/
def IsNormalizedComparison (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X S : Scheme.{u}} (U : X.ProEt) (t : S ⟶ U.left)
    (N : SheafOfModules.{u + 1} (latticeModuleRing S (latticeCoefficientIntegers l E)))
    (e : integralModelRationalize l E X
        ((piece U t (latticeCoefficientIntegers l E)).obj N) ≅
      (piece U t (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj
        (integralModelRationalize l E S N)) : Prop :=
  ∀ (n : ℕ) (W : X.ProEt) (φ : W ⟶ U)
    (s : N.val.obj (op ((Scheme.proEtaleBaseChange t).obj
      ((Scheme.ProEt.sliceTo X U).obj (Over.mk φ))))),
    e.hom.val.app (op W)
      (tensorSection l E X ((piece U t (latticeCoefficientIntegers l E)).obj N) W
        ((uniformizer l E)⁻¹ ^ n) (generator U t (latticeCoefficientIntegers l E) N W φ s)) =
      generator U t (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))
        (integralModelRationalize l E S N) W φ
        (tensorSection l E S N ((Scheme.proEtaleBaseChange t).obj
          ((Scheme.ProEt.sliceTo X U).obj (Over.mk φ))) ((uniformizer l E)⁻¹ ^ n) s)

end AlgebraicGeometry.ProEtale.RationalStratum
