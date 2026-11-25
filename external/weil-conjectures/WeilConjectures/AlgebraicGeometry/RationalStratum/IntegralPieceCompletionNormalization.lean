/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalStratum.RationalStratumIntegralModelBasic
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
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
import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationModuleColimit
import WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientImmersionRestriction
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed

/-! # Completion and normalized rationalization of integral open/closed pieces

The completed-membership predicate and pure-tensor and open/closed generators are
reused from `RationalStratumIntegralModelBasic`. All comparison maps below are fixed on
fractions, including the separate open and closed maps.

## References

* Bhatt--Scholze, Lemma 6.8.2(2), Definition 6.8.10, Proposition 6.8.11(3), Lemma 6.8.13 and Remark
  6.8.15, pp. 59--62
* Bhatt--Scholze, Lemma 6.8.2(2)
* Stacks Tags 00CM, 03CY and 03EK
* Bhatt--Scholze, Lemma 6.8.2(2) and Remark 6.8.15
* Stacks Tag 03DJ
* Stacks Tag 03DI
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale.RationalStratum

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The map on ordinary rationalizations is sheafification of `1 ⊗ f`. -/
def integralPieceLocalizationMap (T : Scheme.{u})
    {H K : SheafOfModules.{u + 1} (latticeModuleRing T (latticeCoefficientIntegers l E))}
    (f : H ⟶ K) : integralModelRationalize l E T H ⟶ integralModelRationalize l E T K :=
  SheafOfModules.changeOfRingsHom (integralLatticeCoefficientMap T l E) H f

/-- The sequential localization colimit, with its transition and every leg specified
on sections. The coefficient restriction is the actual one along the integral inclusion.
The comparison to the cocone point is fixed by all fraction maps, rather than chosen
as an unspecified module isomorphism. -/
def HasNormalizedIntegralLocalization (T : Scheme.{u})
    (H : SheafOfModules.{u + 1} (latticeModuleRing T (latticeCoefficientIntegers l E))) :
    Prop :=
  ∃ (s : H ⟶ H),
    (∀ (W : T.ProEt) (h : H.val.obj (op W)),
      s.val.app (op W) h = latticeConstantCoefficient T (latticeCoefficientIntegers l E) W
        ⟨uniformizer l E, (Padic.coefficientExtensionUniformizer l E).property⟩ • h) ∧
    ∃ (c : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ H) (fun _ ↦ s)))
      (b : c.pt ≅ (SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (integralLatticeCoefficientMap T l E))).obj
            (integralModelRationalize l E T H)),
      Nonempty (IsColimit c) ∧
      ∀ (n : ℕ) (W : T.ProEt) (h : H.val.obj (op W)),
        (c.ι.app n ≫ b.hom).val.app (op W) h =
          tensorSection l E T H W ((uniformizer l E)⁻¹ ^ n) h

/-- The separate closed comparison on all localization fractions. Closed direct image
is evaluated on the actual base change. -/
def IsNormalizedClosedComparison {V S : Scheme.{u}} (t : S ⟶ V)
    (N : SheafOfModules.{u + 1} (latticeModuleRing S (latticeCoefficientIntegers l E)))
    (d : integralModelRationalize l E V
        ((continuousModuleDirectImage t (latticeCoefficientIntegers l E)).obj N) ≅
      (continuousModuleDirectImage t
        (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj
          (integralModelRationalize l E S N)) : Prop :=
  ∀ (n : ℕ) (W : V.ProEt)
    (h : N.val.obj (op ((Scheme.proEtaleBaseChange t).obj W))),
    d.hom.val.app (op W)
      (tensorSection l E V ((continuousModuleDirectImage t
        (latticeCoefficientIntegers l E)).obj N) W ((uniformizer l E)⁻¹ ^ n) h) =
      tensorSection l E S N ((Scheme.proEtaleBaseChange t).obj W)
        ((uniformizer l E)⁻¹ ^ n) h

open Classical in
/-- The separate open comparison on every fraction of each presheaf extension generator. -/
def IsNormalizedOpenComparison {X : Scheme.{u}} (U : X.ProEt)
    (P : SheafOfModules.{u + 1}
      (latticeModuleRing U.left (latticeCoefficientIntegers l E)))
    (e : integralModelRationalize l E X
        ((continuousModuleExtensionByZero U (latticeCoefficientIntegers l E)).obj P) ≅
      (continuousModuleExtensionByZero U
        (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj
          (integralModelRationalize l E U.left P)) : Prop :=
  ∀ (n : ℕ) (W : X.ProEt) (φ : W ⟶ U)
    (h : P.val.obj (op ((Scheme.ProEt.sliceTo X U).obj (Over.mk φ)))),
    e.hom.val.app (op W)
      (tensorSection l E X
        ((continuousModuleExtensionByZero U (latticeCoefficientIntegers l E)).obj P) W
        ((uniformizer l E)⁻¹ ^ n)
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (latticeModuleRing X (latticeCoefficientIntegers l E)).obj)).unit.app
            ((SheafOfModules.extensionByZeroPresheaf
              (latticeModuleRing X (latticeCoefficientIntegers l E)) U).obj
                ((openSliceModules U (latticeCoefficientIntegers l E)).obj P))).app
                  (op W) (DirectSum.of _ φ h))) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (latticeModuleRing X
          (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj)).unit.app
            ((SheafOfModules.extensionByZeroPresheaf
              (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))
                U).obj ((openSliceModules U
                  (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj
                    (integralModelRationalize l E U.left P)))).app (op W)
                      (DirectSum.of _ φ (tensorSection l E U.left P
                        ((Scheme.ProEt.sliceTo X U).obj (Over.mk φ))
                          ((uniformizer l E)⁻¹ ^ n) h))

/-- Integral open/closed pieces are constructible completed degree-zero objects, and
ordinary rationalization commutes with both operations through the fraction-normalized
comparisons. Their composite is natural and transports a specified lattice isomorphism
by the displayed composite, with the same formula on every localization leg. -/
theorem integralPieceCompletionNormalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X]
    (_hdimX : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hlX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom] [QuasiSeparated U.hom]
    [IsNoetherian U.left]
    (_hdimV : ∃ n : ℕ, topologicalKrullDim U.left ≤ n)
    (_hlV : ∀ x : U.left, IsUnit (l : U.left.presheaf.stalk x))
    {S : Scheme.{u}} [IsNoetherian S]
    (_hdimS : ∃ n : ℕ, topologicalKrullDim S ≤ n)
    (_hlS : ∀ x : S, IsUnit (l : S.presheaf.stalk x))
    (t : S ⟶ U.left) [IsClosedImmersion t]
    (_hcomp : IsCompact ((Set.range t)ᶜ)) :
    (∀ (T : Scheme.{u}), (T = S ∨ T = U.left ∨ T = X) →
      ∀ H, HasNormalizedIntegralLocalization l E T H) ∧
    (∀ (N : SheafOfModules.{u + 1}
        (latticeModuleRing S (latticeCoefficientIntegers l E))),
      IsContinuousConstructible S (latticeCoefficientIntegers l E) N →
        IsContinuousConstructible U.left (latticeCoefficientIntegers l E)
          ((continuousModuleDirectImage t (latticeCoefficientIntegers l E)).obj N) ∧
        IsContinuousConstructible X (latticeCoefficientIntegers l E)
          ((piece U t (latticeCoefficientIntegers l E)).obj N) ∧
        IsCompletedModel l E S N ∧
        IsCompletedModel l E U.left
          ((continuousModuleDirectImage t (latticeCoefficientIntegers l E)).obj N) ∧
        IsCompletedModel l E X ((piece U t (latticeCoefficientIntegers l E)).obj N)) ∧
    (∃ (d : ∀ (N : SheafOfModules.{u + 1}
          (latticeModuleRing S (latticeCoefficientIntegers l E)))
        (_hN : IsContinuousConstructible S (latticeCoefficientIntegers l E) N),
          integralModelRationalize l E U.left
            ((continuousModuleDirectImage t (latticeCoefficientIntegers l E)).obj N) ≅
          (continuousModuleDirectImage t
            (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj
              (integralModelRationalize l E S N))
      (e : ∀ (N : SheafOfModules.{u + 1}
          (latticeModuleRing S (latticeCoefficientIntegers l E)))
        (_hN : IsContinuousConstructible S (latticeCoefficientIntegers l E) N),
          integralModelRationalize l E X
            ((piece U t (latticeCoefficientIntegers l E)).obj N) ≅
          (continuousModuleExtensionByZero U
            (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj
              (integralModelRationalize l E U.left
                ((continuousModuleDirectImage t (latticeCoefficientIntegers l E)).obj N)))
      (c : ∀ (N : SheafOfModules.{u + 1}
          (latticeModuleRing S (latticeCoefficientIntegers l E)))
        (_hN : IsContinuousConstructible S (latticeCoefficientIntegers l E) N),
          integralModelRationalize l E X
            ((piece U t (latticeCoefficientIntegers l E)).obj N) ≅
          (piece U t (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj
            (integralModelRationalize l E S N)),
      (∀ N hN, IsNormalizedClosedComparison l E t N (d N hN) ∧
        IsNormalizedOpenComparison l E U
          ((continuousModuleDirectImage t (latticeCoefficientIntegers l E)).obj N) (e N hN) ∧
        (c N hN).hom = (e N hN).hom ≫
          (continuousModuleExtensionByZero U
            (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).map (d N hN).hom ∧
        IsNormalizedComparison l E U t N (c N hN) ∧
        (∀ (L : SheafOfModules.{u + 1}
            (latticeModuleRing S (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
          (α : integralModelRationalize l E S N ≅ L),
          ∃ b : integralModelRationalize l E X
              ((piece U t (latticeCoefficientIntegers l E)).obj N) ≅
            (piece U t (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj L,
            b.hom = (c N hN).hom ≫
              (piece U t (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).map α.hom ∧
            ∀ (n : ℕ) (W : X.ProEt) (φ : W ⟶ U)
              (h : N.val.obj (op ((Scheme.proEtaleBaseChange t).obj
                ((Scheme.ProEt.sliceTo X U).obj (Over.mk φ))))),
              b.hom.val.app (op W)
                (tensorSection l E X ((piece U t (latticeCoefficientIntegers l E)).obj N) W
                  ((uniformizer l E)⁻¹ ^ n)
                    (generator U t (latticeCoefficientIntegers l E) N W φ h)) =
                generator U t (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) L W φ
                  (α.hom.val.app (op ((Scheme.proEtaleBaseChange t).obj
                    ((Scheme.ProEt.sliceTo X U).obj (Over.mk φ))))
                    (tensorSection l E S N ((Scheme.proEtaleBaseChange t).obj
                      ((Scheme.ProEt.sliceTo X U).obj (Over.mk φ)))
                        ((uniformizer l E)⁻¹ ^ n) h)))) ∧
      (∀ N N' hN hN' (f : N ⟶ N'),
        integralPieceLocalizationMap l E X
            ((piece U t (latticeCoefficientIntegers l E)).map f) ≫ (c N' hN').hom =
          (c N hN).hom ≫
            (piece U t (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).map
              (integralPieceLocalizationMap l E S f))) ∧
    (∀ (H : SheafOfModules.{u + 1}
        (latticeModuleRing X (latticeCoefficientIntegers l E))),
      IsContinuousConstructible X (latticeCoefficientIntegers l E) H →
        IsCompletedModel l E X H) := by
  sorry

end AlgebraicGeometry.ProEtale.RationalStratum
