/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdRawLocalization.FdRawLocalizationScalarData
import WeilConjectures.FourierTransform.FdRawLocalization.FdRawLocalizationScalarDescent

/-! # Raw localization of the specified scalar comparisons

Source: trace-definition coefficient-category sentence, extracted raw localization
argument, steps 7--8 (blueprint: lem-fd-raw-localization-scalar-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FdRawLocalization

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)

/-- Exact semilinear raw localization of the specified inverse integral comparison,
with its actual integral lift, normalized units and both four-field contractions.
Source: trace-definition final coefficient-category sentence, extracted proof steps 7--8
(blueprint: lem-fd-raw-localization-scalar-coherence).

Proof:
1. Ordinary and strict scalar extension are semilinear over the coefficient inclusion.
The source uniformizer becomes invertible in the final field. Apply semilinear scalar
localization to b inverse and b. The raw functors fix objects and their Hom maps are
fixed on pure tensors, identifying the endpoints with the specified S, P and J. The
components are exactly Q(b inverse); no replacement of the integral lift is made.
The localized inverse equations and shift squares prove the exact natural isomorphism.
2. Localize the assumed integral inverse cocycle at the final field. Localization
preserves composition and both whiskerings, while the canonical integral associators
localize to the specified rational ones. This gives the three-field equation.
3. At equal fields the assumed integral unit equation identifies b inverse with
inverse completeness after ordinary multiplication. Localizing gives the normalized
identity value. Substituting an identity in either position of the cocycle and using
the two scalar unit laws gives both unit equations; completeness is never set to identity.
4. Expand D. For its first contraction use the cocycle for h,k, then naturality of
j at the inner framework associator, then the cocycle for h.trans k,m. The result is
J of the left framework contraction followed by j for the total extension.
5. For the other contraction, naturality of the PBC associator moves j h across it.
Use the cocycle for k,m at S h K, then for h,k.trans m. The result is J of the right
framework contraction followed by the same total j.
6. The framework pentagon equates the two contractions. The PBC pentagon equates
their target contraction maps as well. No step uses a strict inclusion, so identity,
partially repeated and fully repeated fields and all their unit degeneracies remain.
-/
theorem rawLocalizationScalarCoherence
    (_D : FiniteFieldDatum.{d}) (_hl : l ≠ _D.p)
    (hI : ∀ E : Padic.FiniteCoefficientFields l Ω, (I l Ω T stage E).IsTriangulated)
    (ordinary : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      FdOrdinaryScalarTransport l Ω T h)
    (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
    (hshift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      NatTrans.CommShift (b h).hom ℤ ∧ NatTrans.CommShift (b h).inv ℤ)
    (hexact : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      (I l Ω T stage E ⋙ C l Ω T h).IsTriangulated ∧
        (U l Ω T h ⋙ I l Ω T stage L).IsTriangulated)
    (hlift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
      (V : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
      (hV : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T
        (DerivedCategory.Q.obj V.obj)),
      HEq (((b h).hom.app ⟨DerivedCategory.Q.obj V.obj, hV⟩).hom ≫
        eqToHom (congrArg (fun F ↦ F.obj
          ((U l Ω T h).obj ⟨DerivedCategory.Q.obj V.obj, hV⟩))
          (stage L).integral_identity) ≫
        (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
          ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).hom.app V) ≫
        (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω L) T).hom.app
          ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj V.obj))
        ((pbcAmbientScalarExtension l Ω T h).map
          ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app V.obj) ≫
        pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
          (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
            (.up ℤ)).obj V.obj) ≫
        DerivedCategory.Q.map ((ordinary h).completion l Ω V.obj)))
    (hcocycle : ∀ {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      (b k).inv.app ((U l Ω T h).obj K) ≫
        (C l Ω T k).map ((b h).inv.app K) ≫
        (pbcIntegralScalarAssociator l Ω T dT.out iT.out h k).hom.app
          ((I l Ω T stage E).obj K) =
      (I l Ω T stage M).map ((integralAssoc l Ω T h k).hom.app K) ≫
        (b (h.trans k)).inv.app K)
    (hunit : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      (b (le_refl E)).inv.app K ≫
        (pbcIntegralScalarUnit l Ω T dT.out iT.out E).hom.app ((I l Ω T stage E).obj K) =
      (I l Ω T stage E).map ((integralUnit l Ω T E).hom.app K)) :
    ∃ family : RationalFamily l Ω T stage,
    ∃ j : RawComparison l Ω T stage family,
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
        NatTrans.CommShift (j h).hom ℤ ∧ NatTrans.CommShift (j h).inv ℤ ∧
        (scalar l Ω T h ⋙ J l Ω T stage family L).IsTriangulated ∧
        (J l Ω T stage family E ⋙ (P l Ω T).T h).IsTriangulated) ∧
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
        (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
        (K' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq K' ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) →
        HEq ((j h).hom.app K')
          ((pbcStageLocalization l Ω T L).map ((b h).inv.app K) ≫
            (pbcScalarIntegralComparison l Ω T dT.out iT.out h).inv.app
              ((I l Ω T stage E).obj K))) ∧
      (∀ (E : Padic.FiniteCoefficientFields l Ω)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq ((j (le_refl E)).hom.app K)
          ((J l Ω T stage family E).map
            ((unit l Ω T E).hom.app K))) ∧
      (∀ {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        (j k).hom.app ((scalar l Ω T h).obj K) ≫
          ((P l Ω T).T k).map ((j h).hom.app K) ≫
          ((P l Ω T).assoc h k).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family M).map ((assoc l Ω T h k).hom.app K) ≫
          (j (h.trans k)).hom.app K) ∧
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        (j h).hom.app ((scalar l Ω T (le_refl E)).obj K) ≫
          ((P l Ω T).T h).map ((j (le_refl E)).hom.app K) ≫
          ((P l Ω T).assoc (le_refl E) h).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family L).map ((scalar l Ω T h).map
          ((unit l Ω T E).hom.app K)) ≫
          (j h).hom.app K) ∧
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        (j (le_refl L)).hom.app ((scalar l Ω T h).obj K) ≫
          ((P l Ω T).T (le_refl L)).map ((j h).hom.app K) ≫
          ((P l Ω T).assoc h (le_refl L)).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family L).map
          ((unit l Ω T L).hom.app
            ((scalar l Ω T h).obj K)) ≫ (j h).hom.app K) ∧
      (∀ {E L M N : Padic.FiniteCoefficientFields l Ω}
        (h : E ≤ L) (k : L ≤ M) (m : M ≤ N)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        (fourComparison l Ω T stage family j h k m K ≫
          ((P l Ω T).T m).map
            (((P l Ω T).assoc h k).hom.app ((J l Ω T stage family E).obj K)) ≫
          ((P l Ω T).assoc (h.trans k) m).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family N).map (leftContraction l Ω T h k m K) ≫
          (j ((h.trans k).trans m)).hom.app K) ∧
        (fourComparison l Ω T stage family j h k m K ≫
          ((P l Ω T).assoc k m).hom.app
            (((P l Ω T).T h).obj ((J l Ω T stage family E).obj K)) ≫
          ((P l Ω T).assoc h (k.trans m)).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family N).map (rightContraction l Ω T h k m K) ≫
          (j (h.trans (k.trans m))).hom.app K) ∧
        ((J l Ω T stage family N).map (leftContraction l Ω T h k m K) ≫
          (j ((h.trans k).trans m)).hom.app K =
        (J l Ω T stage family N).map (rightContraction l Ω T h k m K) ≫
          (j (h.trans (k.trans m))).hom.app K)) := by
  obtain ⟨family, j, hj, hlift', hunit', hcocycle', hleft, hright⟩ :=
    rawLocalizationScalarDescent l Ω T stage _D _hl hI ordinary b hshift hexact
      hlift hcocycle hunit
  refine ⟨family, j, hj, hlift', hunit', hcocycle', hleft, hright, ?_⟩
  intro E L M N h k m K
  have hn := (j m).hom.naturality ((assoc l Ω T h k).hom.app K)
  have hp := ((P l Ω T).assoc k m).hom.naturality ((j h).hom.app K)
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [fourComparison, leftContraction]
    calc
      _ = (j m).hom.app ((scalar l Ω T k).obj ((scalar l Ω T h).obj K)) ≫
          ((P l Ω T).T m).map
            ((j k).hom.app ((scalar l Ω T h).obj K) ≫
              ((P l Ω T).T k).map ((j h).hom.app K) ≫
              ((P l Ω T).assoc h k).hom.app ((J l Ω T stage family E).obj K)) ≫
          ((P l Ω T).assoc (h.trans k) m).hom.app
            ((J l Ω T stage family E).obj K) := by
        simp only [Functor.map_comp, Category.assoc]
      _ = (j m).hom.app ((scalar l Ω T k).obj ((scalar l Ω T h).obj K)) ≫
          ((P l Ω T).T m).map
            ((J l Ω T stage family M).map ((assoc l Ω T h k).hom.app K) ≫
              (j (h.trans k)).hom.app K) ≫
          ((P l Ω T).assoc (h.trans k) m).hom.app
            ((J l Ω T stage family E).obj K) := by
        rw [hcocycle']
      _ = (J l Ω T stage family N).map
            ((scalar l Ω T m).map ((assoc l Ω T h k).hom.app K)) ≫
          ((j m).hom.app ((scalar l Ω T (h.trans k)).obj K) ≫
            ((P l Ω T).T m).map ((j (h.trans k)).hom.app K) ≫
            ((P l Ω T).assoc (h.trans k) m).hom.app
              ((J l Ω T stage family E).obj K)) := by
        simpa only [Functor.map_comp, Functor.comp_map, Functor.comp_obj, Category.assoc] using
          (congrArg (fun f ↦ f ≫
            ((P l Ω T).T m).map ((j (h.trans k)).hom.app K) ≫
            ((P l Ω T).assoc (h.trans k) m).hom.app
              ((J l Ω T stage family E).obj K)) hn).symm
      _ = (J l Ω T stage family N).map
            ((scalar l Ω T m).map ((assoc l Ω T h k).hom.app K)) ≫
          ((J l Ω T stage family N).map
            ((assoc l Ω T (h.trans k) m).hom.app K) ≫
            (j ((h.trans k).trans m)).hom.app K) := by
        rw [hcocycle']
      _ = _ := by simp only [Functor.map_comp, Category.assoc]
  · dsimp only [fourComparison, rightContraction]
    calc
      _ = (j m).hom.app ((scalar l Ω T k).obj ((scalar l Ω T h).obj K)) ≫
          ((P l Ω T).T m).map ((j k).hom.app ((scalar l Ω T h).obj K)) ≫
          (((P l Ω T).assoc k m).hom.app
            ((J l Ω T stage family L).obj ((scalar l Ω T h).obj K)) ≫
            ((P l Ω T).T (k.trans m)).map ((j h).hom.app K)) ≫
          ((P l Ω T).assoc h (k.trans m)).hom.app
            ((J l Ω T stage family E).obj K) := by
        simpa only [Functor.comp_map, Functor.comp_obj, Category.assoc] using
          congrArg (fun f ↦
            (j m).hom.app ((scalar l Ω T k).obj ((scalar l Ω T h).obj K)) ≫
            ((P l Ω T).T m).map ((j k).hom.app ((scalar l Ω T h).obj K)) ≫
            f ≫ ((P l Ω T).assoc h (k.trans m)).hom.app
              ((J l Ω T stage family E).obj K)) hp
      _ = (J l Ω T stage family N).map
            ((assoc l Ω T k m).hom.app ((scalar l Ω T h).obj K)) ≫
          (j (k.trans m)).hom.app ((scalar l Ω T h).obj K) ≫
          ((P l Ω T).T (k.trans m)).map ((j h).hom.app K) ≫
          ((P l Ω T).assoc h (k.trans m)).hom.app
            ((J l Ω T stage family E).obj K) := by
        simpa only [Category.assoc] using
          congrArg (fun f ↦ f ≫
            ((P l Ω T).T (k.trans m)).map ((j h).hom.app K) ≫
            ((P l Ω T).assoc h (k.trans m)).hom.app
              ((J l Ω T stage family E).obj K))
            (hcocycle' k m ((scalar l Ω T h).obj K))
      _ = (J l Ω T stage family N).map
            ((assoc l Ω T k m).hom.app ((scalar l Ω T h).obj K)) ≫
          ((J l Ω T stage family N).map
            ((assoc l Ω T h (k.trans m)).hom.app K) ≫
            (j (h.trans (k.trans m))).hom.app K) := by
        rw [hcocycle']
      _ = _ := by simp only [Functor.map_comp, Category.assoc]
  · have ha := GeneralAlgebraicallyClosedCoefficients.associator_cocycle
      l Ω T E L M N h k m K
    change leftContraction l Ω T h k m K = rightContraction l Ω T h k m K at ha
    rw [ha]

end WeilConjectures.FdRawLocalization
