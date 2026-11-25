/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdCoefficientComparison
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Pbc.PbcCommonStageCones
import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import all WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.Shift.Localization

/-! # The integral identity and its raw rationalization

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence; Bhatt--Scholze, Section 6.5,
Definition 6.5.1 and Proposition 6.8.11(3); Stacks Tag 05R6
(blueprint: lem-fd-integral-identity-rational-equivalence).

The comparison uses the existing finite-stage datum, strengthened explicitly by
integral linearity, exactness, inverse formulas and normalized finite reductions.
The fields of `FdRationalStageComparison` retain its forward object, tensor and shift pins.
The coefficient field's canonical small model permits an algebraic closure in any universe.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe d u w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem inverseSemilinear
    {R S : Type*} [CommRing R] [CommRing S]
    {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear S D]
    (φ : R ≃+* S) (e : C ≌ D)
    (hF : ScalarLocalization.IsSemilinear φ.toRingHom e.functor) :
    ScalarLocalization.IsSemilinear φ.symm.toRingHom e.inverse := by
  intro K H a f
  apply e.functor.map_injective
  apply (cancel_mono (e.counitIso.hom.app H)).mp
  rw [hF]
  change e.functor.map (e.inverse.map (a • f)) ≫ e.counitIso.hom.app H =
    (φ (φ.symm a) • e.functor.map (e.inverse.map f)) ≫ e.counitIso.hom.app H
  rw [φ.apply_symm_apply, Linear.smul_comp]
  change (e.inverse ⋙ e.functor).map (a • f) ≫ e.counitIso.hom.app H = _
  rw [e.counitIso.hom.naturality, CategoryTheory.Functor.id_map, Linear.comp_smul]
  congr 1
  exact (e.counitIso.hom.naturality f).symm

-- Localize both integral functors and their unit/counit with the canonical tensor maps.
private def localizedEquivalenceAux
    {R S : Type*} [CommRing R] [CommRing S]
    {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear S D]
    (t : R) (b : S) (φ : R ≃+* S) (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive]
    (h : IsUnit (algebraMap S (Localization.Away b) (φ t)))
    (h' : IsUnit (algebraMap R (Localization.Away t) (φ.symm b)))
    (hF : ScalarLocalization.IsSemilinear φ.toRingHom e.functor)
    (hG : ScalarLocalization.IsSemilinear φ.symm.toRingHom e.inverse) :
    ScalarLocalization R C t ≌ ScalarLocalization S D b := by
  let F := ScalarLocalization.extension t b φ.toRingHom h e.functor hF
  let G := ScalarLocalization.extension b t φ.symm.toRingHom h' e.inverse hG
  have hφ : φ.symm.toRingHom.comp φ.toRingHom = RingHom.id R := by
    ext x
    exact φ.symm_apply_apply x
  have hψ : φ.toRingHom.comp φ.symm.toRingHom = RingHom.id S := by
    ext x
    exact φ.apply_symm_apply x
  have hFG : ScalarLocalization.IsSemilinear (RingHom.id R) (e.functor ⋙ e.inverse) := by
    simpa only [hφ] using
      (ScalarLocalization.semilinear_composition t b φ.toRingHom h
        t φ.symm.toRingHom h' e.functor e.inverse hF hG).2
  have hGF : ScalarLocalization.IsSemilinear (RingHom.id S) (e.inverse ⋙ e.functor) := by
    simpa only [hψ] using
      (ScalarLocalization.semilinear_composition b t φ.symm.toRingHom h'
        b φ.toRingHom h e.inverse e.functor hG hF).2
  have hcomp : ScalarLocalization.extension t t (RingHom.id R)
      (IsLocalization.Away.algebraMap_isUnit t) (e.functor ⋙ e.inverse) hFG = F ⋙ G := by
    simpa only [hφ] using
      (ScalarLocalization.extension_comp t b φ.toRingHom h t φ.symm.toRingHom h'
        e.functor e.inverse hF hG).2
  have hcomp' : ScalarLocalization.extension b b (RingHom.id S)
      (IsLocalization.Away.algebraMap_isUnit b) (e.inverse ⋙ e.functor) hGF = G ⋙ F := by
    simpa only [hψ] using
      (ScalarLocalization.extension_comp b t φ.symm.toRingHom h' b φ.toRingHom h
        e.inverse e.functor hG hF).2
  let η := ScalarLocalization.extensionNatIso t t (RingHom.id R)
    (IsLocalization.Away.algebraMap_isUnit t)
    (ScalarLocalization.isSemilinear_of_linear (𝟭 C)) hFG e.unitIso
  let ε := ScalarLocalization.extensionNatIso b b (RingHom.id S)
    (IsLocalization.Away.algebraMap_isUnit b) hGF
    (ScalarLocalization.isSemilinear_of_linear (𝟭 D)) e.counitIso
  exact CategoryTheory.Equivalence.mk F G
    (eqToIso (ScalarLocalization.extension_id_and_linear (C := C) t).1.symm ≪≫
      η ≪≫ eqToIso hcomp)
    (eqToIso hcomp'.symm ≪≫ ε ≪≫
      eqToIso (ScalarLocalization.extension_id_and_linear (C := D) b).1)

private def localizedEquivalence
    {R S : Type*} [CommRing R] [CommRing S]
    {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear S D]
    (t : R) (b : S) (φ : R ≃+* S) (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive]
    (h : IsUnit (algebraMap S (Localization.Away b) (φ t)))
    (h' : IsUnit (algebraMap R (Localization.Away t) (φ.symm b)))
    (hF : ScalarLocalization.IsSemilinear φ.toRingHom e.functor)
    (hG : ScalarLocalization.IsSemilinear φ.symm.toRingHom e.inverse) :
    ScalarLocalization R C t ≌ ScalarLocalization S D b :=
  { functor := ScalarLocalization.extension t b φ.toRingHom h e.functor hF
    inverse := ScalarLocalization.extension b t φ.symm.toRingHom h' e.inverse hG
    unitIso := (localizedEquivalenceAux t b φ e h h' hF hG).unitIso
    counitIso := (localizedEquivalenceAux t b φ e h h' hF hG).counitIso
    functor_unitIso_comp := (localizedEquivalenceAux t b φ e h h' hF hG).functor_unitIso_comp }

private theorem localizedExact
    {R S : Type*} [CommRing R] [CommRing S]
    {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear S D]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [∀ n : ℤ, (shiftFunctor C n).Linear R]
    [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [IsTriangulated D]
    (t : R) (b : S) (φ : R →+* S)
    (h : IsUnit (algebraMap S (Localization.Away b) (φ t)))
    [HasZeroObject (ScalarLocalization R C t)] [HasShift (ScalarLocalization R C t) ℤ]
    [∀ n : ℤ, (shiftFunctor (ScalarLocalization R C t) n).Additive]
    [Pretriangulated (ScalarLocalization R C t)]
    [HasZeroObject (ScalarLocalization S D b)] [HasShift (ScalarLocalization S D b) ℤ]
    [∀ n : ℤ, (shiftFunctor (ScalarLocalization S D b) n).Additive]
    [Pretriangulated (ScalarLocalization S D b)]
    (Q₀ : C ⥤ ScalarLocalization R C t) (P₀ : D ⥤ ScalarLocalization S D b)
    (hQ : Q₀ = ScalarLocalization.localization R C t)
    (hP : P₀ = ScalarLocalization.localization S D b)
    [Q₀.CommShift ℤ] [P₀.CommShift ℤ] [P₀.IsTriangulated]
    (hdistC : ∀ Δ : Pretriangulated.Triangle (ScalarLocalization R C t),
      Δ ∈ distTriang (ScalarLocalization R C t) ↔
        ∃ Δ₀ : Pretriangulated.Triangle C, Δ₀ ∈ distTriang C ∧
          Nonempty (Δ ≅ Q₀.mapTriangle.obj Δ₀))
    (F : C ⥤ D) [F.Additive] (hF : ScalarLocalization.IsSemilinear φ F)
    [F.CommShift ℤ] [F.IsTriangulated] :
    ∃ cs : (ScalarLocalization.extension t b φ h F hF).CommShift ℤ,
      (fun [_cs : (ScalarLocalization.extension t b φ h F hF).CommShift ℤ] ↦
        (ScalarLocalization.extension t b φ h F hF).IsTriangulated ∧
        ∀ (n : ℤ) (K : C),
          HEq ((ScalarLocalization.extension t b φ h F hF).map
              ((Q₀.commShiftIso n).hom.app K) ≫
            ((ScalarLocalization.extension t b φ h F hF).commShiftIso n).hom.app
              (Q₀.obj K))
            (P₀.map ((F.commShiftIso n).hom.app K) ≫
              (P₀.commShiftIso n).hom.app (F.obj K)))
        (_cs := cs) := by
  subst Q₀
  subst P₀
  let Q := ScalarLocalization.localization R C t
  let P := ScalarLocalization.localization S D b
  let J := ScalarLocalization.extension t b φ h F hF
  let W := Rationalization.W (Submonoid.powers t) C
  have : Q.IsLocalization W :=
    ScalarLocalization.semilinear_localization_isLocalization R C t
  let e : Q ⋙ J ≅ F ⋙ P :=
    eqToIso (ScalarLocalization.extension_spec t b φ h F hF).2.1
  let : Localization.Lifting Q W (F ⋙ P) J := ⟨e⟩
  let cs : J.CommShift ℤ := Functor.commShiftOfLocalization Q W ℤ (F ⋙ P) J
  have : NatTrans.CommShift e.hom ℤ :=
    NatTrans.commShift_iso_hom_of_localization Q W ℤ (F ⋙ P) J
  refine ⟨cs, ?_, ?_⟩
  · have : (Q ⋙ J).IsTriangulated := (Functor.isTriangulated_iff_of_iso e).2 inferInstance
    constructor
    intro Δ hΔ
    obtain ⟨Δ₀, hΔ₀, ⟨i⟩⟩ := (hdistC Δ).1 hΔ
    exact Pretriangulated.isomorphic_distinguished _
      ((Q ⋙ J).map_distinguished Δ₀ hΔ₀) _
      (J.mapTriangle.mapIso i ≪≫ (Functor.mapTriangleCompIso Q J).symm.app Δ₀)
  · intro n K
    apply heq_of_eq
    change J.map ((Q.commShiftIso n).hom.app K) ≫
      (J.commShiftIso n).hom.app (Q.obj K) = _
    rw [Functor.commShiftOfLocalization_iso_hom_app Q W (F ⋙ P) J]
    have eh (X : C) : (Localization.Lifting.iso Q W (F ⋙ P) J).hom.app X =
        𝟙 (P.obj (F.obj X)) := by
      change (eqToHom ((ScalarLocalization.extension_spec t b φ h F hF).2.1) : _ ⟶ _).app X = _
      rw [eqToHom_app]
      rfl
    have ei (X : C) : (Localization.Lifting.iso Q W (F ⋙ P) J).inv.app X =
        𝟙 (P.obj (F.obj X)) := by
      change (eqToHom ((ScalarLocalization.extension_spec t b φ h F hF).2.1).symm :
        _ ⟶ _).app X = _
      rw [eqToHom_app]
      rfl
    rw [eh, ei]
    dsimp only [Q, P, J, Functor.comp_obj, ScalarLocalization.extension,
      ScalarLocalization.localization]
    simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
    change J.map ((Q.commShiftIso n).hom.app K) ≫
      J.map ((Q.commShiftIso n).inv.app K) ≫ (Functor.commShiftIso (F ⋙ P) n).hom.app K = _
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, J.map_id, Category.id_comp,
      Functor.commShiftIso_comp_hom_app]
    rfl

-- State the tensor and scalar APIs with exactly the recorded localization instances.
private theorem localizedTensor
    {R S : Type*} [CommRing R] [CommRing S]
    {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear S D]
    (t : R) (b : S) (φ : R →+* S)
    (h : IsUnit (algebraMap S (Localization.Away b) (φ t)))
    (F : C ⥤ D) [F.Additive] (hF : ScalarLocalization.IsSemilinear φ F)
    (ψ : Localization.Away t →+* Localization.Away b)
    (hψ : ScalarLocalization.coefficientMap t b φ h = ψ)
    (K H : C) (a : Localization.Away t) (f : K ⟶ H) :
    HEq ((ScalarLocalization.extension t b φ h F hF).map (fdRawTensor t a f))
      (fdRawTensor b (ψ a) (F.map f)) := by
  apply heq_of_eq
  change ScalarLocalization.extensionHom t b φ h F hF K H (a ⊗ₜ[R] f) = _
  rw [ScalarLocalization.extensionHom_tmul, hψ]
  rfl

private theorem localizedScale
    {R S : Type*} [CommRing R] [CommRing S]
    {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear S D]
    (t : R) (b : S) (φ : R →+* S)
    (h : IsUnit (algebraMap S (Localization.Away b) (φ t)))
    (F : C ⥤ D) [F.Additive] (hF : ScalarLocalization.IsSemilinear φ F)
    (ψ : Localization.Away t →+* Localization.Away b)
    (hψ : ScalarLocalization.coefficientMap t b φ h = ψ)
    (K H : ScalarLocalization R C t) (a : Localization.Away t) (f : K ⟶ H) :
    (ScalarLocalization.extension t b φ h F hF).map (fdRawScale t a f) =
      fdRawScale b (ψ a) ((ScalarLocalization.extension t b φ h F hF).map f) := by
  change (ScalarLocalization.extension t b φ h F hF).map (a • f) = _
  rw [(ScalarLocalization.extension_spec t b φ h F hF).1, hψ]
  rfl

section Integral

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (T : Scheme.{u}) [IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

omit [Fact l.Prime] [AlgebraicGeometry.IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)] in
private theorem global_unit : IsUnit (l : Γ(T, ⊤)) := by
  apply T.toRingedSpace.isUnit_of_isUnit_germ
  intro t ht
  simpa only [map_natCast] using
    (Fact.out : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) t

omit [AlgebraicGeometry.IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] in
private theorem coefficient_projection (n : ℕ) :
    (purCoefficientIso l E T).hom ≫
        completedIntegralCommRingProjectionUnrestricted l E T n =
      pbcAdicProjection T (pbcIntegralDatum l E) n ≫
        (IntegralCoefficientPresentation.level l E T (integralCoefficientULift l E) n).hom := by
  apply (adicLisseForget T).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  have he := congrArg Iso.hom (purCoefficientIso_existsUnique l E T).exists.choose_spec
  change (adicLisseForget T).map (purCoefficientIso l E T).hom = _ at he
  rw [he]
  exact (integralDetailedCoefficientComparison_exists T l E).exists.choose_spec n

-- Projection normalization determines the constant section before derived descent.
omit [AlgebraicGeometry.IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] in
private theorem coefficient_constant (U : T.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) :
    (purCoefficientIso l E T).hom.hom.app U
        (pbcCompletedSection T (pbcIntegralDatum l E) U (ULift.up a)) =
      integralScalarConstant l E T U a := by
  apply (integralScalarConstant_existsUnique l E T U a).unique ?_
    (integralScalarConstant_existsUnique l E T U a).exists.choose_spec
  intro n
  have hp : pbcCompletedScalar T (pbcIntegralDatum l E) ≫
      pbcAdicProjection T (pbcIntegralDatum l E) n =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk ((pbcIntegralDatum l E).ideal ^ (n + 1)))) ≫
          (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).hom := by
    dsimp only [pbcCompletedScalar, pbcAdicProjection, pbcCompletedComparison]
    erw [Category.assoc]
    erw [HasLimit.isoOfNatIso_hom_π]
    erw [← Category.assoc]
    erw [(adicDatumScalar_exists T
      { toCompleteCoefficientDatum := (pbcIntegralDatum l E).toCompleteCoefficientDatum,
        quotientFinite := (pbcIntegralDatum l E).quotientFinite }).exists.choose_spec n]
    rfl
  have hs := congrArg (fun f ↦ pbcCompletedScalar T (pbcIntegralDatum l E) ≫ f)
    (coefficient_projection l E T n)
  erw [← Category.assoc (pbcCompletedScalar T (pbcIntegralDatum l E))
    (pbcAdicProjection T (pbcIntegralDatum l E) n), hp] at hs
  dsimp only [IntegralCoefficientPresentation.level, Iso.trans_hom, Iso.symm_hom] at hs
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at hs
  have hc := congrArg (fun f ↦ f.hom.app U
      ((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (PbcIntegralRing l E)))).app U
          (ULift.up a))) hs
  have hn := toSheafify_naturality (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom
      (Ideal.Quotient.mk ((pbcIntegralDatum l E).ideal ^ (n + 1)))))
  have hn' := toSheafify_naturality (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).map
      (integralCoefficientULift l E n).toCommRingCatIso.hom)
  have hnn := congrArg (fun f ↦ (f.app U).hom (ULift.up a)) hn
  have hnn' := congrArg (fun f ↦ (f.app U).hom
    (Ideal.Quotient.mk ((pbcIntegralDatum l E).ideal ^ (n + 1)) (ULift.up a))) hn'
  have hq := (integralCoefficientULift_exists l E n).exists.choose_spec (ULift.up a)
  refine hc.trans ?_
  change (((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (integralCoefficientULift l E n).toCommRingCatIso.hom).hom.app U)
    ((((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk ((pbcIntegralDatum l E).ideal ^ (n + 1))))).hom.app U)
      (((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (PbcIntegralRing l E)))).app U)
          (ULift.up a))) = _
  erw [← hnn, ← hnn']
  change ((toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app U)
        ((integralCoefficientULift l E n)
          (Ideal.Quotient.mk ((pbcIntegralDatum l E).ideal ^ (n + 1)) (ULift.up a))) = _
  exact congrArg (fun x ↦ ((toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app U) x)
        hq

omit [AlgebraicGeometry.IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] in
private theorem coefficient_constant_ring (U : T.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) :
    (integralDetailedCoefficientComparison T l E).hom.hom.app U
        (pbcCompletedSection T (pbcIntegralDatum l E) U (ULift.up a)) =
      integralScalarConstant l E T U a := by
  have h := congrArg (fun f ↦ f.hom.app U
      (pbcCompletedSection T (pbcIntegralDatum l E) U (ULift.up a)))
    (congrArg Iso.hom (purCoefficientIso_existsUnique l E T).exists.choose_spec)
  exact h.symm.trans (coefficient_constant l E T U a)

-- Check scalar multiplication on complexes, then descend through the derived localization.
omit [AlgebraicGeometry.IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] in
private theorem detailedTransport_action
    (a : Padic.coefficientExtensionIntegers l E)
    (K : DerivedCategory (integralTowerModules l E T)) :
    (integralDetailedTransport T l E).map ((integralScalarDerivedAction l E T a).app K) =
      ULift.up a • 𝟙 ((integralDetailedTransport T l E).obj K) := by
  let F := fdCoefficientTransport l E T
  let ν : 𝟭 (PbcCompletedDerived T (pbcIntegralDatum l E)) ⟶ 𝟭 _ :=
    { app := fun X ↦ ULift.up a • 𝟙 X
      naturality := by
        intro X Y f
        change f ≫ (ULift.up a • 𝟙 Y) = (ULift.up a • 𝟙 X) ≫ f
        rw [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp] }
  apply IntegralScalarAux.action_descent
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E T) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (integralTowerModules l E T) (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory F.mapDerivedCategoryFactors
    (integralScalarDerivedAction l E T a) ν
    (fun P ↦ (integralScalarChainAction l E T a).app P)
    (integralScalarDerivedAction_app_Q l E T a) (fun P ↦ ?_) K
  have hchain : (F.mapHomologicalComplex (.up ℤ)).map
      ((integralScalarChainAction l E T a).app P) =
      ULift.up a • 𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
    apply HomologicalComplex.hom_ext
    intro i
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (P.X i).val.obj U at x
    change (((integralScalarChainAction l E T a).app P).f i).val.app U x = _
    have h := (integralScalarChainAction_existsUnique l E T a).exists.choose_spec P i U x
    change (((integralScalarChainAction l E T a).app P).f i).val.app U x = _ at h
    refine h.trans ?_
    change integralScalarConstant l E T U a • x =
      (integralDetailedCoefficientComparison T l E).hom.hom.app U
        (pbcCompletedSection T (pbcIntegralDatum l E) U (ULift.up a)) • x
    rw [coefficient_constant_ring]
  dsimp only [Functor.comp_map, ν]
  rw [hchain, Functor.map_smul]
  exact congrArg (fun f ↦ ULift.up a • f)
    (DerivedCategory.Q.map_id ((F.mapHomologicalComplex (.up ℤ)).obj P))

private def integralEquivalenceAux :
    sfIntegralConstructibleCategory l E T ≌
      PbcBoundedConstructibleComplete T (pbcIntegralDatum l E) := by
  let Φ := (purCoefficientModel l E T).symm
  have h : ObjectProperty.inverseImage
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) Φ.functor =
        sfIntegralConstructible l E T := by
    ext K
    exact (integralStratifiedPerfectDetailed T l E Fact.out (global_unit l T) K).symm
  exact Φ.congrFullSubcategory h

-- Expose the two actual restriction functors without unfolding the unit and counit.
private def integralEquivalence :
    sfIntegralConstructibleCategory l E T ≌
      PbcBoundedConstructibleComplete T (pbcIntegralDatum l E) :=
  { functor := ObjectProperty.lift
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))
      ((sfIntegralConstructible l E T).ι ⋙ integralDetailedTransport T l E)
      (fun K ↦ ((integralEquivalenceAux l E T).functor.obj K).property)
    inverse := (sfIntegralConstructible l E T).lift
      ((ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))) ⋙
        pbcDerivedRestrict (purCoefficientIso l E T).inv)
      (fun K ↦ ((integralEquivalenceAux l E T).inverse.obj K).property)
    unitIso := (integralEquivalenceAux l E T).unitIso
    counitIso := (integralEquivalenceAux l E T).counitIso
    functor_unitIso_comp := (integralEquivalenceAux l E T).functor_unitIso_comp }

private theorem integralEquivalence_forward :
    (integralEquivalence l E T).functor ⋙
      (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))) =
    (sfIntegralConstructible l E T).ι ⋙ integralDetailedTransport T l E := rfl

private theorem integralEquivalence_inverse :
    (integralEquivalence l E T).inverse ⋙ (sfIntegralConstructible l E T).ι =
      (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))) ⋙
        pbcDerivedRestrict (purCoefficientIso l E T).inv := rfl

private instance integralEquivalence_additive :
    (integralEquivalence l E T).functor.Additive := by
  have : (integralDetailedTransport T l E).Additive := inferInstanceAs
    ((fdCoefficientTransport l E T).mapDerivedCategory.Additive)
  have : ((integralEquivalence l E T).functor ⋙
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))).Additive := by
    rw [integralEquivalence_forward]
    infer_instance
  exact Functor.additive_of_comp_faithful _
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)))

private instance integralEquivalence_inverse_additive :
    (integralEquivalence l E T).inverse.Additive := by
  have : (pbcDerivedRestrict (purCoefficientIso l E T).inv).Additive :=
    inferInstanceAs (((pbcRestrict (purCoefficientIso l E T).inv).mapDerivedCategory).Additive)
  have : ((integralEquivalence l E T).inverse ⋙
      (sfIntegralConstructible l E T).ι).Additive := by
    rw [integralEquivalence_inverse]
    infer_instance
  exact Functor.additive_of_comp_faithful _ (sfIntegralConstructible l E T).ι

private theorem integralEquivalence_semilinear :
    ScalarLocalization.IsSemilinear
      (ULift.ringEquiv : PbcIntegralRing l E ≃+* _).symm.toRingHom
      (integralEquivalence l E T).functor := by
  intro K H a f
  apply (ObjectProperty.ι
    (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))).map_injective
  change (integralDetailedTransport T l E).map (a • f.hom) =
    ULift.up a • (integralDetailedTransport T l E).map f.hom
  rw [(sfIntegralConstructible_linear l E T).1, Functor.map_comp,
    detailedTransport_action, Linear.smul_comp, Category.id_comp]

private instance integralEquivalence_shift :
    (integralEquivalence l E T).functor.CommShift ℤ := by
  let e := eqToIso (integralEquivalence_forward l E T)
  let : (integralDetailedTransport T l E).CommShift ℤ := inferInstanceAs
    ((fdCoefficientTransport l E T).mapDerivedCategory.CommShift ℤ)
  exact Functor.CommShift.ofComp e ℤ

private instance integralEquivalence_inverse_shift :
    (integralEquivalence l E T).inverse.CommShift ℤ := by
  let e := eqToIso (integralEquivalence_inverse l E T)
  let : (pbcDerivedRestrict (purCoefficientIso l E T).inv).CommShift ℤ :=
    inferInstanceAs (((pbcRestrict (purCoefficientIso l E T).inv).mapDerivedCategory).CommShift ℤ)
  exact Functor.CommShift.ofComp e ℤ

private instance integralEquivalence_tri :
    (integralEquivalence l E T).functor.IsTriangulated := by
  let e := eqToIso (integralEquivalence_forward l E T)
  let : (integralDetailedTransport T l E).CommShift ℤ := inferInstanceAs
    ((fdCoefficientTransport l E T).mapDerivedCategory.CommShift ℤ)
  have : (integralDetailedTransport T l E).IsTriangulated := inferInstanceAs
    ((fdCoefficientTransport l E T).mapDerivedCategory.IsTriangulated)
  have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  exact (Functor.isTriangulated_iff_comp_right e).mpr inferInstance

private instance integralEquivalence_inverse_tri :
    (integralEquivalence l E T).inverse.IsTriangulated := by
  let e := eqToIso (integralEquivalence_inverse l E T)
  let : (pbcDerivedRestrict (purCoefficientIso l E T).inv).CommShift ℤ :=
    inferInstanceAs (((pbcRestrict (purCoefficientIso l E T).inv).mapDerivedCategory).CommShift ℤ)
  have : (pbcDerivedRestrict (purCoefficientIso l E T).inv).IsTriangulated :=
    inferInstanceAs
      (((pbcRestrict (purCoefficientIso l E T).inv).mapDerivedCategory).IsTriangulated)
  have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  exact (Functor.isTriangulated_iff_comp_right e).mpr inferInstance

private theorem integralEquivalence_forward_shift (n : ℤ)
    (K : sfIntegralConstructibleCategory l E T) :
    HEq ((ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))).map
        (((integralEquivalence l E T).functor.commShiftIso n).hom.app K) ≫
      ((ObjectProperty.ι (PbcIsBoundedConstructibleComplete T
        (pbcIntegralDatum l E))).commShiftIso n).hom.app
          ((integralEquivalence l E T).functor.obj K))
      ((integralDetailedTransport T l E).map
          (((sfIntegralConstructible l E T).ι.commShiftIso n).hom.app K) ≫
        (((fdCoefficientTransport l E T).mapDerivedCategory).commShiftIso n).hom.app K.obj) := by
  let e := eqToIso (integralEquivalence_forward l E T)
  let : (integralDetailedTransport T l E).CommShift ℤ := inferInstanceAs
    ((fdCoefficientTransport l E T).mapDerivedCategory.CommShift ℤ)
  have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  apply heq_of_eq
  change (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))).map
    ((Functor.CommShift.OfComp.iso e n).hom.app K) ≫ _ = _
  erw [Functor.CommShift.OfComp.map_iso_hom_app]
  have he (X : sfIntegralConstructibleCategory l E T) : e.hom.app X =
      𝟙 (((sfIntegralConstructible l E T).ι ⋙ integralDetailedTransport T l E).obj X) := rfl
  have hi (X : sfIntegralConstructibleCategory l E T) : e.inv.app X =
      𝟙 (((sfIntegralConstructible l E T).ι ⋙ integralDetailedTransport T l E).obj X) := rfl
  rw [he, hi]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.commShiftIso_comp_hom_app]
  erw [Category.id_comp, Category.comp_id]
  rfl

private theorem integralEquivalence_inverse_shift_pin (n : ℤ)
    (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) :
    HEq ((sfIntegralConstructible l E T).ι.map
        (((integralEquivalence l E T).inverse.commShiftIso n).hom.app K) ≫
      ((sfIntegralConstructible l E T).ι.commShiftIso n).hom.app
        ((integralEquivalence l E T).inverse.obj K))
      ((pbcDerivedRestrict (purCoefficientIso l E T).inv).map
          (((ObjectProperty.ι (PbcIsBoundedConstructibleComplete T
            (pbcIntegralDatum l E))).commShiftIso n).hom.app K) ≫
        (((pbcRestrict (purCoefficientIso l E T).inv).mapDerivedCategory).commShiftIso n).hom.app
          K.obj) := by
  let e := eqToIso (integralEquivalence_inverse l E T)
  let : (pbcDerivedRestrict (purCoefficientIso l E T).inv).CommShift ℤ :=
    inferInstanceAs (((pbcRestrict (purCoefficientIso l E T).inv).mapDerivedCategory).CommShift ℤ)
  have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  apply heq_of_eq
  change (sfIntegralConstructible l E T).ι.map
    ((Functor.CommShift.OfComp.iso e n).hom.app K) ≫ _ = _
  erw [Functor.CommShift.OfComp.map_iso_hom_app]
  have he (X : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) : e.hom.app X =
      𝟙 (((ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))) ⋙
        pbcDerivedRestrict (purCoefficientIso l E T).inv).obj X) := rfl
  have hi (X : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) : e.inv.app X =
      𝟙 (((ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))) ⋙
        pbcDerivedRestrict (purCoefficientIso l E T).inv).obj X) := rfl
  rw [he, hi]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.commShiftIso_comp_hom_app]
  erw [Category.id_comp, Category.comp_id]
  rfl

omit [AlgebraicGeometry.IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] in
private theorem finiteReductions :
    ∃ hρ, IntegralCoefficientPresentation.DerivedCompatible l E T
      (integralCoefficientULift l E) (purCoefficientIso l E T) hρ := by
  obtain ⟨hρ, h⟩ := (IntegralCoefficientPresentation.comparison l E T).2.2.2
  have hq (n : ℕ) (x : PbcIntegralRing l E) :
      integralCoefficientULift l E n (Ideal.Quotient.mk _ x) =
        ULift.up (Ideal.Quotient.mk _ x.down) :=
    (integralCoefficientULift_exists l E n).exists.choose_spec x
  have hc := (h (integralCoefficientULift l E) hq).2.2.2
    (purCoefficientIso l E T) (coefficient_projection l E T)
  exact ⟨hρ, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

private theorem pbcCoefficient_algebraMap (a : PbcIntegralRing l E) :
    pbcRationalCoefficientEquiv l E (algebraMap _ _ a) =
      algebraMap (Padic.coefficientExtensionIntegers l E) E a.down := by
  dsimp only [pbcRationalCoefficientEquiv, RingEquiv.trans_apply]
  erw [IsLocalization.ringEquivOfRingEquiv_eq]
  exact (sfRationalCoefficientEquiv l E).commutes a.down

private theorem localizedCoefficient_up :
    ScalarLocalization.coefficientMap
        (Padic.coefficientExtensionUniformizer l E) (pbcUniformizer l E)
        (ULift.ringEquiv : PbcIntegralRing l E ≃+* _).symm.toRingHom
        (show IsUnit (algebraMap _ (Localization.Away (pbcUniformizer l E))
          (ULift.up (Padic.coefficientExtensionUniformizer l E))) from
          IsLocalization.Away.algebraMap_isUnit (pbcUniformizer l E)) =
      (pbcRationalCoefficientEquiv l E).symm.toRingHom.comp
        (sfRationalCoefficientEquiv l E).toRingHom := by
  symm
  apply (ScalarLocalization.coefficientMap_unique _ _ _ _ _).mp
  ext a
  apply (pbcRationalCoefficientEquiv l E).injective
  change pbcRationalCoefficientEquiv l E
    ((pbcRationalCoefficientEquiv l E).symm
      (sfRationalCoefficientEquiv l E (algebraMap _ _ a))) = _
  rw [RingEquiv.apply_symm_apply, AlgEquiv.commutes]
  exact (pbcCoefficient_algebraMap l E (ULift.up a)).symm

private theorem localizedCoefficient_down :
    ScalarLocalization.coefficientMap (pbcUniformizer l E)
        (Padic.coefficientExtensionUniformizer l E)
        (ULift.ringEquiv : PbcIntegralRing l E ≃+* _).toRingHom
        (show IsUnit (algebraMap _
          (Localization.Away (Padic.coefficientExtensionUniformizer l E))
          (pbcUniformizer l E).down) from
          IsLocalization.Away.algebraMap_isUnit
            (Padic.coefficientExtensionUniformizer l E)) =
      (sfRationalCoefficientEquiv l E).symm.toRingHom.comp
        (pbcRationalCoefficientEquiv l E).toRingHom := by
  symm
  apply (ScalarLocalization.coefficientMap_unique _ _ _ _ _).mp
  ext a
  apply (sfRationalCoefficientEquiv l E).injective
  change sfRationalCoefficientEquiv l E
    ((sfRationalCoefficientEquiv l E).symm
      (pbcRationalCoefficientEquiv l E (algebraMap _ _ a))) = _
  rw [AlgEquiv.apply_symm_apply, pbcCoefficient_algebraMap]
  exact ((sfRationalCoefficientEquiv l E).commutes a.down).symm

end Integral

-- Keep the chosen triangulations and normalized maps abstract during final assembly.
attribute [local irreducible] integralEquivalence integralEquivalenceAux
  localizedEquivalenceAux
  sfRationalTriangulationDatum sfRationalCoefficientEquiv pbcRationalCoefficientEquiv
  ScalarLocalization.extensionHom ScalarLocalization.localization

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
/-- The common integral identity induces inverse exact linear equivalences on the
integral categories and their raw rationalizations, with the prescribed finite reductions.
Source: trace-definition final sentence, auxiliary subclaim from comparison proof steps 1--2;
Bhatt--Scholze, Section 6.5, Definition 6.5.1 and Proposition 6.8.11(3); Stacks Tag 05R6
(blueprint: lem-fd-integral-identity-rational-equivalence).

Proof (the four steps of the DAG node):
1. Apply lem-weil-pbc-integral-coefficient-presentation-comparison. Its unique quotient
isomorphisms send [x] to [x.down].up. Their inverse-limit isomorphism is fixed by every
finite projection. Scalar restriction along it and its inverse are exact inverse functors,
with their normalized finite reductions and transitions. By
lem-weil-pbc-integral-stratified-perfect-characterization, these restrictions preserve and
reflect precisely the two integral predicates, including compatible etale-origin witnesses.
Restrict the ambient functors to the full subcategories. In their common realization both
are identity on objects and arrows.
2. By lem-weil-integral-constructible-triangulated and
lem-weil-pbc-uniform-complete-triangulated, shifts and triangles are inherited.
situation-conventions supplies the shift comparisons induced
by the degreewise identity: coefficient restriction does not change differentials,
shift signs or the cone matrix. Consequently the two restrictions preserve triangles.
lem-weil-integral-constructible-linear identifies the Hom action with constant sections;
the coefficient projection equations fix every constant scalar, proving linearity in
both directions.
3. Use def-weil-rationalization-karoubi, def-weil-pbc-rational-category and
def-weil-linear-scalar-localization. Send K to I(K) and f tensor a to I(f) tensor a.
Integral linearity gives balancedness; additivity extends the map from pure tensors.
On pure tensors the identity and composition equations are the integral functor equations
and multiplication of scalars. The inverse restriction gives the same construction in
reverse. Both composites fix integral objects and pure tensors, hence all morphisms.
Thus these are equivalences with the displayed inverse formulas and field linearity.
The raw categories have exactly the original integral objects: no retract is adjoined.
4. By lem-weil-linear-scalar-localization-triangulated, a distinguished rational triangle
is isomorphic to the localization of an integral distinguished triangle. The localized
identity-induced shift comparison intertwines the two localization functors. Step 2
therefore makes its image distinguished; use the same argument for the inverse.
This proves rational exactness with precisely the shift pins in the comparison datum. -/
theorem fdIntegralIdentityRationalEquivalence
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (E : Padic.FiniteCoefficientFields l Ω) :
    ∃ c : FdRationalStageComparison l Ω T E,
    ∃ si : c.integral.inverse.CommShift ℤ,
    (fun [_si : c.integral.inverse.CommShift ℤ] ↦
      c.integral.functor.Additive ∧ c.integral.inverse.Additive ∧
      c.integral.functor.IsTriangulated ∧
      c.integral.inverse.IsTriangulated ∧
      (∀ (K H : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
        (a : Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E)) (f : K ⟶ H),
        c.integral.functor.map (a • f) = ULift.up a • c.integral.functor.map f) ∧
      (∀ (K H : pbcIntegralStage l Ω T E)
        (a : PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) (f : K ⟶ H),
        c.integral.inverse.map (a • f) = a.down • c.integral.inverse.map f) ∧
      (∀ K : pbcStageCategory l Ω T E,
        c.rational.inverse.obj K = ⟨c.integral.inverse.obj K.obj⟩) ∧
      (∀ (K H : pbcIntegralStage l Ω T E)
        (a : Localization.Away (pbcStageUniformizer.{u} l Ω E)) (f : K ⟶ H),
        HEq (c.rational.inverse.map (fdRawTensor (pbcStageUniformizer.{u} l Ω E) a f))
          (fdRawTensor
            (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E))
            ((sfRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E)).symm
              (pbcRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E) a))
            (c.integral.inverse.map f))) ∧
      (∀ (K H : sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
        (a : Localization.Away
          (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E))) (f : K ⟶ H),
        c.rational.functor.map
            (fdRawScale (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E))
              a f) =
          fdRawScale (pbcStageUniformizer.{u} l Ω E)
            ((pbcRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E)).symm
              (sfRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E) a))
            (c.rational.functor.map f)) ∧
      (∀ (K H : pbcStageCategory l Ω T E)
        (a : Localization.Away (pbcStageUniformizer.{u} l Ω E)) (f : K ⟶ H),
        c.rational.inverse.map (fdRawScale (pbcStageUniformizer.{u} l Ω E) a f) =
          fdRawScale
            (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E))
            ((sfRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E)).symm
              (pbcRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E) a))
            (c.rational.inverse.map f)) ∧
      (fun [_s : c.rational.inverse.CommShift ℤ] ↦
        ∀ (n : ℤ) (K : pbcIntegralStage l Ω T E),
          HEq (c.rational.inverse.map
              (((pbcStageLocalization l Ω T E).commShiftIso n).hom.app K) ≫
            (c.rational.inverse.commShiftIso n).hom.app
              ((pbcStageLocalization l Ω T E).obj K))
            ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).map
                ((c.integral.inverse.commShiftIso n).hom.app K) ≫
              ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).commShiftIso
                n).hom.app (c.integral.inverse.obj K)))
        (_s := c.inverse_exact) ∧
      ∃ e : pbcAdicCompletion T (pbcStageDatum.{u} l Ω E) ≅
          completedIntegralCommRingSheafUnrestricted l (pbcFiniteField.{u} l Ω E) T,
        (adicLisseForget T).mapIso e =
          integralDetailedCoefficientComparison T l (pbcFiniteField.{u} l Ω E) ∧
        c.integral.inverse ⋙ (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι =
          pbcStageInclusion l Ω T E ⋙ pbcDerivedRestrict e.inv ∧
        (∀ (n : ℤ) (K : pbcIntegralStage l Ω T E),
          HEq ((sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι.map
                ((c.integral.inverse.commShiftIso n).hom.app K) ≫
              ((sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι.commShiftIso
                n).hom.app (c.integral.inverse.obj K))
            ((pbcDerivedRestrict e.inv).map
                (((pbcStageInclusion l Ω T E).commShiftIso n).hom.app K) ≫
              (((pbcRestrict e.inv).mapDerivedCategory).commShiftIso n).hom.app K.obj)) ∧
        ∃ r : ∀ n : ℕ,
            pbcRestrict (IntegralCoefficientPresentation.level l (pbcFiniteField.{u} l Ω E) T
                (integralCoefficientULift l (pbcFiniteField.{u} l Ω E)) n).hom ⋙
              pbcRestrict (pbcAdicProjection T (pbcStageDatum.{u} l Ω E) n) ≅
            pbcRestrict (completedIntegralCommRingProjectionUnrestricted l
                (pbcFiniteField.{u} l Ω E) T n) ⋙ pbcRestrict e.hom,
          (∀ (n : ℕ)
            (M : pbcModules T
              (integralCoefficientCommRingSheaf l (pbcFiniteField.{u} l Ω E) T n))
            (U : T.ProEtᵒᵖ) (x : M.val.obj U), ((r n).hom.app M).val.app U x = x) ∧
          ∃ α : ∀ n : ℕ, pbcDerivedRestrict e.hom ⋙
                pbcDerivedExtend (pbcAdicProjection T (pbcStageDatum.{u} l Ω E) n) ≅
              pbcDerivedExtend (completedIntegralCommRingProjectionUnrestricted l
                (pbcFiniteField.{u} l Ω E) T n) ⋙
                pbcDerivedRestrict
                  (IntegralCoefficientPresentation.level l (pbcFiniteField.{u} l Ω E) T
                    (integralCoefficientULift l (pbcFiniteField.{u} l Ω E)) n).hom,
            ∀ (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) (n : ℕ),
              (pbcDerivedScalarAdjunction
                  (pbcAdicProjection T (pbcStageDatum.{u} l Ω E) n)).unit.app
                    ((pbcDerivedRestrict e.hom).obj K.obj) ≫
                (IntegralCoefficientPresentation.restrictedComparison e
                  (IntegralCoefficientPresentation.level l (pbcFiniteField.{u} l Ω E) T
                    (integralCoefficientULift l (pbcFiniteField.{u} l Ω E)) n)
                  (pbcAdicProjection T (pbcStageDatum.{u} l Ω E) n)
                  (completedIntegralCommRingProjectionUnrestricted l
                    (pbcFiniteField.{u} l Ω E) T n) (r n) (α n) K.obj).hom =
                (pbcDerivedRestrict e.hom).map
                  ((pbcDerivedScalarAdjunction
                    (completedIntegralCommRingProjectionUnrestricted l
                      (pbcFiniteField.{u} l Ω E) T n)).unit.app K.obj)) (_si := si) := by
  let F := pbcFiniteField.{u} l Ω E
  let R : Type u := Padic.coefficientExtensionIntegers l F
  let S := PbcIntegralRing l F
  let t := Padic.coefficientExtensionUniformizer l F
  let b := pbcUniformizer l F
  let φ : R ≃+* S := ULift.ringEquiv.symm
  let I : sfIntegralConstructibleCategory l F T ≌ pbcIntegralStage l Ω T E :=
    integralEquivalence l F T
  have hF : ScalarLocalization.IsSemilinear φ.toRingHom I.functor :=
    integralEquivalence_semilinear l F T
  have hG := inverseSemilinear φ I hF
  have hu : IsUnit (algebraMap S (Localization.Away b) (φ t)) :=
    IsLocalization.Away.algebraMap_isUnit b
  have hv : IsUnit (algebraMap R (Localization.Away t) (φ.symm b)) :=
    IsLocalization.Away.algebraMap_isUnit t
  let J : sfRationalConstructibleCategory l F T ≌ pbcStageCategory l Ω T E :=
    localizedEquivalence t b φ I hu hv hF hG
  have hpbc : (pbcStageLocalization l Ω T E).IsTriangulated := by
    constructor
    intro Δ hΔ
    exact (qbarStagePretriangulated_exists l Ω T E).exists.choose_spec _ |>.mpr
      ⟨Δ, hΔ, ⟨Iso.refl _⟩⟩
  have hdist := (sfRationalTriangulationDatum l F T).choose_spec.choose_spec.2
    |>.choose_spec.choose_spec.2.choose_spec.2.2
  obtain ⟨sj, hj, hjshift⟩ := localizedExact
    (C := sfIntegralConstructibleCategory l F T) (D := pbcIntegralStage l Ω T E)
    t b φ.toRingHom hu
    (sfRationalConstructibleLocalization l F T) (pbcStageLocalization l Ω T E)
    rfl rfl hdist I.functor hF
  let : J.functor.CommShift ℤ := sj
  have : J.functor.IsTriangulated := hj
  obtain ⟨sg, hg, hgshift⟩ := localizedExact
    (C := pbcIntegralStage l Ω T E) (D := sfIntegralConstructibleCategory l F T)
    b t φ.symm.toRingHom hv
    (pbcStageLocalization l Ω T E) (sfRationalConstructibleLocalization l F T)
    rfl rfl
    (qbarStagePretriangulated_exists l Ω T E).exists.choose_spec I.inverse hG
  let : J.inverse.CommShift ℤ := sg
  have : J.inverse.IsTriangulated := hg
  let c : FdRationalStageComparison l Ω T E := by
    refine { integral := I
             integral_shift := integralEquivalence_shift l F T
             integral_identity := ?_
             integral_shift_normalization := ?_
             rational := J
             shift := sj
             additive := ?_
             exact := ?_
             inverse_exact := sg
             inverse_triangles := ?_
             objects := ?_
             shift_normalization := ?_
             tensors := ?_ }
    · exact integralEquivalence_forward l F T
    · exact integralEquivalence_forward_shift l F T
    · exact inferInstanceAs
        ((ScalarLocalization.extension t b φ.toRingHom hu I.functor hF).Additive)
    · constructor
      intro Δ hΔ
      exact Functor.map_distinguished J.functor Δ hΔ
    · constructor
      intro Δ hΔ
      exact Functor.map_distinguished J.inverse Δ hΔ
    · intro K
      rfl
    · intro n K
      change HEq (J.functor.map
          (((sfRationalConstructibleLocalization l F T).commShiftIso n).hom.app K) ≫
        (J.functor.commShiftIso n).hom.app
          ((sfRationalConstructibleLocalization l F T).obj K))
        ((pbcStageLocalization l Ω T E).map
          ((I.functor.commShiftIso n).hom.app K) ≫
            ((pbcStageLocalization l Ω T E).commShiftIso n).hom.app (I.functor.obj K))
      exact hjshift n K
    · intro K H a f
      exact localizedTensor t b φ.toRingHom hu I.functor hF _
        (localizedCoefficient_up l F) K H a f
  refine ⟨c, integralEquivalence_inverse_shift l F T,
    integralEquivalence_additive l F T, integralEquivalence_inverse_additive l F T,
    integralEquivalence_tri l F T, integralEquivalence_inverse_tri l F T,
    hF, hG, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K
    rfl
  · intro K H a f
    exact localizedTensor b t φ.symm.toRingHom hv I.inverse hG _
      (localizedCoefficient_down l F) K H a f
  · intro K H a f
    exact localizedScale t b φ.toRingHom hu I.functor hF _
      (localizedCoefficient_up l F) K H a f
  · intro K H a f
    exact localizedScale b t φ.symm.toRingHom hv I.inverse hG _
      (localizedCoefficient_down l F) K H a f
  · intro n K
    exact hgshift n K
  · refine ⟨purCoefficientIso l F T,
      (purCoefficientIso_existsUnique l F T).exists.choose_spec,
      integralEquivalence_inverse l F T, integralEquivalence_inverse_shift_pin l F T, ?_⟩
    obtain ⟨hρ, r, hr, α, hα, _⟩ := finiteReductions l F T
    exact ⟨r, hr, α, fun K n ↦ hα K.obj n⟩

end WeilConjectures
