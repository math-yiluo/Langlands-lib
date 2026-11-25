/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTriangulation
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import all WeilConjectures.AlgebraicGeometry.Perfect.PerfectChartTensorComparison
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedLocalPerfectCriterion
import WeilConjectures.AlgebraicGeometry.Completed.CompletedRealizationDerivedCohomology
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Construction of finite coefficient extension

Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.

## References

* Milne, Section 19
* Bhatt--Scholze 6.6.11
* Stacks 06YY and 08H3
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
variable [Algebra (Padic l) E] [Algebra (Padic l) F]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable (i : E →ₐ[Padic l] F)

/-- The given field embedding restricted to the actual lifted valuation rings. -/
def pbcEmbeddingIntegerMap : PbcIntegralRing l E →+* PbcIntegralRing l F :=
  RingHom.ulift (WeilConjectures.integralScalarIntegerInclusion l E F i)

/-- The same-index positive target quotient kills the source uniformizer ideal power. -/
theorem pbcEmbeddingIntegerMap_quotient_kernel (n : ℕ) (a : PbcIntegralRing l E)
    (ha : a ∈ (pbcIntegralDatum l E).ideal ^ (n + 1)) :
    Ideal.Quotient.mk ((pbcIntegralDatum l F).ideal ^ (n + 1))
      (pbcEmbeddingIntegerMap l E F i a) = 0 := by
  change a ∈ (Ideal.span {pbcUniformizer l E}) ^ (n + 1) at ha
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
  have hx : a.down ∈ Padic.coefficientExtensionIdeal l E (n + 1) := by
    rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact map_dvd (ULift.ringEquiv.toRingHom) ha
  have ht := Ideal.Quotient.eq_zero_iff_mem.mp
    (WeilConjectures.integralScalar_quotient_kernel l E F i n a.down hx)
  rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at ht
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change pbcEmbeddingIntegerMap l E F i a ∈
    (Ideal.span {pbcUniformizer l F}) ^ (n + 1)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact map_dvd (ULift.ringEquiv.symm.toRingHom) ht

/-- The finite coefficient map induced by the specified field embedding. -/
def pbcScalarQuotientMap (n : ℕ) :
    PbcQuotient (pbcIntegralDatum l E) n →+* PbcQuotient (pbcIntegralDatum l F) n :=
  Ideal.Quotient.lift ((pbcIntegralDatum l E).ideal ^ (n + 1))
    ((Ideal.Quotient.mk ((pbcIntegralDatum l F).ideal ^ (n + 1))).comp
      (pbcEmbeddingIntegerMap l E F i))
    (pbcEmbeddingIntegerMap_quotient_kernel l E F i n)

variable (T : Scheme.{u})

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcFiniteCoefficientMap_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (a : A →+* B) (b : B →+* C) :
    AdicCoefficients.coefficientMap T a ≫ AdicCoefficients.coefficientMap T b =
      AdicCoefficients.coefficientMap T (b.comp a) := by
  unfold AdicCoefficients.coefficientMap
  rw [← CategoryTheory.Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcFiniteCoefficientMap_id
    {A : Type (u + 1)} [CommRing A] [Finite A] :
    AdicCoefficients.coefficientMap T (RingHom.id A) = 𝟙 _ := by
  unfold AdicCoefficients.coefficientMap
  have h : AdicCoefficients.functionPresheafMap T (RingHom.id A) = 𝟙 _ := by
    ext U f
    rfl
  rw [h]
  exact (presheafToSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_id _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The residue-normalized completed coefficient map exists uniquely. -/
theorem pbcScalarCoefficientMap_exists :
    ∃! a : pbcAdicCompletion T (pbcIntegralDatum l E) ⟶
        pbcAdicCompletion T (pbcIntegralDatum l F),
      ∀ n : ℕ, a ≫ pbcAdicProjection T (pbcIntegralDatum l F) n =
        pbcAdicProjection T (pbcIntegralDatum l E) n ≫
          @AdicCoefficients.coefficientMap T
            (PbcQuotient (pbcIntegralDatum l E) n)
            (PbcQuotient (pbcIntegralDatum l F) n) _ _ _ _
            (pbcScalarQuotientMap l E F i n) := by
  let t : pbcAdicRings T (pbcIntegralDatum l E) ⟶
      pbcAdicRings T (pbcIntegralDatum l F) :=
    NatTrans.ofOpSequence (fun n ↦
      AdicCoefficients.coefficientMap T (pbcScalarQuotientMap l E F i n)) (fun n ↦ by
      simp only [pbcAdicRings, AdicCoefficients.ringSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      rw [pbcFiniteCoefficientMap_comp, pbcFiniteCoefficientMap_comp]
      congr 1
      ext x
      rfl)
  refine ⟨limMap t, ?_, ?_⟩
  · intro n
    exact limMap_π t (op n)
  · intro c hc
    apply limit.hom_ext
    intro n
    exact (hc n.unop).trans (limMap_π t n).symm

/-- The actual completed coefficient inclusion, fixed by all residue projections. -/
def pbcScalarCoefficientMap :
    pbcAdicCompletion T (pbcIntegralDatum l E) ⟶
      pbcAdicCompletion T (pbcIntegralDatum l F) :=
  (pbcScalarCoefficientMap_exists l E F i T).exists.choose

/-- Ordinary ambient derived tensor along the actual completed coefficient inclusion. -/
abbrev pbcEmbeddingAmbientTensor :
    PbcCompletedDerived T (pbcIntegralDatum l E) ⥤
      PbcCompletedDerived T (pbcIntegralDatum l F) :=
  pbcDerivedExtend (pbcScalarCoefficientMap l E F i T)

variable [IsNoetherian T]
variable (hDim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
variable (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarLevelConstantComparison_eq (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (pbcLevelConstantComparison T d n).hom =
      AdicCoefficients.constantComparison T (A ⧸ d.ideal ^ (n + 1)) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pbcAdicRings T d).obj (op n)).property
  change toSheafify _ _ ≫ (pbcLevelConstantComparison T d n).hom.hom =
    toSheafify _ _ ≫ sheafifyMap _ _
  rw [← toSheafify_naturality]
  ext U b
  exact (pbcLevelConstantComparison_exists T d n).exists.choose_spec U b

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarLevelConstantComparison_naturality (T : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B) (n : ℕ)
    (q : (A ⧸ dA.ideal ^ (n + 1)) →+* (B ⧸ dB.ideal ^ (n + 1))) :
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map (CommRingCat.ofHom q) ≫
        (pbcLevelConstantComparison T dB n).hom =
      (pbcLevelConstantComparison T dA n).hom ≫ AdicCoefficients.coefficientMap T q := by
  rw [scalarLevelConstantComparison_eq, scalarLevelConstantComparison_eq]
  change (presheafToSheaf _ CommRingCat).map _ ≫
      (presheafToSheaf _ CommRingCat).map _ =
    (presheafToSheaf _ CommRingCat).map _ ≫
      (presheafToSheaf _ CommRingCat).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

private theorem scalarExactDerived
    {R S C D : Type*} [CommRing R] [CommRing S]
    [Category C] [Category D] [Abelian C] [Abelian D] [Linear R C] [Linear S D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : R) (b : S)
    (h : ∀ (M N : C) (f : M ⟶ N), F.map (a • f) = b • F.map f)
    (K L : DerivedCategory C) (f : K ⟶ L) :
    F.mapDerivedCategory.map (a • f) = b • F.mapDerivedCategory.map f := by
  let G := F.mapDerivedCategory
  let γ₁ : G ⟶ G :=
    { app := fun M ↦ G.map (a • 𝟙 M)
      naturality := fun M N f ↦ by
        simp only [← G.map_comp, Linear.comp_smul, Linear.smul_comp,
          Category.comp_id, Category.id_comp] }
  let γ₂ : G ⟶ G :=
    { app := fun M ↦ b • 𝟙 (G.obj M)
      naturality := fun M N f ↦ by simp }
  have heq : γ₁ = γ₂ := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
    intro P
    change G.map (a • 𝟙 (DerivedCategory.Q.obj P)) = b • 𝟙 _
    apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app P)).mp
    have hn := F.mapDerivedCategoryFactors.hom.naturality (a • 𝟙 P)
    have hc : (F.mapHomologicalComplex (.up ℤ)).map (a • 𝟙 P) =
        b • 𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
      ext n
      change F.map (a • 𝟙 (P.X n)) = b • 𝟙 (F.obj (P.X n))
      simpa only [CategoryTheory.Functor.map_id] using h (P.X n) (P.X n) (𝟙 _)
    simp only [Functor.comp_map, Functor.map_smul, CategoryTheory.Functor.map_id, hc,
      Linear.comp_smul] at hn
    rw [Linear.smul_comp, Category.id_comp]
    change G.map (a • 𝟙 (DerivedCategory.Q.obj P)) ≫
      F.mapDerivedCategoryFactors.hom.app P = b • F.mapDerivedCategoryFactors.hom.app P
    exact hn.trans (congrArg (fun z ↦ b • z)
      (Category.comp_id (F.mapDerivedCategoryFactors.hom.app P)))
  have hi := congrArg (fun γ : G ⟶ G ↦ γ.app K) heq
  change G.map (a • f) = b • G.map f
  change G.map (a • 𝟙 K) = b • 𝟙 (G.obj K) at hi
  calc
    G.map (a • f) = G.map ((a • 𝟙 K) ≫ f) :=
      congrArg G.map (by rw [Linear.smul_comp, Category.id_comp])
    _ = (b • 𝟙 (G.obj K)) ≫ G.map f := by rw [G.map_comp, hi]
    _ = b • G.map f := by rw [Linear.smul_comp, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsNoetherian T] in
private theorem scalarCompletedCoefficientConstant :
    pbcCompletedScalar T (pbcIntegralDatum l E) ≫ pbcScalarCoefficientMap l E F i T =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (pbcEmbeddingIntegerMap l E F i)) ≫
        pbcCompletedScalar T (pbcIntegralDatum l F) := by
  have hp (A : Type u) [Field A] [Algebra (Padic l) A]
      [FiniteDimensional (Padic l) A] (n : ℕ) :
      pbcCompletedScalar T (pbcIntegralDatum l A) ≫
          pbcAdicProjection T (pbcIntegralDatum l A) n =
        (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk ((pbcIntegralDatum l A).ideal ^ (n + 1)))) ≫
            (pbcLevelConstantComparison T (pbcIntegralDatum l A) n).hom := by
    dsimp only [pbcCompletedScalar, pbcAdicProjection, pbcCompletedComparison]
    rw [Category.assoc]
    erw [HasLimit.isoOfNatIso_hom_π]
    rw [← Category.assoc]
    erw [(adicDatumScalar_exists T
      { toCompleteCoefficientDatum := (pbcIntegralDatum l A).toCompleteCoefficientDatum,
        quotientFinite := (pbcIntegralDatum l A).quotientFinite }).exists.choose_spec n]
    rfl
  apply limit.hom_ext
  rintro ⟨n⟩
  change _ ≫ pbcAdicProjection T (pbcIntegralDatum l F) n =
    _ ≫ pbcAdicProjection T (pbcIntegralDatum l F) n
  have hc := (pbcScalarCoefficientMap_exists l E F i T).exists.choose_spec n
  change pbcScalarCoefficientMap l E F i T ≫ _ = _ at hc
  rw [Category.assoc, hc,
    ← Category.assoc, hp, Category.assoc, Category.assoc, hp]
  rw [← scalarLevelConstantComparison_naturality]
  simp only [← Functor.map_comp_assoc]
  congr 2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsNoetherian T] in
private theorem scalarCompletedCoefficientSection (U : T.ProEtᵒᵖ) (a : PbcIntegralRing l E) :
    (pbcScalarCoefficientMap l E F i T).hom.app U
        (pbcCompletedSection T (pbcIntegralDatum l E) U a) =
      pbcCompletedSection T (pbcIntegralDatum l F) U (pbcEmbeddingIntegerMap l E F i a) := by
  have h := congrArg (fun f ↦ f.hom.app U
    (((toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (PbcIntegralRing l E))))).app U a))
    (scalarCompletedCoefficientConstant l E F i T)
  have hn := toSheafify_naturality (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom (pbcEmbeddingIntegerMap l E F i)))
  have hc := congrArg (fun f ↦ f.app U a) hn
  change _ = (pbcCompletedScalar T (pbcIntegralDatum l F)).hom.app U _ at h
  exact h.trans (congrArg ((pbcCompletedScalar T (pbcIntegralDatum l F)).hom.app U) hc.symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The K-flat counit computes a bounded projective completed constant model.
This is the representative-level factorization used in the completed local-perfect
criterion, retaining the given complex instead of choosing a new representative. -/
private def scalarPerfectModel (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (C : CochainComplex (ModuleCat.{u + 1} A) ℤ) (b : ℤ) [C.IsStrictlyLE b]
    (hC : ∀ q : ℤ, Module.Projective A (C.X q)) :
    (integralConstantDerived X d).obj ((completedConstantQ _).obj C) ≅
      (pbcDerivedExtend (pbcCompletedScalar X d)).obj
        (DerivedCategory.Q.obj ((CompletedConstantReduction.constantComplex X A).obj C)) := by
  let F := adicLisseConstantModules X A
  have : F.Additive := CompletedConstantReduction.constant_additive X A
  have : PreservesFiniteLimits F := (CompletedConstantReduction.constant_exact X A).1
  have : PreservesFiniteColimits F := (CompletedConstantReduction.constant_exact X A).2
  let c := CompletedConstantReduction.base X d.ideal ≫ (pbcCompletedComparison X d).hom
  have hc : c = pbcCompletedScalar X d := by
    unfold pbcCompletedScalar
    rw [completedScalar_eq]
  let C₀ := (CompletedConstantReduction.constantComplex X A).obj C
  have : IsIso (pbcComplexCounit c C₀) := by
    have := pbcExtensionCounit_isIso c C₀ (constant_kflat X C b hC)
    dsimp only [pbcComplexCounit]
    infer_instance
  exact (integralRealizationFactors X d).app C ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
      (ordinaryConstantModel X d) (.up ℤ)).app C) ≪≫
    (DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (F ⋙ pbcExtend c)) (.up ℤ)).app C)).symm ≪≫
    (asIso (pbcComplexCounit c C₀)).symm ≪≫
    (eqToIso (congrArg (fun z ↦ (pbcDerivedExtend z).obj (DerivedCategory.Q.obj C₀)) hc))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ambient tensor preserves the three defining integral membership conditions. -/
theorem pbcEmbeddingAmbientTensor_preserves
    (K : PbcIntegralCategory l E T hDim hInv) :
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l F)
      ((pbcEmbeddingAmbientTensor l E F i T).obj K.obj) := by
  classical
  have hl : IsUnit (l : Γ(T, ⊤)) := by
    apply T.toRingedSpace.isUnit_of_isUnit_germ
    intro t ht
    simpa only [map_natCast] using hInv t
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  let φ := pbcScalarCoefficientMap l E F i T
  let q := pbcEmbeddingIntegerMap l E F i
  let G := ModuleCat.extendScalars.{u + 1, u + 1, u + 1} q
  have : G.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} q).left_adjoint_additive
  obtain ⟨s, hs⟩ := (integralCompletedLocalPerfectCriterion T l E hDim hl K.obj).mp K.property
  apply (integralCompletedLocalPerfectCriterion T l F hDim hl _).mpr
  refine ⟨s, fun k ↦ ?_⟩
  obtain ⟨V, hV, hmodels⟩ := hs k
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨P, ⟨C, a, b, ha, hb, hC, ⟨eP⟩⟩, ⟨e⟩⟩ := hmodels U f hf
  let := ha
  let := hb
  let D := (G.mapHomologicalComplex (.up ℤ)).obj C
  have hd (n : ℤ) : Module.Projective (PbcIntegralRing l F) (D.X n) ∧
      Module.Finite (PbcIntegralRing l F) (D.X n) := by
    let := q.toAlgebra
    have := (hC n).1
    have := (hC n).2
    change Module.Projective (PbcIntegralRing l F)
        (TensorProduct (PbcIntegralRing l E) (PbcIntegralRing l F) (C.X n)) ∧
      Module.Finite (PbcIntegralRing l F)
        (TensorProduct (PbcIntegralRing l E) (PbcIntegralRing l F) (C.X n))
    constructor <;> infer_instance
  have : CochainComplex.IsStrictlyGE D a := by dsimp [D]; infer_instance
  have : CochainComplex.IsStrictlyLE D b := by dsimp [D]; infer_instance
  let CE := DerivedCategory.Q.obj ((CompletedConstantReduction.constantComplex T
    (PbcIntegralRing l E)).obj C)
  let β := (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map (CommRingCat.ofHom q)
  have hc : pbcCompletedScalar T dE ≫ φ = β ≫ pbcCompletedScalar T dF :=
    scalarCompletedCoefficientConstant l E F i T
  let em : (pbcDerivedExtend φ).obj ((integralConstantDerived T dE).obj P) ≅
      (integralConstantDerived T dF).obj ((completedConstantQ _).obj D) :=
    (pbcDerivedExtend φ).mapIso ((integralConstantDerived T dE).mapIso eP ≪≫
      scalarPerfectModel T dE C b (fun n ↦ (hC n).1)) ≪≫
    pbcReductionNormalization (pbcCompletedScalar T dE) φ
      (β ≫ pbcCompletedScalar T dF) hc CE ≪≫
    (pbcReductionNormalization β (pbcCompletedScalar T dF)
      (β ≫ pbcCompletedScalar T dF) rfl CE).symm ≪≫
    (pbcDerivedExtend (pbcCompletedScalar T dF)).mapIso
      (constantTensorIso T q C b (fun n ↦ (hC n).1)) ≪≫
    (scalarPerfectModel T dF D b (fun n ↦ (hd n).1)).symm
  obtain ⟨et⟩ := scalarChartRespectsIso (s.immersion k) φ U ⟨e⟩
  exact ⟨(completedConstantQ _).obj D,
    ⟨D, a, b, inferInstance, inferInstance, hd, ⟨Iso.refl _⟩⟩,
    ⟨et ≪≫ integralMapLocalIso (s.immersion k) _ U em⟩⟩

/-- Restriction of the actual ambient tensor, retaining its object and morphism maps. -/
def pbcEmbeddingIntegralTensor :
    PbcIntegralCategory l E T hDim hInv ⥤ PbcIntegralCategory l F T hDim hInv :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l F))
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) ⋙
      pbcEmbeddingAmbientTensor l E F i T)
    (pbcEmbeddingAmbientTensor_preserves l E F i T hDim hInv)

private theorem scalarAdjunction
    {R S C D : Type*} [CommRing R] [CommRing S]
    [Category C] [Category D] [Preadditive C] [Preadditive D] [Linear R C] [Linear S D]
    {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) (a : R) (b : S)
    (h : ∀ (M N : D) (f : M ⟶ N), G.map (b • f) = a • G.map f)
    (K K' : C) (f : K ⟶ K') : L.map (a • f) = b • L.map f := by
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, h]
  have hn := adj.unit.naturality (a • f)
  have hf := adj.unit.naturality f
  simp only [Functor.id_map, Functor.comp_map] at hn hf
  rw [← hn, Linear.smul_comp, hf, Linear.comp_smul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsNoetherian T] in
private theorem scalarRestrict (a : PbcIntegralRing l E)
    (M N : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l F))) (f : M ⟶ N) :
    (pbcRestrict (pbcScalarCoefficientMap l E F i T)).map
        ((pbcEmbeddingIntegerMap l E F i a) • f) =
      a • (pbcRestrict (pbcScalarCoefficientMap l E F i T)).map f := by
  ext U x
  change pbcCompletedSection T (pbcIntegralDatum l F) U (pbcEmbeddingIntegerMap l E F i a) •
      f.val.app U x =
    (pbcScalarCoefficientMap l E F i T).hom.app U
      (pbcCompletedSection T (pbcIntegralDatum l E) U a) • f.val.app U x
  rw [scalarCompletedCoefficientSection]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarIntegralSemilinear :
    ScalarLocalization.IsSemilinear (pbcEmbeddingIntegerMap l E F i)
      (pbcEmbeddingIntegralTensor l E F i T hDim hInv) := by
  intro K L a f
  apply ObjectProperty.hom_ext
  exact scalarAdjunction (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i T))
    a (pbcEmbeddingIntegerMap l E F i a)
    (scalarExactDerived (pbcRestrict (pbcScalarCoefficientMap l E F i T))
      (pbcEmbeddingIntegerMap l E F i a) a (scalarRestrict l E F i T a))
    K.obj L.obj f.hom

private theorem scalarRationalCoefficient (A : Type u) [Field A] [Algebra (Padic l) A]
    [FiniteDimensional (Padic l) A] (a : PbcIntegralRing l A) :
    pbcRationalCoefficientEquiv l A (algebraMap (PbcIntegralRing l A)
      (Localization.Away (pbcUniformizer l A)) a) = (a.down : A) := by
  unfold pbcRationalCoefficientEquiv
  rw [RingEquiv.trans_apply]
  erw [IsLocalization.ringEquivOfRingEquiv_eq]
  exact (Padic.coefficientExtension_localization_uniformizer l A).2.choose.commutes a.down

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
section
attribute [-instance] ULift.module

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The additive Hom map of rational extension is uniquely fixed on pure tensors. -/
theorem pbcRationalScalarHom_exists (K L : PbcIntegralCategory l E T hDim hInv) :
    ∃! m :
      (ScalarLocalization.mk (R := PbcIntegralRing l E) (p := pbcUniformizer l E) K ⟶
        ScalarLocalization.mk L) →+
      (ScalarLocalization.mk (R := PbcIntegralRing l F) (p := pbcUniformizer l F)
        ((pbcEmbeddingIntegralTensor l E F i T hDim hInv).obj K) ⟶
          ScalarLocalization.mk ((pbcEmbeddingIntegralTensor l E F i T hDim hInv).obj L)),
      ∀ (a : Localization.Away (pbcUniformizer l E)) (f : K ⟶ L),
        m (a • (pbcRationalization T (pbcIntegralDatum l E)
          (pbcUniformizer l E)).map f) =
          (pbcRationalCoefficientEquiv l F).symm (i (pbcRationalCoefficientEquiv l E a))
            • (pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)).map
              ((pbcEmbeddingIntegralTensor l E F i T hDim hInv).map f) := by
  let φ := pbcEmbeddingIntegerMap l E F i
  let k : Localization.Away (pbcUniformizer l E) →+*
      Localization.Away (pbcUniformizer l F) :=
    (pbcRationalCoefficientEquiv l F).symm.toRingHom.comp
      (i.toRingHom.comp (pbcRationalCoefficientEquiv l E).toRingHom)
  have hc : k.comp (algebraMap (PbcIntegralRing l E)
      (Localization.Away (pbcUniformizer l E))) =
      (algebraMap (PbcIntegralRing l F) (Localization.Away (pbcUniformizer l F))).comp φ := by
    ext a
    apply (pbcRationalCoefficientEquiv l F).injective
    simp only [RingHom.comp_apply, k, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply, scalarRationalCoefficient]
    rfl
  have hu : IsUnit (algebraMap (PbcIntegralRing l F)
      (Localization.Away (pbcUniformizer l F)) (φ (pbcUniformizer l E))) := by
    have hh := congrArg (fun f ↦ f (pbcUniformizer l E)) hc
    change k (algebraMap _ _ (pbcUniformizer l E)) =
      algebraMap (PbcIntegralRing l F) (Localization.Away (pbcUniformizer l F))
        (φ (pbcUniformizer l E)) at hh
    rw [← hh]
    exact (IsLocalization.Away.algebraMap_isUnit (pbcUniformizer l E)).map k
  have hk := (ScalarLocalization.coefficientMap_unique
    (pbcUniformizer l E) (pbcUniformizer l F) φ hu k).mp hc
  have hFAdd : (pbcEmbeddingIntegralTensor l E F i T hDim hInv).Additive := by
    constructor
    intro M N f g
    apply ObjectProperty.hom_ext
    change (pbcEmbeddingAmbientTensor l E F i T).map (f.hom + g.hom) =
      (pbcEmbeddingAmbientTensor l E F i T).map f.hom +
        (pbcEmbeddingAmbientTensor l E F i T).map g.hom
    have : (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i T)).Additive := by
      unfold pbcDerivedRestrict
      infer_instance
    have : (pbcEmbeddingAmbientTensor l E F i T).Additive :=
      (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i T)).left_adjoint_additive
    exact Functor.map_add _
  obtain ⟨m, hm, huniq⟩ := ScalarLocalization.existsUnique_semilinearHom
    (pbcUniformizer l E) (pbcUniformizer l F) φ hu
    (pbcEmbeddingIntegralTensor l E F i T hDim hInv)
    (scalarIntegralSemilinear l E F i T hDim hInv) K L
  have hm' (a : Localization.Away (pbcUniformizer l E)) (f : K ⟶ L) :
      m (a ⊗ₜ[PbcIntegralRing l E] f) =
        k a ⊗ₜ[PbcIntegralRing l F]
          (pbcEmbeddingIntegralTensor l E F i T hDim hInv).map f := by
    rw [hm, ← hk]
  refine ⟨m, ?_, ?_⟩
  · intro a f
    change m ((a * 1) ⊗ₜ[PbcIntegralRing l E] f) =
      (k a * 1) ⊗ₜ[PbcIntegralRing l F]
        (pbcEmbeddingIntegralTensor l E F i T hDim hInv).map f
    simpa only [mul_one] using hm' a f
  · intro m' hm''
    apply huniq m'
    intro a f
    have h' := hm'' a f
    change m' ((a * 1) ⊗ₜ[PbcIntegralRing l E] f) =
      (k a * 1) ⊗ₜ[PbcIntegralRing l F]
        (pbcEmbeddingIntegralTensor l E F i T hDim hInv).map f at h'
    rw [← hk]
    change m' (a ⊗ₜ[PbcIntegralRing l E] f) =
      k a ⊗ₜ[PbcIntegralRing l F]
        (pbcEmbeddingIntegralTensor l E F i T hDim hInv).map f
    simpa only [mul_one] using h'

end

/-- The unique additive extension of the integral coefficient-change Hom formula. -/
def pbcRationalScalarHom (K L : PbcIntegralCategory l E T hDim hInv) :=
  (pbcRationalScalarHom_exists l E F i T hDim hInv K L).exists.choose

section
attribute [-instance] ULift.module

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcRationalScalarHom_tmul (K L : PbcIntegralCategory l E T hDim hInv)
    (a : Localization.Away (pbcUniformizer l E)) (f : K ⟶ L) :
    pbcRationalScalarHom l E F i T hDim hInv K L (a ⊗ₜ[PbcIntegralRing l E] f) =
      (pbcRationalCoefficientEquiv l F).symm (i (pbcRationalCoefficientEquiv l E a))
        ⊗ₜ[PbcIntegralRing l F]
          (pbcEmbeddingIntegralTensor l E F i T hDim hInv).map f := by
  have h := (pbcRationalScalarHom_exists l E F i T hDim hInv K L).exists.choose_spec a f
  change pbcRationalScalarHom l E F i T hDim hInv K L
      ((a * 1) ⊗ₜ[PbcIntegralRing l E] f) =
    ((pbcRationalCoefficientEquiv l F).symm (i (pbcRationalCoefficientEquiv l E a)) * 1)
      ⊗ₜ[PbcIntegralRing l F] (pbcEmbeddingIntegralTensor l E F i T hDim hInv).map f at h
  simpa only [mul_one] using h

attribute [local irreducible] pbcRationalScalarHom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified rational Hom maps preserve identities and composition. -/
theorem pbcRationalScalarHom_laws :
    (∀ K : PbcRationalDerivedCategory l E T hDim hInv,
      pbcRationalScalarHom l E F i T hDim hInv K.obj K.obj (𝟙 K) =
        𝟙 (ScalarLocalization.mk
          ((pbcEmbeddingIntegralTensor l E F i T hDim hInv).obj K.obj))) ∧
    (∀ (K L M : PbcRationalDerivedCategory l E T hDim hInv) (f : K ⟶ L) (g : L ⟶ M),
      pbcRationalScalarHom l E F i T hDim hInv K.obj M.obj (f ≫ g) =
        pbcRationalScalarHom l E F i T hDim hInv K.obj L.obj f ≫
          pbcRationalScalarHom l E F i T hDim hInv L.obj M.obj g) := by
  constructor
  · intro K
    change pbcRationalScalarHom l E F i T hDim hInv K.obj K.obj
      (1 ⊗ₜ[PbcIntegralRing l E] 𝟙 K.obj) =
        (1 : Localization.Away (pbcUniformizer l F)) ⊗ₜ[PbcIntegralRing l F] 𝟙 _
    rw [pbcRationalScalarHom_tmul]
    simp only [map_one, CategoryTheory.Functor.map_id]
  · intro K L M f g
    change pbcRationalScalarHom l E F i T hDim hInv K.obj M.obj
      (ScalarLocalization.composition _ _ _ _ _ _ g f) =
        ScalarLocalization.composition _ _ _ _ _ _
          (pbcRationalScalarHom l E F i T hDim hInv L.obj M.obj g)
          (pbcRationalScalarHom l E F i T hDim hInv K.obj L.obj f)
    induction g using TensorProduct.inductionOn with
    | tmul b g =>
      induction f using TensorProduct.inductionOn with
      | tmul a f =>
        rw [ScalarLocalization.composition_tmul]
        rw [pbcRationalScalarHom_tmul, pbcRationalScalarHom_tmul,
          pbcRationalScalarHom_tmul, ScalarLocalization.composition_tmul]
        simp only [map_mul, CategoryTheory.Functor.map_comp]
      | add f f' hf hf' => simp only [_root_.map_add, hf, hf']
    | add g g' hg hg' => simp only [_root_.map_add, LinearMap.add_apply, hg, hg']

end

/-- Derived scalar extension followed by raw scalar localization, on the actual Dbc. -/
def pbcRationalScalarExtension :
    PbcRationalDerivedCategory l E T hDim hInv ⥤
      PbcRationalDerivedCategory l F T hDim hInv where
  obj K := ⟨(pbcEmbeddingIntegralTensor l E F i T hDim hInv).obj K.obj⟩
  map {K L} f := pbcRationalScalarHom l E F i T hDim hInv K.obj L.obj f
  map_id K := (pbcRationalScalarHom_laws l E F i T hDim hInv).1 K
  map_comp f g := (pbcRationalScalarHom_laws l E F i T hDim hInv).2 _ _ _ f g

end AlgebraicGeometry.Scheme
