/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.FourierTransform.FdCoefficientComparison
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import all WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.PoincareDuality.CompletedScalarExtensionTExact
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcFiniteRawScalarComparison

/-! # Generator-normalized scalar transport through the coefficient presentation

Source: Bhatt--Scholze 3.4.12, 3.5.1 and 6.8.2; trace-definition coefficient comparison
(blueprint: lem-fd-coefficient-scalar-lift-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local irreducible] completedScalarComparison completedScalarChainComparison

local instance (priority := 7000) instFdCoefficientScalarLiftNormalization1 (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} T

local instance (priority := 7000) instFdCoefficientScalarLiftNormalization2 (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} T

local instance (priority := 6000) instFdCoefficientScalarLiftNormalization3 (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) : HasDerivedCategory (integralTowerModules.{u, u} l E T) :=
  integralTowerHasDerivedCategory.{u, u} l E T

section Ordinary
variable (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (i : E →ₐ[ℚ_[l]] L) (T : Scheme.{u})

private theorem fdOrdinary_exists :
    ∃ e : completedOrdinaryScalarExtension l E L i T ⋙ fdCoefficientTransport l L T ≅
        fdCoefficientTransport l E T ⋙ pbcExtend (pbcScalarCoefficientMap l E L i T),
      ∀ (M : integralTowerModules l E T) (U : T.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L T).obj.obj U)
        (x : M.val.obj U),
        (e.hom.app M).val.app U (completedScalarTensorSection l E L i T M U s x) =
          pbcTensorSection (pbcScalarCoefficientMap l E L i T)
            ((fdCoefficientTransport l E T).obj M) U
            ((integralDetailedCoefficientComparison T l L).inv.hom.app U s) x := by
  let cE := purCoefficientIso l E T
  let cL := purCoefficientIso l L T
  let f := completedCoefficientMap l E L i T
  let g := pbcScalarCoefficientMap l E L i T
  have hs : cE.inv ≫ g = f ≫ cL.inv := by
    apply (cancel_mono cL.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h := coefficientScalar_square l E L i T
    rw [scalarMap_eq_completed l E L i T] at h
    change cE.hom ≫ f = g ≫ cL.hom at h
    rw [← h, Iso.inv_hom_id_assoc]
  obtain ⟨aG, hG⟩ := coefficientRestrictionAdjunction T cE.symm
  obtain ⟨aH, hH⟩ := coefficientRestrictionAdjunction T cL.symm
  have hI := (pbcScalarAdjunction_exists g).exists.choose_spec
  have hm (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))
      (U : T.ProEtᵒᵖ) (s z : (pbcAdicCompletion T (pbcIntegralDatum l L)).obj.obj U)
      (x : M.val.obj U) :
      pbcTensorSection g M U (s * z) x = s • pbcTensorSection g M U z x := by
    unfold pbcTensorSection
    exact completedTensor_smul T g M U s z x
  obtain ⟨e, he, _⟩ := ordinaryScalarComparison T cE.symm cL.symm f g hs
    (pbcExtend g) (pbcTensorSection g) (pbcScalarAdjunction g) hI hm aG hG aH hH
  have hE := (purCoefficientIso_existsUnique l E T).exists.choose_spec
  have hL := (purCoefficientIso_existsUnique l L T).exists.choose_spec
  change (adicLisseForget T).mapIso cE = integralDetailedCoefficientComparison T l E at hE
  change (adicLisseForget T).mapIso cL = integralDetailedCoefficientComparison T l L at hL
  unfold fdCoefficientTransport
  rw [← hE, ← hL]
  refine ⟨e, ?_⟩
  intro M U s x
  exact he M U s x

end Ordinary

private theorem fdOrdinaryTransport_exists (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) {A B : Padic.FiniteCoefficientFields l Ω} (h : A ≤ B) :
    Nonempty (FdOrdinaryScalarTransport l Ω T h) := by
  let E := pbcFiniteField.{u} l Ω A
  let L := pbcFiniteField.{u} l Ω B
  let i := pbcFiniteFieldInclusion.{u} l Ω h
  have hm := rawScalar_coefficientMap l Ω T h
  change pbcCompletedScalarMap l Ω T h = pbcScalarCoefficientMap l E L i T at hm
  have ho : ∃ c : completedOrdinaryScalarExtension l E L i T ⋙
        fdCoefficientTransport l L T ≅
        fdCoefficientTransport l E T ⋙ pbcExtend (pbcCompletedScalarMap l Ω T h),
      ∀ (M : integralTowerModules l E T) (U : T.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L T).obj.obj U)
        (x : M.val.obj U),
        (c.hom.app M).val.app U (completedScalarTensorSection l E L i T M U s x) =
          pbcTensorSection (pbcCompletedScalarMap l Ω T h)
            ((fdCoefficientTransport l E T).obj M) U
            ((integralDetailedCoefficientComparison T l L).inv.hom.app U s) x := by
    rw [hm]
    exact fdOrdinary_exists l E L i T
  obtain ⟨c, hc⟩ := ho
  exact ⟨⟨c, hc⟩⟩

private theorem fdScalarDerivedComparison (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (f : R ⟶ S)
    [PreservesFiniteLimits (pbcExtend f)] [PreservesFiniteColimits (pbcExtend f)] :
    ∃ e : pbcDerivedExtend f ≅ (pbcExtend f).mapDerivedCategory,
      ∀ P : CochainComplex (pbcModules T R) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (pbcExtend f).mapDerivedCategoryFactors.hom.app P = pbcComplexCounit f P := by
  let F := pbcExtend f
  let LF := pbcDerivedExtend f
  let ε := pbcExtensionCounit f
  let V := HomotopyCategory.quasiIso (pbcModules T R) (.up ℤ)
  have : LF.IsLeftDerivedFunctor ε V := pbcDerivedExtension_universal _
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom V :=
    Functor.isLeftDerivedFunctor_of_inverts V _ F.mapDerivedCategoryFactorsh
  let e := Functor.leftDerivedNatIso LF F.mapDerivedCategory ε
    F.mapDerivedCategoryFactorsh.hom V (Iso.refl _)
  have he (P : HomotopyCategory (pbcModules T R) (.up ℤ)) :
      e.hom.app (DerivedCategory.Qh.obj P) ≫
        F.mapDerivedCategoryFactorsh.hom.app P = ε.app P := by
    simpa only [e, Functor.leftDerivedNatIso_hom, Iso.refl_hom,
      NatTrans.id_app, Category.comp_id] using
      Functor.leftDerivedNatTrans_app LF F.mapDerivedCategory ε
        F.mapDerivedCategoryFactorsh.hom V (𝟙 _) P
  refine ⟨e, ?_⟩
  intro P
  unfold pbcComplexCounit
  rw [← he]
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  dsimp only [F, LF]
  simp only [Category.assoc, ← NatTrans.naturality_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app]
  exact congrArg (fun f ↦ e.hom.app (DerivedCategory.Q.obj P) ≫ f)
    (Category.comp_id (F.mapDerivedCategoryFactors.hom.app P)).symm

private theorem fdDerivedTransport_exists (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) {A B : Padic.FiniteCoefficientFields l Ω} (h : A ≤ B)
    (o : FdOrdinaryScalarTransport l Ω T h) :
    ∃ b : integralDetailedTransport T l (pbcFiniteField.{u} l Ω A) ⋙
        pbcAmbientScalarExtension l Ω T h ≅
      completedDerivedScalarExtension.{u, u} l (pbcFiniteField.{u} l Ω A)
        (pbcFiniteField.{u} l Ω B) (pbcFiniteFieldInclusion l Ω h) T ⋙
          integralDetailedTransport T l (pbcFiniteField.{u} l Ω B),
      ∀ P : CochainComplex (integralTowerModules.{u, u} l (pbcFiniteField.{u} l Ω A) T) ℤ,
        b.hom.app (DerivedCategory.Q.obj P) ≫
          (integralDetailedTransport T l (pbcFiniteField.{u} l Ω B)).map
            (completedScalarCounit.{u, u} l (pbcFiniteField.{u} l Ω A)
              (pbcFiniteField.{u} l Ω B) (pbcFiniteFieldInclusion l Ω h) T P) ≫
          (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω B) T).hom.app
            ((completedOrdinaryScalarComplex.{u, u} l (pbcFiniteField.{u} l Ω A)
              (pbcFiniteField.{u} l Ω B) (pbcFiniteFieldInclusion l Ω h) T).obj P) =
        (pbcAmbientScalarExtension l Ω T h).map
          ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω A) T).hom.app P) ≫
        pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
          (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω A) T).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((o.complex l Ω).inv.app P) := by
  let E := pbcFiniteField.{u} l Ω A
  let L := pbcFiniteField.{u} l Ω B
  let i := pbcFiniteFieldInclusion.{u} l Ω h
  let F := completedOrdinaryScalarExtension.{u, u} l E L i T
  let G : integralTowerModules.{u, u} l L T ⥤
      pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l L)) :=
    fdCoefficientTransport l L T
  let H : integralTowerModules.{u, u} l E T ⥤
      pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)) :=
    fdCoefficientTransport l E T
  let J := pbcExtend (pbcCompletedScalarMap l Ω T h)
  let : F.Additive := completedOrdinaryScalarExtension_additive l E L i T
  let : G.Additive := fdCoefficientTransportAdditive l L T
  let : H.Additive := fdCoefficientTransportAdditive l E T
  let : J.Additive := pbcExtend_additive _
  have : PreservesFiniteLimits F := podCompletedOrdinaryScalarExtension_preservesFiniteLimits
    l E L i T
  have : PreservesFiniteColimits F := podCompletedOrdinaryScalarExtension_preservesFiniteColimits
    l E L i T
  have : PreservesFiniteLimits G := fdCoefficientTransportLimits l L T
  have : PreservesFiniteColimits G := fdCoefficientTransportColimits l L T
  have : PreservesFiniteLimits H := fdCoefficientTransportLimits l E T
  have : PreservesFiniteColimits H := fdCoefficientTransportColimits l E T
  have : PreservesFiniteLimits J := by
    dsimp only [J]
    rw [rawScalar_coefficientMap l Ω T h]
    exact (scalarExtension_exact l E L i T).1
  have : PreservesFiniteColimits J := by
    dsimp only [J]
    rw [rawScalar_coefficientMap l Ω T h]
    exact (scalarExtension_exact l E L i T).2
  obtain ⟨dF, hdF⟩ := ordinary_derived_comparison l E L i T
  obtain ⟨dJ, hdJ⟩ := fdScalarDerivedComparison T (pbcCompletedScalarMap l Ω T h)
  let e : H ⋙ J ≅ F ⋙ G := o.comparison.symm
  let b := Functor.isoWhiskerLeft H.mapDerivedCategory dJ ≪≫
    Functor.mapDerivedCategorySquareIso e ≪≫
    Functor.isoWhiskerRight dF.symm G.mapDerivedCategory
  refine ⟨b, ?_⟩
  intro P
  have hc := derivedSquare_factors e P
  have hcomplex : (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app P =
      (o.complex l Ω).inv.app P := by
    apply HomologicalComplex.hom_ext
    intro n
    simp only [FdOrdinaryScalarTransport.complex, Iso.trans_inv, NatTrans.comp_app,
      Iso.symm_inv, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f,
      NatIso.mapHomologicalComplex_inv_app_f,
      e, Iso.symm_hom, Iso.refl_inv,
      Iso.refl_hom, NatTrans.id_app]
    change o.comparison.inv.app (P.X n) ≫ 𝟙 _ =
      (𝟙 _ ≫ o.comparison.inv.app (P.X n)) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  rw [hcomplex] at hc
  change (dJ.hom.app (H.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
      (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (dF.inv.app (DerivedCategory.Q.obj P))) ≫
      G.mapDerivedCategory.map (completedScalarCounit l E L i T P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
    (pbcDerivedExtend (pbcCompletedScalarMap l Ω T h)).map
      (H.mapDerivedCategoryFactors.hom.app P) ≫
      pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
        ((H.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((o.complex l Ω).inv.app P)
  simp only [Category.assoc]
  rw [← G.mapDerivedCategory.map_comp_assoc, ← hdF P,
    Iso.inv_hom_id_app_assoc]
  rw [hc]
  rw [← dJ.hom.naturality_assoc]
  have hd : dJ.hom.app ((H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).obj P) ≫
      J.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) =
      pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
        ((H.mapHomologicalComplex (.up ℤ)).obj P) :=
    hdJ ((H.mapHomologicalComplex (.up ℤ)).obj P)
  simpa only [Category.assoc, Functor.comp_obj] using congrArg (fun k ↦
    (pbcDerivedExtend (pbcCompletedScalarMap l Ω T h)).map
      (H.mapDerivedCategoryFactors.hom.app P) ≫
        k ≫ DerivedCategory.Q.map ((o.complex l Ω).inv.app P)) hd

/-- The ordinary coefficient-presentation comparison, composed with the actual
quotient-map completion, gives the required integral scalar lift.
Source: trace-definition coefficient-category sentence, normalized integral
completion comparison proof steps 2 and 3; Bhatt--Scholze 3.4.12, 3.5.1 and 6.8.2
(blueprint: lem-fd-coefficient-scalar-lift-normalization).

Proof: the completed coefficient isomorphisms commute with every finite projection.
Their scalar square therefore commutes. The balanced tensor comparison transports
each tensor generator by precisely these coefficient isomorphisms; its inverse
uses their inverses, and both composites are identities on generators, hence on
the sheafified tensor product. This constructs o. Derive this isomorphism using
the canonical counits, as in purScalarModel_existsUnique. Restrict its inverse
to the integral constructible source, and compose with coefficient transport of
the actual completedScalarComparison. This is invertible because the source is
derived complete and strict scalar extension preserves constructibility. On a
flat-term K-flat representative substitute the counit normalization of the
ordinary transport and the localization equation of completedScalarComparison.
Naturality moves coefficient transport factors across these maps. Cancellation
of the two inverse ordinary tensor comparisons leaves exactly o.completion.
Its quotient coordinates are the actual projections and its shifted-product
coordinate is zero; uniqueness of descent makes the equation independent of the
representative. -/
theorem fdCoefficientScalarLift_normalization
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] :
    ∀ {A B : Padic.FiniteCoefficientFields l Ω} (h : A ≤ B),
      ∃ (o : FdOrdinaryScalarTransport l Ω T h)
        (a : (sfIntegralConstructible l (pbcFiniteField.{u} l Ω A) T).ι ⋙
          integralDetailedTransport T l (pbcFiniteField.{u} l Ω A) ⋙
            pbcAmbientScalarExtension l Ω T h ≅
        sfConstructibleIntegralScalarExtension D.p l hl (pbcFiniteField.{u} l Ω A)
          (pbcFiniteField.{u} l Ω B) (pbcFiniteFieldInclusion l Ω h) T ⋙
          (sfIntegralConstructible l (pbcFiniteField.{u} l Ω B) T).ι ⋙
            integralDetailedTransport T l (pbcFiniteField.{u} l Ω B)),
      ∀ (P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω A) T).FullSubcategory)
        (hP : sfIntegralConstructible l (pbcFiniteField.{u} l Ω A) T
          (DerivedCategory.Q.obj P.obj)),
      HEq (a.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
        (integralDetailedTransport T l (pbcFiniteField.{u} l Ω B)).map
          ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω A)
            (pbcFiniteField.{u} l Ω B) (pbcFiniteFieldInclusion l Ω h) T).hom.app P) ≫
        (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω B) T).hom.app
          ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω A)
            (pbcFiniteField.{u} l Ω B) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj))
        ((pbcAmbientScalarExtension l Ω T h).map
          ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω A) T).hom.app P.obj) ≫
        pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
          (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω A) T).mapHomologicalComplex
            (.up ℤ)).obj P.obj) ≫
        DerivedCategory.Q.map (o.completion l Ω P.obj)) := by
  have _ := dT.out
  have _ := iT.out
  intro A B h
  let E := pbcFiniteField.{u} l Ω A
  let L := pbcFiniteField.{u} l Ω B
  let i := pbcFiniteFieldInclusion.{u} l Ω h
  obtain ⟨o⟩ := fdOrdinaryTransport_exists l Ω T h
  obtain ⟨b, hb⟩ := fdDerivedTransport_exists l Ω T h o
  let iE := (sfIntegralConstructible l E T).ι
  let iL := (sfIntegralConstructible l L T).ι
  let S := sfConstructibleIntegralScalarExtension D.p l hl E L i T
  let G := integralDetailedTransport T l L
  have hχ (K : sfIntegralConstructibleCategory l E T) :
      IsIso ((completedScalarComparison.{u, u} l E L i T).app K.obj) := by
    obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let D0 := scalarExtensionDatum.{0} q hprime
    have hlD : l ≠ D0.p := by
      change l ≠ q
      omega
    have hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E T K.obj :=
      ⟨D0, hlD, (sfDerivedComplete_iff_legacy l E T D0 hlD K.obj).mp K.property.1⟩
    exact ((finiteFreeCompletedScalarComparison.{u, u} l E L i T).2.1 K.obj hcomplete).1
  let β : iE ⋙ completedDerivedScalarExtension.{u, u} l E L i T ≅ S ⋙ iL :=
    NatIso.ofComponents (fun K ↦ asIso ((completedScalarComparison l E L i T).app K.obj))
      (fun f ↦ (completedScalarComparison l E L i T).naturality f.hom)
  let a := Functor.isoWhiskerLeft iE b ≪≫ Functor.isoWhiskerRight β G
  refine ⟨o, a, ?_⟩
  intro P hP
  apply heq_of_eq
  change (b.hom.app (DerivedCategory.Q.obj P.obj) ≫
      G.map ((completedScalarComparison l E L i T).app (DerivedCategory.Q.obj P.obj))) ≫
      G.map ((integralScalarExtensionComparison l E L i T).hom.app P) ≫
      (fdCoefficientTransportFactors l L T).hom.app
        ((integralScalarComplexFunctor l E L i T).obj P.obj) = _
  have hspec : (completedScalarComparison l E L i T).app (DerivedCategory.Q.obj P.obj) ≫
      (integralScalarExtensionComparison l E L i T).hom.app P =
      completedScalarCounit l E L i T P.obj ≫
        DerivedCategory.Q.map ((completedScalarChainComparison l E L i T).app P.obj) :=
    completedScalarComparison_spec l E L i T P
  rw [Category.assoc, ← G.map_comp_assoc, hspec]
  rw [G.map_comp]
  simp only [Category.assoc]
  have hnat := (fdCoefficientTransportFactors l L T).hom.naturality
    ((completedScalarChainComparison l E L i T).app P.obj)
  change G.map (DerivedCategory.Q.map
      ((completedScalarChainComparison l E L i T).app P.obj)) ≫
      (fdCoefficientTransportFactors l L T).hom.app
        ((integralScalarComplexFunctor l E L i T).obj P.obj) =
    (fdCoefficientTransportFactors l L T).hom.app
      ((completedOrdinaryScalarComplex l E L i T).obj P.obj) ≫
      DerivedCategory.Q.map
        (((fdCoefficientTransport l L T).mapHomologicalComplex (.up ℤ)).map
          ((completedScalarChainComparison l E L i T).app P.obj)) at hnat
  rw [hnat]
  have hfinal := congrArg (fun k ↦ k ≫ DerivedCategory.Q.map
      (((fdCoefficientTransport l L T).mapHomologicalComplex (.up ℤ)).map
        ((completedScalarChainComparison l E L i T).app P.obj))) (hb P.obj)
  simpa only [Category.assoc, FdOrdinaryScalarTransport.completion,
    DerivedCategory.Q.map_comp] using hfinal

end WeilConjectures
