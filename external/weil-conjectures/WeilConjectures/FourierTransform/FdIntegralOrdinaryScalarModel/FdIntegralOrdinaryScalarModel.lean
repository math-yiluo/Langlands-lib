/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.FourierTransform.FdIntegralScalarLiftProperty
import all Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientShift
import all WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible

/-! # Normalized ordinary derived scalar comparison

Source: trace-definition coefficient-category comparison, integral steps 1--6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.FdRawLocalization
namespace WeilConjectures.FdIntegralOrdinaryScalarModel

-- Ring-presentation comparisons use the common completed sheaf, not its limit cone.
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

private theorem cancel_iso_factor
    {A : Type*} [Category A] {X Y Z W : A}
    (a : X ⟶ Y) (e : Y ≅ Z) (b : Y ⟶ W) :
    (a ≫ e.hom) ≫ e.inv ≫ b = a ≫ b := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem iso_square_factor
    {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} (a : F ≅ G) {X W : B} {Y Z : A}
    (e : X ⟶ G.obj Y) (f : Y ⟶ Z) (c : F.obj Z ⟶ W) (d : G.obj Z ⟶ W)
    (h : a.hom.app Z ≫ d = c) :
    (e ≫ a.inv.app Y) ≫ F.map f ≫ c = e ≫ G.map f ≫ d := by
  rw [Category.assoc, ← a.inv.naturality_assoc, ← h]
  simp only [Iso.inv_hom_id_app_assoc]

private theorem normalization_comp
    {A : Type*} [Category A]
    {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ : A}
    (e : X₀ ⟶ X₁) (s : X₁ ⟶ X₂) (u : X₂ ⟶ X₃) (w : X₃ ⟶ X₄)
    (p : X₀ ⟶ Y₁) (q : Y₁ ⟶ Y₂) (v : Y₂ ⟶ X₃)
    (z : Y₂ ⟶ X₄) (k : Y₁ ⟶ Y₃) (f : Y₃ ⟶ X₄)
    (h : e ≫ s ≫ u = p ≫ q ≫ v) (hv : v ≫ w = z)
    (hn : q ≫ z = k ≫ f) : e ≫ s ≫ u ≫ w = p ≫ k ≫ f := by
  calc
    _ = (e ≫ s ≫ u) ≫ w := by simp only [Category.assoc]
    _ = (p ≫ q ≫ v) ≫ w := congrArg (fun x ↦ x ≫ w) h
    _ = p ≫ q ≫ z := by rw [Category.assoc, Category.assoc, hv]
    _ = p ≫ k ≫ f := by rw [hn]

private theorem commShift_ext
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    {F : A ⥤ B} (s t : F.CommShift ℤ)
    (h : ∀ n, Functor.commShiftIso F (self := s) n =
      Functor.commShiftIso F (self := t) n) : s = t := by
  cases s
  cases t
  congr 1
  funext n
  exact h n

private theorem mateShift_eq
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    {F : A ⥤ B} {G : B ⥤ A} (a : F ⊣ G)
    [s : F.CommShift ℤ] [G.CommShift ℤ] [a.CommShift ℤ] :
    a.leftAdjointCommShift ℤ = s := by
  apply commShift_ext
  intro n
  exact Adjunction.CommShift.compatibilityUnit_unique_left a _ _ _
    (Adjunction.LeftAdjointCommShift.compatibilityUnit_iso a n)
    (by
      intro X
      have hu := NatTrans.shift_app_comm a.unit n X
      simp only [Functor.commShiftIso_comp_hom_app,
        Functor.commShiftIso_id_hom_app] at hu
      simpa using hu)

private theorem normalizedIso_shift
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    (Q : A ⥤ B) [Q.CommShift ℤ] [Q.EssSurj]
    (F G : B ⥤ C) [F.CommShift ℤ] [G.CommShift ℤ]
    (H : A ⥤ C) [H.CommShift ℤ]
    (a : Q ⋙ F ⟶ H) [NatTrans.CommShift a ℤ]
    (c : Q ⋙ G ≅ H) [NatTrans.CommShift c.hom ℤ]
    (e : F ≅ G) (he : ∀ X, e.hom.app (Q.obj X) ≫ c.hom.app X = a.app X) :
    NatTrans.CommShift e.hom ℤ := by
  have hh : Functor.whiskerLeft Q e.hom = a ≫ c.inv := by
    ext X
    exact (c.app X).eq_comp_inv.mpr (he X)
  have : NatTrans.CommShift (Functor.whiskerLeft Q e.hom) ℤ := by
    rw [hh]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft e.hom Q
    (fun X ↦ ⟨_, (Q.objObjPreimageIso X).inv, inferInstance⟩)

@[instance_reducible]
private def restrictionShift (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    (pbcDerivedRestrict φ).CommShift ℤ :=
  inferInstanceAs ((pbcRestrict φ).mapDerivedCategory.CommShift ℤ)

attribute [local instance] restrictionShift

private theorem ambientExactModel
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (i : E →ₐ[ℚ_[l]] L) (T : Scheme.{u}) :
    letI := (scalarExtension_exact l E L i T).1
    letI := (scalarExtension_exact l E L i T).2
    ∃ e : pbcEmbeddingAmbientTensor l E L i T ≅
        (pbcExtend (pbcScalarCoefficientMap l E L i T)).mapDerivedCategory,
      (letI := (pbcDerivedScalarAdjunction
        (pbcScalarCoefficientMap l E L i T)).leftAdjointCommShift ℤ
       NatTrans.CommShift e.hom ℤ) ∧
      ∀ P : CochainComplex (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (pbcExtend (pbcScalarCoefficientMap l E L i T)).mapDerivedCategoryFactors.hom.app P =
            pbcComplexCounit (pbcScalarCoefficientMap l E L i T) P := by
  have := (scalarExtension_exact l E L i T).1
  have := (scalarExtension_exact l E L i T).2
  let F := pbcExtend (pbcScalarCoefficientMap l E L i T)
  let LF := pbcDerivedExtend (pbcScalarCoefficientMap l E L i T)
  let ε := pbcExtensionCounit (pbcScalarCoefficientMap l E L i T)
  let V := HomotopyCategory.quasiIso
    (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) (.up ℤ)
  have : LF.IsLeftDerivedFunctor ε V := pbcDerivedExtension_universal _
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom V :=
    Functor.isLeftDerivedFunctor_of_inverts V _ F.mapDerivedCategoryFactorsh
  let e := Functor.leftDerivedNatIso LF F.mapDerivedCategory ε
    F.mapDerivedCategoryFactorsh.hom V (Iso.refl _)
  have he (P : HomotopyCategory
      (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) (.up ℤ)) :
      e.hom.app (DerivedCategory.Qh.obj P) ≫
        F.mapDerivedCategoryFactorsh.hom.app P = ε.app P := by
    simpa only [e, Functor.leftDerivedNatIso_hom, Iso.refl_hom,
      NatTrans.id_app, Category.comp_id] using
      Functor.leftDerivedNatTrans_app LF F.mapDerivedCategory ε
        F.mapDerivedCategoryFactorsh.hom V (𝟙 _) P
  have hε : NatTrans.CommShift ε ℤ :=
    (pbcAmbientScalarShift_exists l E L i T).exists.choose_spec
  have hs : NatTrans.CommShift e.hom ℤ :=
    normalizedIso_shift DerivedCategory.Qh LF F.mapDerivedCategory
      (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ε
      F.mapDerivedCategoryFactorsh e he
  have hadj : (pbcDerivedScalarAdjunction
      (pbcScalarCoefficientMap l E L i T)).CommShift ℤ :=
    AlgebraicGeometry.Scheme.scalarAdjunction_shift l E L i T
  have hm := mateShift_eq
    (s := pbcAmbientScalarShift l E L i T)
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E L i T))
  refine ⟨e, ?_, ?_⟩
  · rw [hm]
    exact hs
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

@[instance_reducible]
private def detailedShift
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) : (integralDetailedTransport T l E).CommShift ℤ :=
  Functor.instCommShiftDerivedCategoryMapDerivedCategoryInt (fdCoefficientTransport l E T)

attribute [local instance] detailedShift

private theorem ambientExactModel_at
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (i : E →ₐ[ℚ_[l]] L) (T : Scheme.{u})
    (φ : pbcAdicCompletion T (pbcIntegralDatum l E) ⟶
      pbcAdicCompletion T (pbcIntegralDatum l L))
    (hφ : φ = pbcScalarCoefficientMap l E L i T)
    [PreservesFiniteLimits (pbcExtend φ)] [PreservesFiniteColimits (pbcExtend φ)] :
    ∃ e : pbcDerivedExtend φ ≅ (pbcExtend φ).mapDerivedCategory,
      (letI : (pbcDerivedRestrict φ).CommShift ℤ :=
        inferInstanceAs ((pbcRestrict φ).mapDerivedCategory.CommShift ℤ)
       letI := (pbcDerivedScalarAdjunction φ).leftAdjointCommShift ℤ
       NatTrans.CommShift e.hom ℤ) ∧
      ∀ P, e.hom.app (DerivedCategory.Q.obj P) ≫
          (pbcExtend φ).mapDerivedCategoryFactors.hom.app P = pbcComplexCounit φ P := by
  subst φ
  exact ambientExactModel l E L i T

/-- The complex comparison induced by the ordinary coefficient-presentation square.
Source: trace-definition coefficient transport, integral step 3
(blueprint: lem-fd-integral-ordinary-scalar-model). -/
private def ordinaryTransportComplex
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (o : FdOrdinaryScalarTransport l Ω T h) :=
  let H : integralTowerModules l (pbcFiniteField.{u} l Ω L) T ⥤
      pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω L))) :=
    fdCoefficientTransport l (pbcFiniteField.{u} l Ω L) T
  letI : H.Additive := fdCoefficientTransportAdditive l (pbcFiniteField.{u} l Ω L) T
  Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex
      (ordinaryScalarModelIso l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T) (.up ℤ))
    (H.mapHomologicalComplex (.up ℤ)) ≪≫ o.complex l Ω

private theorem ordinaryTransportComplex_completion
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (o : FdOrdinaryScalarTransport l Ω T h)
    (P : CochainComplex (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ) :
    (ordinaryTransportComplex l Ω T h o).hom.app P ≫ o.completion l Ω P =
      ((fdCoefficientTransport l (pbcFiniteField.{u} l Ω L) T).mapHomologicalComplex
        (.up ℤ)).map
          ((integralScalarCompletionChain l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).app P) := by
  rw [integralScalarCompletionChain_model]
  exact (cancel_iso_factor _ ((o.complex l Ω).app P) _).trans
    (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω L) T).mapHomologicalComplex
      (.up ℤ)).map_comp _ _).symm

/-- The exact ordinary derived comparison preserves the prescribed ambient shift and
retains its counit equation on each cochain representative.
Source: trace-definition coefficient transport, integral steps 3--4
(blueprint: lem-fd-integral-ordinary-scalar-model).

Proof: finite scalar extension is exact in the completed presentation. Compare its
universal left derived functor with its exact derived functor using their counits.
Essential surjectivity of the homotopy localization reflects shift compatibility;
the unit equation of the scalar adjunction identifies the counit-normalized shift
with the prescribed mate shift. Derive the ordinary coefficient-presentation square,
compose with that normalized comparison, and apply the derived square factor equation.
On complexes the two presentation factors agree degreewise, giving the stated equation.
-/
private theorem ordinaryTransportSquare
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (o : FdOrdinaryScalarTransport l Ω T h) :
    ∃ e : integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T ⋙
        integralDetailedTransport T l (pbcFiniteField.{u} l Ω L) ≅
      integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
        pbcAmbientScalarExtension l Ω T h,
      NatTrans.CommShift e.hom ℤ ∧
      ∀ P : CochainComplex (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (pbcAmbientScalarExtension l Ω T h).map
            ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app P) ≫
          pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
            (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
              (.up ℤ)).obj P) =
        (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
          ((integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h)
              T).mapDerivedCategoryFactors.hom.app P) ≫
        (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω L) T).hom.app
          (((integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h)
              T).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((ordinaryTransportComplex l Ω T h o).hom.app P) := by
  let E' := pbcFiniteField.{u} l Ω E
  let L' := pbcFiniteField.{u} l Ω L
  let i := pbcFiniteFieldInclusion l Ω h
  let φ := pbcCompletedScalarMap l Ω T h
  have hφ : φ = pbcScalarCoefficientMap l E' L' i T :=
    pbcStageCoefficientMap_eq l Ω T h
  have : PreservesFiniteLimits (pbcExtend φ) := by
    rw [hφ]
    exact (scalarExtension_exact l E' L' i T).1
  have : PreservesFiniteColimits (pbcExtend φ) := by
    rw [hφ]
    exact (scalarExtension_exact l E' L' i T).2
  let G : integralTowerModules l E' T ⥤
      pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E')) :=
    fdCoefficientTransport l E' T
  let H : integralTowerModules l L' T ⥤
      pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l L')) :=
    fdCoefficientTransport l L' T
  have : G.Additive := fdCoefficientTransportAdditive l E' T
  have : H.Additive := fdCoefficientTransportAdditive l L' T
  have : PreservesFiniteLimits G := fdCoefficientTransportLimits l E' T
  have : PreservesFiniteLimits H := fdCoefficientTransportLimits l L' T
  have : PreservesFiniteColimits G := fdCoefficientTransportColimits l E' T
  have : PreservesFiniteColimits H := fdCoefficientTransportColimits l L' T
  let q := ordinaryScalarModelIso l E' L' i T
  let c : integralOrdinaryScalar l E' L' i T ⋙ H ≅ G ⋙ pbcExtend φ :=
    Functor.isoWhiskerRight q H ≪≫ o.comparison
  let eD := Functor.mapDerivedCategorySquareIso
    (F₁ := integralOrdinaryScalar l E' L' i T)
    (F₂ := H) (G₁ := G) (G₂ := pbcExtend φ) c
  have hc : NatTrans.CommShift eD.hom ℤ := by
    dsimp only [eD, Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  obtain ⟨a, ha, hn⟩ := ambientExactModel_at l E' L' i T φ hφ
  have he : NatTrans.CommShift
      (eD ≪≫ Functor.isoWhiskerLeft
        (integralDetailedTransport T l E') a.symm).hom ℤ := by
    have hah : NatTrans.CommShift a.hom ℤ := ha
    have hai : NatTrans.CommShift a.inv ℤ := NatTrans.CommShift.of_iso_inv a ℤ
    have haw : NatTrans.CommShift
        (Functor.whiskerLeft G.mapDerivedCategory a.inv) ℤ :=
      by infer_instance
    change NatTrans.CommShift
      (eD.hom ≫ Functor.whiskerLeft G.mapDerivedCategory a.inv) ℤ
    exact NatTrans.CommShift.comp _ _ ℤ
  refine ⟨_, he, ?_⟩
  intro P
  have hs := iso_square_factor a (eD.hom.app (DerivedCategory.Q.obj P))
    (G.mapDerivedCategoryFactors.hom.app P) _ _
    (hn ((G.mapHomologicalComplex (.up ℤ)).obj P))
  have hp := derivedSquare_factors
    (F := integralOrdinaryScalar l E' L' i T)
    (H := H) (G := G) (I := pbcExtend φ) c P
  refine hs.trans (hp.trans ?_)
  congr 2

/-- The ordinary derived scalar square for the prescribed ambient shift, normalized
by the actual completion map on every cochain representative.
Source: trace-definition coefficient transport, integral steps 3--4
(blueprint: lem-fd-integral-ordinary-scalar-model).

Proof: form the exact derived square of the ordinary coefficient comparison and
compare its target scalar functor with the counit-normalized ambient derived functor.
The scalar adjunction unit determines its mate shift uniquely. Retain the derived
factor equation on representatives, compose with ordinary.completion, cancel the
complex comparison and use the intrinsic completion-chain model. Naturality moves
the resulting chain across the target coefficient factor, yielding the equation below.
-/
theorem ordinaryTransportModel
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (o : FdOrdinaryScalarTransport l Ω T h) :
    letI := fdCoefficientTransportLimits l (pbcFiniteField.{u} l Ω E) T
    letI := fdCoefficientTransportColimits l (pbcFiniteField.{u} l Ω E) T
    letI := fdCoefficientTransportLimits l (pbcFiniteField.{u} l Ω L) T
    letI := fdCoefficientTransportColimits l (pbcFiniteField.{u} l Ω L) T
    letI : (integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).CommShift ℤ :=
      Functor.instCommShiftDerivedCategoryMapDerivedCategoryInt
        (fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T)
    letI : (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).CommShift ℤ :=
      Functor.instCommShiftDerivedCategoryMapDerivedCategoryInt
        (fdCoefficientTransport l (pbcFiniteField.{u} l Ω L) T)
    ∃ e : integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T ⋙
        integralDetailedTransport T l (pbcFiniteField.{u} l Ω L) ≅
      integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
        pbcAmbientScalarExtension l Ω T h,
      NatTrans.CommShift e.hom ℤ ∧
      ∀ P : CochainComplex (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (pbcAmbientScalarExtension l Ω T h).map
            ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app P) ≫
          pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
            (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
              (.up ℤ)).obj P) ≫ DerivedCategory.Q.map (o.completion l Ω P) =
        (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
          ((integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h)
              T).mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l (pbcFiniteField.{u} l Ω E)
              (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).app P)) ≫
        (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω L) T).hom.app
          ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj P) := by
  obtain ⟨e, he, hn⟩ := ordinaryTransportSquare l Ω T h o
  refine ⟨e, he, ?_⟩
  intro P
  let E' := pbcFiniteField.{u} l Ω E
  let L' := pbcFiniteField.{u} l Ω L
  let i := pbcFiniteFieldInclusion l Ω h
  let dL := integralDetailedTransport T l L'
  let f := (fdCoefficientTransportFactors l L' T).hom.app
    ((integralScalarComplexFunctor l E' L' i T).obj P)
  have hcomp :
      DerivedCategory.Q.map ((ordinaryTransportComplex l Ω T h o).hom.app P) ≫
        DerivedCategory.Q.map (o.completion l Ω P) =
      DerivedCategory.Q.map
        (((fdCoefficientTransport l L' T).mapHomologicalComplex (.up ℤ)).map
          ((integralScalarCompletionChain l E' L' i T).app P)) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans
      (congrArg DerivedCategory.Q.map (ordinaryTransportComplex_completion l Ω T h o P))
  have hnat :
      (fdCoefficientTransportFactors l L' T).hom.app
          (((integralOrdinaryScalar l E' L' i T).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          (((fdCoefficientTransport l L' T).mapHomologicalComplex (.up ℤ)).map
            ((integralScalarCompletionChain l E' L' i T).app P)) =
      dL.map (DerivedCategory.Q.map
          ((integralScalarCompletionChain l E' L' i T).app P)) ≫ f :=
    ((fdCoefficientTransportFactors l L' T).hom.naturality
      ((integralScalarCompletionChain l E' L' i T).app P)).symm
  have hz := normalization_comp _ _ _ _ _ _ _ _ _ _ (hn P) hcomp hnat
  exact hz.trans ((Category.assoc
    (dL.map ((integralOrdinaryScalar l E' L' i T).mapDerivedCategoryFactors.hom.app P))
    (dL.map (DerivedCategory.Q.map
      ((integralScalarCompletionChain l E' L' i T).app P))) f).symm.trans
      (congrArg (fun v ↦ v ≫ f) (dL.map_comp _ _).symm))

end WeilConjectures.FdIntegralOrdinaryScalarModel
