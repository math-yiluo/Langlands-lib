/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientData
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingPullbackFixed
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection
import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.IntegralScalarModelCoordinates
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.Topology.ConstructibleIsRetrocompact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Descent of finite-model quotient cohomology -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ZeroObject
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteModelQuotient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local instance] quotientModuleCategory quotientModuleAbelian quotientModuleDerived

/-- The named homology coordinates have exactly the original conclusion.
This conversion is checked before introducing local irreducibility attributes. -/
private theorem quotient_conclusion_coordinates
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (M : AdicCompletion.Modules l E V)
    (n : ℕ) (hf : Finite (R l E n))
    (enc : ∀ T : Scheme.{u}, Encoding l E n T)
    :
    ((∀ q : ℤ, q ≠ -1 → q ≠ 0 →
      IsZero ((quotientHomology l E n V q).obj (reduction l E V M n))) ∧
    (∀ q : ℤ, IsConstantModelConstructible
      (DerivedNakayama.quotientRing l E (n + 1)) V
      ((quotientHomology l E n V q).obj (reduction l E V M n))) ∧
    (letI := hf
     ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf V
       (ULift.{u + 1} (R l E n))
       ((ordinaryHomology l E n V q).obj
         ((derivedEncoding l E n V (enc V)).functor.obj (reduction l E V M n))))) →
    ((∀ q : ℤ, q ≠ -1 → q ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (reduction l E V M n))) ∧
    (∀ q : ℤ, IsConstantModelConstructible
      (DerivedNakayama.quotientRing l E (n + 1)) V
      ((DerivedCategory.homologyFunctor _ q).obj (reduction l E V M n))) ∧
    (letI := hf
     letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
     ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf V
       (ULift.{u + 1} (R l E n))
       ((DerivedCategory.homologyFunctor _ q).obj
         ((enc V).fixedDerived.functor.obj (reduction l E V M n))))) := by
  intro h
  exact h

attribute [local irreducible] CondensedRing.upperStar finiteConstantScalarExtension
  HasDerivedCategory.standard Mod.extendScalars Functor.mapDerivedCategory
  upperStarFromPoint pointUpperStar reduction differential

private theorem integral_constructible_charts
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (M : AdicCompletion.Modules l E V)
    (hM : IsConstantModelConstructible (DerivedNakayama.integerRing l E) V M) :
    ∃ S : Scheme.Stratification V,
      ∃ C : ∀ i : Fin S.n,
          Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain i),
        ∀ (i : Fin S.n) (j : (C i).I₀),
          ∃ P : ModuleCat.{u + 1} (A l E), Module.FinitePresentation (A l E) P ∧
            Nonempty ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
              ((C i).f j ≫ S.immersion i)).obj M ≅ model l E ((C i).X j) P) := by
  have hV : CompactSpace V ∧ QuasiSeparatedSpace V := ⟨inferInstance, inferInstance⟩
  obtain ⟨S, hS⟩ : IsFiniteConstantStratified (DerivedNakayama.integerRing l E) V M := by
    simpa only [IsConstantModelConstructible, ite_eq_left hV] using hM
  have hcover (i : Fin S.n) :=
    (finiteConstantLocalModel_iff_exists_cover (DerivedNakayama.integerRing l E) _).mp (hS i)
  choose C hC using hcover
  refine ⟨S, C, fun i j ↦ ?_⟩
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := hC i j
  obtain ⟨P, hP, ⟨eP⟩⟩ := integral_scalar_model_coordinates l E ((C i).X j) Q hQ
  exact ⟨P, hP, ⟨((CondensedRing.upperStarComp (DerivedNakayama.integerRing l E)
    ((C i).f j) (S.immersion i)).app M) ≪≫ eQ ≪≫ eP⟩⟩

private theorem integral_matrix (a b : ℕ)
    (f : FiniteConstantModel.freeScalars (A l E) a ⟶
      FiniteConstantModel.freeScalars (A l E) b) :
    ∃ v : Matrix (Fin b) (Fin a) (A l E), integralDifferential l E a b v = f := by
  classical
  let ca := LinearEquiv.piCongrRight fun _ : Fin a ↦
    (ULift.moduleEquiv : ULift.{u + 1} (A l E) ≃ₗ[A l E] A l E)
  let cb := LinearEquiv.piCongrRight fun _ : Fin b ↦
    (ULift.moduleEquiv : ULift.{u + 1} (A l E) ≃ₗ[A l E] A l E)
  let g := cb.toLinearMap.comp (f.hom.comp ca.symm.toLinearMap)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  apply ModuleCat.hom_ext
  change cb.symm.toLinearMap.comp
    ((Matrix.toLin' (LinearMap.toMatrix' g)).comp ca.toLinearMap) = f.hom
  rw [Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  change cb.symm (cb (f.hom (ca.symm (ca x)))) = f.hom x
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

private theorem scalar_resolution (P : ModuleCat.{u + 1} (A l E))
    (hP : Module.FinitePresentation (A l E) P) :
    ∃ (a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E))
      (w : ModuleCat.of (A l E) (Fin b → ULift.{u + 1} (A l E)) ⟶ P),
      Function.Injective (integralDifferential l E a b v).hom ∧
      Function.Exact (integralDifferential l E a b v).hom w.hom ∧
      Function.Surjective w.hom := by
  have := hP
  have : IsPrincipalIdealRing (A l E) := by
    have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
    exact h.2.2.2.2.2.2.2.2.1
  obtain ⟨a, b, f, w, hi, he, hs⟩ := FiniteConstantModel.scalar_resolution (A l E) P
  obtain ⟨v, hv⟩ := integral_matrix l E a b f
  exact ⟨a, b, v, w, hv ▸ hi, hv ▸ he, hs⟩

private theorem ordinary_complex_zero (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) (q : ℤ) (h₁ : q ≠ -1) (h₀ : q ≠ 0) :
    IsZero ((ordinaryHomology l E n T q).obj
      (ordinaryComplex l E T n a b v)) := by
  dsimp only [ordinaryHomology]
  dsimp only [ordinaryComplex]
  let F := constantSheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))
  let K := scalarComplex l E n a b v
  have hz : IsZero (K.X q) :=
    HomologicalComplex.isZero_double_X _ _ q h₁ h₀
  have hH : IsZero (K.homology q) := (K.sc q).isZero_homology_of_isZero_X₂ hz
  exact (F.map_isZero hH).of_iso
    ((DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
      (F.mapHomologicalComplexHomologyIso (.up ℤ) q).app K)

private theorem ordinary_cover_zero (B : Type (u + 1)) [CommRing B]
    {T : Scheme.{u}} (C : Scheme.Cover.{u} Scheme.proetalePrecoverage T)
    (H : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B))
    (h : ∀ i, IsZero ((upperStar (ModuleCat.{u + 1} B) (C.f i)).obj H)) :
    IsZero H := by
  rw [IsZero.iff_id_eq_zero]
  have (i : C.I₀) : WeaklyEtale (C.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk i)
  have : IsIso (0 : H ⟶ H) := by
    refine isIso_of_isIso_localizationRestriction (ModuleCat.{u + 1} B) (0 : H ⟶ H)
      C.f C.mem₀ fun i ↦ ?_
    apply (NatIso.isIso_map_iff
      (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B)
        (C.f i) inferInstance) _).1
    exact isIso_of_source_target_iso_zero _ (h i).isoZero (h i).isoZero
  exact (cancel_mono (0 : H ⟶ H)).mp (by simp)

private theorem ordinary_strata_zero (B : Type (u + 1)) [CommRing B]
    {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (S : Scheme.Stratification T)
    (H : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B))
    (h : ∀ i, IsZero ((upperStar (ModuleCat.{u + 1} B) (S.immersion i)).obj H)) :
    IsZero H := by
  have (i : Fin S.n) : IsImmersion (S.immersion i) := S.isImmersion i
  have (i : Fin S.n) : CompactSpace (S.domain i) := by
    rw [← isCompact_univ_iff]
    apply (S.immersion i).isEmbedding.isCompact_iff.mpr
    simpa only [Set.image_univ, S.range_immersion, Set.inter_univ] using
      (S.isConstructible_stratum i).isRetrocompact isCompact_univ isOpen_univ
  have (i : Fin S.n) : QuasiCompact (S.immersion i) := inferInstance
  rw [IsZero.iff_id_eq_zero]
  apply eq_zero_of_forall_upperStar_map_eq_zero B S.immersion
  · intro x
    have hx : x ∈ ⋃ i, S.stratum i := by rw [S.iUnion_stratum_eq_univ]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, (S.range_immersion i).symm ▸ hi⟩
  · intro i
    exact (h i).eq_of_src _ _

private theorem intrinsic_of_ordinary_stratified (B : Type u) [CommRing B] [Finite B]
    (V : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} B)))
    (hF : FiniteDiscreteOrdinary.ordinaryStratified B V F) :
    Scheme.IsConstructibleProEtaleFixedModuleSheaf V (ULift.{u + 1} B) F := by
  obtain ⟨S, hS⟩ := hF
  have h : ProEtale.IsConstructible (ULift.{u + 1} B) F :=
    ⟨S, fun i ↦ (FiniteDiscreteOrdinary.localModel_iff_finiteLocal B _ _).mp (hS i)⟩
  obtain ⟨S, hn, hS⟩ := Scheme.positive_stratification V (ULift.{u + 1} B) F h
  have hS' (i : Fin S.n) : ∃ (ι : Type (u + 1)) (W : ι → Scheme.{u})
      (g : ∀ j, W j ⟶ S.domain i), Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage _ ∧
        ∀ j, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1} B), Finite M ∧
          Nonempty (((g j)^*[ModuleCat.{u + 1} (ULift.{u + 1} B)]).obj
              ((S.immersion i)^*[ModuleCat.{u + 1} (ULift.{u + 1} B)].obj F) ≅
            (constantSheaf (Scheme.ProEt.topology (W j)) _).obj M) := by
    obtain ⟨ι, W, g, hg, h⟩ := hS i
    refine ⟨ι, W, g, hg, fun j ↦ ?_⟩
    obtain ⟨M, hM, e⟩ := h j
    exact ⟨M, Module.finite_of_finite (ULift.{u + 1} B), e⟩
  refine ⟨S, hn, S.isConstructible_stratum, fun i ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨I, U, f, hf, he⟩ := finiteModels_over (ULift.{u + 1} B) _ (hS' i)
    exact ⟨I, U, f, hf, fun j ↦ ⟨(he j).choose, (he j).choose_spec.2⟩⟩
  · exact finite_geometricStalk_of_finite_models (ULift.{u + 1} B) _ (hS' i)

set_option backward.isDefEq.respectTransparency true in
private theorem exact_comparison
    {C D H : Type*} [Category C] [Category D] [Category H]
    [Abelian C] [Abelian D] [Abelian H]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory H]
    (F : C ⥤ D) (G : D ⥤ H) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (L : DerivedCategory C ⥤ DerivedCategory D) (hL : L ≅ F.mapDerivedCategory)
    (K : DerivedCategory C) (q : ℤ) :
    Nonempty (G.obj (F.obj ((DerivedCategory.homologyFunctor _ q).obj K)) ≅
      (DerivedCategory.homologyFunctor _ q).obj (G.mapDerivedCategory.obj (L.obj K))) := by
  exact ⟨G.mapIso ((F.mapDerivedCategoryHomologyFunctorIso q).app K) ≪≫
    (G.mapDerivedCategoryHomologyFunctorIso q).app (F.mapDerivedCategory.obj K) ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso (G.mapDerivedCategory.mapIso
      (hL.app K).symm)⟩

private instance quotient_upper_star_additive (n : ℕ) {V T : Scheme.{u}}
    (f : T ⟶ V) : (quotientUpperStar l E n f).Additive := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact CondensedRing.upperStar_additive (FiniteDiscreteOrdinary.coefficient (R l E n)) f

private instance quotient_upper_star_limits (n : ℕ) {V T : Scheme.{u}}
    (f : T ⟶ V) : PreservesFiniteLimits (quotientUpperStar l E n f) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact CondensedRing.preservesFiniteLimits_upperStar
    (FiniteDiscreteOrdinary.coefficient (R l E n)) f

private instance quotient_upper_star_colimits (n : ℕ) {V T : Scheme.{u}}
    (f : T ⟶ V) : PreservesFiniteColimits (quotientUpperStar l E n f) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact CondensedRing.preservesFiniteColimits_upperStar
    (FiniteDiscreteOrdinary.coefficient (R l E n)) f

private instance fixed_encoding_additive (n : ℕ) (T : Scheme.{u})
    (e : Encoding l E n T) : (fixedEncoding l E n T e).functor.Additive := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  change (e.ordinary.functor ⋙ e.fixed.functor).Additive
  infer_instance

private def derived_encoding_iso (n : ℕ) (T : Scheme.{u}) (e : Encoding l E n T) :
    (derivedEncoding l E n T e).functor ≅
      (fixedEncoding l E n T e).functor.mapDerivedCategory := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact Iso.refl _

set_option backward.isDefEq.respectTransparency true in
private theorem quotient_pullback_homology
    (n : ℕ) {V T : Scheme.{u}} (f : T ⟶ V) (e : Encoding l E n T)
    (K : DerivedCategory (quotientModules l E n V)) (q : ℤ) :
    Nonempty ((fixedEncoding l E n T e).functor.obj
      ((quotientUpperStar l E n f).obj
        ((quotientHomology l E n V q).obj K)) ≅
    (ordinaryHomology l E n T q).obj
      ((derivedEncoding l E n T e).functor.obj
        ((quotientPullback l E n f).obj K))) := by
  dsimp only [ordinaryHomology]
  dsimp only [quotientHomology]
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let F := quotientUpperStar l E n f
  let G := (fixedEncoding l E n T e).functor
  let L := quotientPullback l E n f
  refine ⟨(exact_comparison F G L
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
      (FiniteDiscreteOrdinary.coefficient (R l E n)) f) K q).some ≪≫ ?_⟩
  exact (ordinaryHomology l E n T q).mapIso
    ((derived_encoding_iso l E n T e).app (L.obj K)).symm

set_option backward.isDefEq.respectTransparency true in
private theorem internal_complex_encoded
    (T : Scheme.{u}) (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E))
    (e : Encoding l E n T) :
    Nonempty ((derivedEncoding l E n T e).functor.obj (internalComplex l E T n a b v e) ≅
      ordinaryComplex l E T n a b v) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact ⟨(derivedEncoding l E n T e).counitIso.app _⟩

set_option backward.isDefEq.respectTransparency true in
private theorem encoded_homology
    (n : ℕ) (T : Scheme.{u}) (e : Encoding l E n T)
    (K : DerivedCategory (quotientModules l E n T)) (q : ℤ) :
    Nonempty ((fixedEncoding l E n T e).functor.obj
      ((quotientHomology l E n T q).obj K) ≅
      (ordinaryHomology l E n T q).obj ((derivedEncoding l E n T e).functor.obj K)) := by
  dsimp only [ordinaryHomology]
  dsimp only [quotientHomology]
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact ⟨(((fixedEncoding l E n T e).functor.mapDerivedCategoryHomologyFunctorIso q).app K) ≪≫
    (ordinaryHomology l E n T q).mapIso
      ((derived_encoding_iso l E n T e).app K).symm⟩

attribute [local irreducible] internalComplex ordinaryComplex
  FiniteDiscreteOrdinary.Encoding.fixedDerived CondensedRing.moduleObjectDerivedPullback
  fixedEncoding derivedEncoding

private theorem quotient_stratified_comparison
    (n : ℕ) (hf : Finite (R l E n))
    (hd : @DiscreteTopology (R l E n) (AdicCompletion.finiteTopology l E (n + 1)))
    (T : Scheme.{u}) (e : Encoding l E n T)
    (H : quotientModules l E n T) :
    IsFiniteConstantStratified (DerivedNakayama.quotientRing l E (n + 1)) T H ↔
      FiniteDiscreteOrdinary.ordinaryStratified (R l E n) T
        ((fixedEncoding l E n T e).functor.obj H) := by
  let := hf
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : DiscreteTopology (R l E n) := hd
  unfold fixedEncoding
  exact FiniteDiscreteOrdinary.stratified_comparison (R l E n) T e H

private theorem quotient_encoding_pullback (n : ℕ)
    {V T : Scheme.{u}} (f : T ⟶ V) (eV : Encoding l E n V) (eT : Encoding l E n T)
    (H : quotientModules l E n V)
    (hf : Finite (R l E n))
    (hd : @DiscreteTopology (R l E n) (AdicCompletion.finiteTopology l E (n + 1))) :
    Nonempty ((fixedEncoding l E n T eT).functor.obj
      ((quotientUpperStar l E n f).obj H) ≅
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n))) f).obj
        ((fixedEncoding l E n V eV).functor.obj H)) := by
  let := hf
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : DiscreteTopology (R l E n) := hd
  unfold fixedEncoding quotientUpperStar
  exact FiniteDiscreteOrdinary.encoding_pullback_fixed (R l E n) f eV eT H

/-- The literal scalar cohomology model of the two-term matrix complex. -/
private def scalarCohomologyModel (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) (q : ℤ) :
    ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)) :=
  if q = -1 then kernel (differential l E n a b v)
  else if q = 0 then cokernel (differential l E n a b v)
  else ModuleCat.of (ULift.{u + 1} (R l E n)) PUnit.{u + 2}

private theorem chart_model (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) (e : Encoding l E n T)
    (D : DerivedCategory (quotientModules l E n T))
    (h : ChartCalculation l E T n a b v e D) (q : ℤ) :
    Finite (scalarCohomologyModel l E n a b v q) ∧
      Nonempty ((ordinaryHomology l E n T q).obj
        ((derivedEncoding l E n T e).functor.obj D) ≅
        (constantSheaf (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
            (scalarCohomologyModel l E n a b v q)) ∧
      (q ≠ -1 → q ≠ 0 → IsZero (scalarCohomologyModel l E n a b v q)) := by
  classical
  by_cases h₁ : q = -1
  · subst q
    simpa only [scalarCohomologyModel, ite_eq_left rfl, ite_true] using
      (show Finite ↥(kernel (differential l E n a b v)) ∧
        Nonempty ((ordinaryHomology l E n T (-1)).obj
          ((derivedEncoding l E n T e).functor.obj D) ≅
          (constantSheaf (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
              (kernel (differential l E n a b v))) ∧
        ((-1 : ℤ) ≠ -1 → (-1 : ℤ) ≠ 0 →
          IsZero (kernel (differential l E n a b v))) from
        ⟨h.finiteKernel, h.kernelModel, fun hn ↦ (hn rfl).elim⟩)
  by_cases h₀ : q = 0
  · subst q
    simpa only
    [scalarCohomologyModel, ite_eq_right (by decide : (0 : ℤ) ≠ -1), ite_eq_left rfl, ite_true]
      using (show Finite ↥(cokernel (differential l E n a b v)) ∧
        Nonempty ((ordinaryHomology l E n T 0).obj
          ((derivedEncoding l E n T e).functor.obj D) ≅
          (constantSheaf (Scheme.ProEt.topology T)
            (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
              (cokernel (differential l E n a b v))) ∧
        ((0 : ℤ) ≠ -1 → (0 : ℤ) ≠ 0 →
          IsZero (cokernel (differential l E n a b v))) from
        ⟨h.finiteCokernel, h.cokernelModel, fun _ hn ↦ (hn rfl).elim⟩)
  have hZ : IsZero (scalarCohomologyModel l E n a b v q) := by
    simp only [scalarCohomologyModel, ite_eq_right h₁, ite_eq_right h₀]
    exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  have hF : Finite (scalarCohomologyModel l E n a b v q) := by
    simp only [scalarCohomologyModel, ite_eq_right h₁, ite_eq_right h₀]
    infer_instance
  have hz : IsZero ((ordinaryHomology l E n T q).obj
      ((derivedEncoding l E n T e).functor.obj D)) := by
    apply (ordinary_complex_zero l E T n a b v q h₁ h₀).of_iso
    exact (ordinaryHomology l E n T q).mapIso
      ((derivedEncoding l E n T e).functor.mapIso h.complex.some ≪≫
        (internal_complex_encoded l E T n a b v e).some)
  exact ⟨hF, ⟨hz.iso ((constantSheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).map_isZero hZ)⟩,
    fun _ _ ↦ hZ⟩

/-- Descent of the local finite quotient calculation to cohomology sheaves.

Source: blueprint latest, ctf-equals-bc, Locality and Strata; Stacks Tag 09AJ
(blueprint: lem-sfb-finite-model-quotient-cohomology-descent).

Proof: choose the finite constructible stratification and pro-etale covers given
by hM. Express each scalar model by a finite presentation over the integral DVR,
whose kernel is finite free, and apply hcalc to that scalar resolution. The local
two-term calculation vanishes outside degrees -1 and 0. Exact inverse image
commutes with cohomology. On a cover member, module pullback agrees with localized
site restriction, so the sheaf cover-local isomorphism criterion descends this
vanishing to each stratum. Constructible strata in a qcqs scheme have quasi-compact
immersions. The proved
finite quasi-compact jointly surjective module pullback detection theorem therefore
descends vanishing from the strata, including an empty family over the empty scheme.
For degrees -1 and 0 retain the original strata and covers. Their cohomology is
constant with finite scalar kernel and cokernel by hcalc. The normalized finite
coefficient encoding and its pullback comparison turn these into internal finite
scalar models. They give internal constructibility. In ordinary coordinates the
same covers give local constancy and finite geometric stalks, hence intrinsic
constructibility. If the partition has no strata, V is empty; use its one-stratum
empty partition for the positive-length intrinsic predicate. For every other degree
use the zero scalar model. This argument
needs no Noetherianity or completeness assumption.
-/
theorem cohomology_descent
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (M : AdicCompletion.Modules l E V)
    (hM : IsConstantModelConstructible (DerivedNakayama.integerRing l E) V M)
    (n : ℕ) (hf : Finite (R l E n))
    (hd : @DiscreteTopology (R l E n) (AdicCompletion.finiteTopology l E (n + 1)))
    (enc : ∀ T : Scheme.{u}, Encoding l E n T)
    (hcalc : LocalCalculation l E V M n enc) :
    (∀ q : ℤ, q ≠ -1 → q ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (reduction l E V M n))) ∧
    (∀ q : ℤ, IsConstantModelConstructible
      (DerivedNakayama.quotientRing l E (n + 1)) V
      ((DerivedCategory.homologyFunctor _ q).obj (reduction l E V M n))) ∧
    (letI := hf
     letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
     ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf V
       (ULift.{u + 1} (R l E n))
       ((DerivedCategory.homologyFunctor _ q).obj
         ((enc V).fixedDerived.functor.obj (reduction l E V M n)))) := by
  apply quotient_conclusion_coordinates l E V M n hf enc
  classical
  let := hf
  let Λ := DerivedNakayama.quotientRing l E (n + 1)
  change LocalCalculationAt l E V M n enc (reduction l E V M n) at hcalc
  generalize hK : reduction l E V M n = K at hcalc ⊢
  have hV : CompactSpace V ∧ QuasiSeparatedSpace V := ⟨inferInstance, inferInstance⟩
  obtain ⟨S, C, hC⟩ := integral_constructible_charts l E V M hM
  have hcharts (i : Fin S.n) (j : (C i).I₀) (q : ℤ) :
      ∃ P : ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)),
        Finite P ∧ Nonempty
          ((fixedEncoding l E n ((C i).X j) (enc ((C i).X j))).functor.obj
            ((quotientUpperStar l E n ((C i).f j ≫ S.immersion i)).obj
              ((quotientHomology l E n V q).obj K)) ≅
            (constantSheaf (Scheme.ProEt.topology ((C i).X j))
              (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj P) ∧
        (q ≠ -1 → q ≠ 0 → IsZero P) := by
    obtain ⟨P, hP, ⟨eM⟩⟩ := hC i j
    obtain ⟨a, b, v, w, hinj, hex, hsurj⟩ := scalar_resolution l E P hP
    have hlocal := hcalc.chart S C i j P hP eM a b v w hinj hex hsurj
    obtain ⟨hF, ⟨eH⟩, hz⟩ := chart_model l E ((C i).X j) n a b v
      (enc ((C i).X j)) _ hlocal q
    exact ⟨scalarCohomologyModel l E n a b v q, hF,
      ⟨(quotient_pullback_homology l E n ((C i).f j ≫ S.immersion i)
        (enc ((C i).X j)) K q).some ≪≫ eH⟩, hz⟩
  let B := ULift.{u + 1} (R l E n)
  let G := (fixedEncoding l E n V (enc V)).functor
  have hordinary (i : Fin S.n) (j : (C i).I₀) (q : ℤ) :
      ∃ P : ModuleCat.{u + 1} B, Finite P ∧ Nonempty
        ((upperStar (ModuleCat.{u + 1} B) ((C i).f j ≫ S.immersion i)).obj
          (G.obj ((quotientHomology l E n V q).obj K)) ≅
        (constantSheaf (Scheme.ProEt.topology ((C i).X j))
          (ModuleCat.{u + 1} B)).obj P) ∧ (q ≠ -1 → q ≠ 0 → IsZero P) := by
    obtain ⟨P, hP, ⟨eP⟩, hz⟩ := hcharts i j q
    exact ⟨P, hP, ⟨(quotient_encoding_pullback l E n
      ((C i).f j ≫ S.immersion i) (enc V) (enc ((C i).X j)) _ hf hd).some.symm ≪≫ eP⟩,
      hz⟩
  have hvan (q : ℤ) (h₁ : q ≠ -1) (h₀ : q ≠ 0) :
      IsZero ((quotientHomology l E n V q).obj K) := by
    apply IsZero.of_full_of_faithful_of_isZero G
    apply ordinary_strata_zero B S
    intro i
    apply ordinary_cover_zero B (C i)
    intro j
    obtain ⟨P, hP, ⟨eP⟩, hz⟩ := hordinary i j q
    have hzero := ((constantSheaf (Scheme.ProEt.topology ((C i).X j))
      (ModuleCat.{u + 1} B)).map_isZero (hz h₁ h₀)).of_iso eP
    exact hzero.of_iso ((upperStarComp (ModuleCat.{u + 1} B)
      ((C i).f j) (S.immersion i)).app _).symm
  have hord (q : ℤ) : FiniteDiscreteOrdinary.ordinaryStratified (R l E n) V
      (G.obj ((quotientHomology l E n V q).obj K)) := by
    refine ⟨S, fun i ↦ ⟨C i, fun j ↦ ?_⟩⟩
    obtain ⟨P, hP, ⟨eP⟩, _⟩ := hordinary i j q
    exact ⟨P, hP, ⟨((upperStarComp (ModuleCat.{u + 1} B)
      ((C i).f j) (S.immersion i)).app _).symm ≪≫ eP⟩⟩
  have hcons (q : ℤ) : IsConstantModelConstructible Λ V
      ((quotientHomology l E n V q).obj K) := by
    rw [IsConstantModelConstructible, ite_eq_left hV]
    exact (quotient_stratified_comparison l E n hf hd V (enc V) _).mpr (hord q)
  refine ⟨hvan, hcons, fun q ↦ ?_⟩
  have he := (encoded_homology l E n V (enc V) K q).some
  exact intrinsic_of_ordinary_stratified (R l E n) V _
    ((FiniteDiscreteOrdinary.stratified_iso (R l E n) V he).mp (hord q))

end AlgebraicGeometry.ProEtale.FiniteModelQuotient
