/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicFiniteDiagramData
public import WeilConjectures.RingTheory.QuotientLevelTor
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLevelConstantRestriction
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import all WeilConjectures.AlgebraicGeometry.Perfect.PerfectChartTensorComparison
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedLocalPerfectCriterion
import WeilConjectures.AlgebraicGeometry.Completed.CompletedRealizationDerivedCohomology
import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The consecutive-quotient Tor sheaf of a constant perfect complex

For a perfect complex `C` over the valuation ring `A`, the degree-`q` cohomology of the
`n+1`-st reduction of its constant realization is the constant sheaf of the module
`M = H^q(C ⊗ A/π^{n+2})`, and the consecutive-quotient Tor sheaf of a constant sheaf is
the constant sheaf of the module-level Tor. A torsion summand `N₀` of `H^q(C)` is a retract
of `M`, which gives the surjection onto `N₀/πN₀`.

## References

* Bhatt--Scholze, Proposition 6.6.11
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

section Sheaf

variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The cohomology of a finite reduction of the constant realization of a perfect complex is
the constant sheaf of the cohomology of the reduced complex. -/
theorem nonempty_reduction_homology_iso (q : ℤ)
    (C : completedConstantDerived (ModuleCat.{u + 1} A))
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (a b : ℤ) (_ha : P.IsStrictlyGE a)
    (hb : P.IsStrictlyLE b)
    (hP : ∀ i, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i))
    (e : C ≅ (completedConstantQ (ModuleCat.{u + 1} A)).obj P) (n : ℕ) :
    Nonempty ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcCompletedReduction T d n).obj ((integralConstantDerived T d).obj C)) ≅
      (pbcRestrict (pbcLevelConstantComparison T d n).inv).obj
        ((adicLisseConstantModules T (A ⧸ d.ideal ^ (n + 1))).obj
          ((((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
            (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).mapHomologicalComplex (.up ℤ)).obj
              P).homology q))) := by
  classical
  let := hb
  let F := adicLisseConstantModules T A
  have : F.Additive := CompletedConstantReduction.constant_additive T A
  let c := CompletedConstantReduction.base T d.ideal ≫ (pbcCompletedComparison T d).hom
  let C₀ := (CompletedConstantReduction.constantComplex T A).obj P
  have : IsIso (pbcComplexCounit c C₀) := by
    have := pbcExtensionCounit_isIso c C₀ (constant_kflat T P b (fun q ↦ (hP q).1))
    dsimp only [pbcComplexCounit]
    infer_instance
  let e₁ : (integralConstantDerived T d).obj C ≅
      (pbcDerivedExtend c).obj (DerivedCategory.Q.obj C₀) :=
    (integralConstantDerived T d).mapIso e ≪≫
      (integralRealizationFactors T d).app P ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (ordinaryConstantModel T d) (.up ℤ)).app P) ≪≫
      (DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (F ⋙ pbcExtend c)) (.up ℤ)).app P)).symm ≪≫
      (asIso (pbcComplexCounit c C₀)).symm
  let := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).left_adjoint_additive
  let p := pbcAdicProjection T d n
  let j := pbcLevelConstantComparison T d n
  let qq := Ideal.Quotient.mk (d.ideal ^ (n + 1))
  let β := (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map (CommRingCat.ofHom qq)
  have hcp : c ≫ p = β ≫ j.hom := by
    dsimp [c, p, pbcAdicProjection, pbcCompletedComparison]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc]
    have hb₀ := (CompletedConstantReduction.base_exists T d.ideal).choose_spec.1 n
    change CompletedConstantReduction.base T d.ideal ≫ _ = _ at hb₀
    rw [hb₀]
    rfl
  have hcpj : c ≫ p ≫ j.inv = β := by
    rw [← Category.assoc, hcp, Category.assoc, j.hom_inv_id, Category.comp_id]
  let C₁ := DerivedCategory.Q.obj C₀
  let eglobal := (restrictIsoAsExtend j).app _ ≪≫
    (pbcDerivedExtend j.inv).mapIso (pbcReductionNormalization c p (c ≫ p) rfl C₁) ≪≫
    pbcReductionNormalization (c ≫ p) j.inv β hcpj C₁ ≪≫
    constantTensorIso T qq P b (fun i ↦ (hP i).1)
  let Fn := adicLisseConstantModules T (A ⧸ d.ideal ^ (n + 1))
  have : Fn.Additive := CompletedConstantReduction.constant_additive T _
  have : PreservesFiniteLimits Fn := (CompletedConstantReduction.constant_exact T _).1
  have : PreservesFiniteColimits Fn := (CompletedConstantReduction.constant_exact T _).2
  let P' := ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} qq).mapHomologicalComplex
    (.up ℤ)).obj P
  let X := (pbcCompletedReduction T d n).obj ((integralConstantDerived T d).obj C)
  let eX : (pbcDerivedRestrict j.hom).obj X ≅ DerivedCategory.Q.obj (Fn.mapHomologicalComplex
      (.up ℤ) |>.obj P') :=
    (pbcDerivedRestrict j.hom).mapIso ((pbcDerivedExtend p).mapIso e₁) ≪≫ eglobal
  let eq := proEtaleScalarEquivalence T ((adicLisseForget T).mapIso j)
  let eH : (pbcRestrict j.hom).obj ((DerivedCategory.homologyFunctor _ q).obj X) ≅
      Fn.obj (P'.homology q) :=
    ((pbcRestrict j.hom).mapDerivedCategoryHomologyFunctorIso q).app X ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso eX ≪≫
      (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
      (Fn.mapHomologicalComplexHomologyIso (.up ℤ) q).app P'
  exact ⟨eq.unitIso.app _ ≪≫ (pbcRestrict j.inv).mapIso eH⟩

/-- The consecutive-quotient Tor sheaf of a constant sheaf is the constant sheaf of the
module-level Tor. -/
theorem nonempty_tor_constant_iso (n : ℕ) (M : ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1 + 1))) :
    Nonempty ((DerivedCategory.homologyFunctor _ (-1)).obj
        ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((pbcRestrict (pbcLevelConstantComparison T d (n + 1)).inv).obj
              ((adicLisseConstantModules T (A ⧸ d.ideal ^ (n + 1 + 1))).obj M)))) ≅
      (pbcRestrict (pbcLevelConstantComparison T d n).inv).obj
        ((adicLisseConstantModules T (A ⧸ d.ideal ^ (n + 1))).obj
          (ModuleCat.levelTor d.ideal n M))) := by
  classical
  let := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).left_adjoint_additive
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))
  let j₁ := pbcLevelConstantComparison T d (n + 1)
  let j := pbcLevelConstantComparison T d n
  let quot := pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)
  let β := (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
  have hβ : (adicLisseRingSystem T d.ideal).map (homOfLE (Nat.le_succ n)).op = β :=
    Functor.ofOpSequence_map_homOfLE_succ _ n
  have hq : quot ≫ j.inv = j₁.inv ≫ β := by
    have h := pbcConstantSystemComparison_naturality T d (homOfLE (Nat.le_succ n)).op
    rw [hβ] at h
    change β ≫ j.hom = j₁.hom ≫ quot at h
    rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, j.hom_inv_id,
      Category.comp_id]
  let Fm := adicLisseConstantModules T (A ⧸ d.ideal ^ (n + 1 + 1))
  have : Fm.Additive := CompletedConstantReduction.constant_additive T _
  have : PreservesFiniteLimits Fm := (CompletedConstantReduction.constant_exact T _).1
  have : PreservesFiniteColimits Fm := (CompletedConstantReduction.constant_exact T _).2
  let Fn := adicLisseConstantModules T (A ⧸ d.ideal ^ (n + 1))
  have : Fn.Additive := CompletedConstantReduction.constant_additive T _
  have : PreservesFiniteLimits Fn := (CompletedConstantReduction.constant_exact T _).1
  have : PreservesFiniteColimits Fn := (CompletedConstantReduction.constant_exact T _).2
  let R := projectiveResolution M
  have hR (i : ℤ) : Module.Projective (A ⧸ d.ideal ^ (n + 1 + 1)) (R.cochainComplex.X i) :=
    (IsProjective.iff_projective _).2 (inferInstanceAs (Projective (R.cochainComplex.X i)))
  let eq₁ := proEtaleScalarEquivalence T ((adicLisseForget T).mapIso j₁)
  let eq := proEtaleScalarEquivalence T ((adicLisseForget T).mapIso j)
  let X := (DerivedCategory.singleFunctor _ 0).obj ((pbcRestrict j₁.inv).obj (Fm.obj M))
  let eS : (DerivedCategory.singleFunctor _ 0).obj M ≅
      DerivedCategory.Q.obj R.cochainComplex :=
    (asIso (DerivedCategory.Q.map R.π')).symm
  let e₁ : (pbcDerivedRestrict j₁.hom).obj X ≅
      DerivedCategory.Q.obj (Fm.mapHomologicalComplex (.up ℤ) |>.obj R.cochainComplex) :=
    ((pbcRestrict j₁.hom).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (eq₁.counitIso.app _) ≪≫
      ((Fm.mapDerivedCategorySingleFunctor 0).app M).symm ≪≫
      Fm.mapDerivedCategory.mapIso eS ≪≫ Fm.mapDerivedCategoryFactors.app _
  let Z := (pbcDerivedExtend quot).obj X
  let eZ : (pbcDerivedRestrict j.hom).obj Z ≅ DerivedCategory.Q.obj
      (Fn.mapHomologicalComplex (.up ℤ) |>.obj (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).mapHomologicalComplex (.up ℤ)).obj
          R.cochainComplex)) :=
    (restrictIsoAsExtend j).app Z ≪≫
      pbcReductionNormalization quot j.inv (j₁.inv ≫ β) hq X ≪≫
      (pbcReductionNormalization j₁.inv β (j₁.inv ≫ β) rfl X).symm ≪≫
      (pbcDerivedExtend β).mapIso (((restrictIsoAsExtend j₁).app X).symm ≪≫ e₁) ≪≫
      constantTensorIso T (Ideal.Quotient.factorPowSucc d.ideal (n + 1)) R.cochainComplex 0 hR
  let eH : (pbcRestrict j.hom).obj ((DerivedCategory.homologyFunctor _ (-1)).obj Z) ≅
      Fn.obj (ModuleCat.levelTor d.ideal n M) :=
    ((pbcRestrict j.hom).mapDerivedCategoryHomologyFunctorIso (-1)).app Z ≪≫
      (DerivedCategory.homologyFunctor _ (-1)).mapIso eZ ≪≫
      (DerivedCategory.homologyFunctorFactors _ (-1)).app _ ≪≫
      (Fn.mapHomologicalComplexHomologyIso (.up ℤ) (-1)).app _
  exact ⟨eq.unitIso.app _ ≪≫ (pbcRestrict j.inv).mapIso eH⟩

/-- Restricting the constant sheaf of `A/I^{n+1} ⊗ X` to the completed coefficients gives
the completed realization of `X`, when `I^{n+1}` kills `X`. -/
theorem nonempty_restrict_level_constant_iso (n : ℕ) (X : ModuleCat.{u + 1} A)
    (hX : ∀ a ∈ d.ideal ^ (n + 1), ∀ x : X, a • x = 0) :
    Nonempty ((pbcRestrict (pbcAdicProjection T d n)).obj
        ((pbcRestrict (pbcLevelConstantComparison T d n).inv).obj
          ((adicLisseConstantModules T (A ⧸ d.ideal ^ (n + 1))).obj
            ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
              (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).obj X))) ≅
      (integralConstantModule T d).obj X) := by
  let f := Ideal.Quotient.mk (d.ideal ^ (n + 1))
  let η := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f).unit.app X
  have : Mono η := by
    obtain ⟨μ, hμ⟩ := ModuleCat.exists_unit_retraction d.ideal (n + 1) X hX
    exact mono_of_mono_fac hμ
  have : Epi η := (ModuleCat.epi_iff_surjective η).2 fun t ↦
    ModuleCat.exists_extendRestrictScalarsAdj_unit_app_eq f Ideal.Quotient.mk_surjective t
  have : IsIso η := isIso_of_mono_of_epi η
  obtain ⟨e⟩ := nonempty_integralConstantModule_restrictScalars_iso T d n
    ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).obj X)
  exact ⟨e.symm ≪≫ (integralConstantModule T d).mapIso (asIso η).symm⟩

end Sheaf

end AlgebraicGeometry.Scheme
