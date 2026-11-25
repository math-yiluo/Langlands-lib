/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import WeilConjectures.AlgebraicGeometry.AdicFiniteCompletionTower
import WeilConjectures.AlgebraicGeometry.AdicFiniteTopRoosEpi
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # AdicFiniteCompletionBounds
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

private theorem tor_cohomology_bounds
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (R : Sheaf T CommRingCat.{w}) (K : ConstantCompletion.D R) (a b : ℤ)
    (hK : HasCoefficientModelTorAmplitude R K a b) (q : ℤ) (hq : q < a ∨ b < q) :
    IsZero ((coefficientModelCohomology R q).obj K) := by
  let := HasDerivedCategory.standard (Mod R)
  let L := (ConstantCompletion.Q R).objPreimage K
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients L
  have : QuasiIso p := hp
  let e : (ConstantCompletion.Q R).obj P ≅ K :=
    asIso ((ConstantCompletion.Q R).map p) ≪≫
      (ConstantCompletion.Q R).objObjPreimageIso K
  have hz := hK.2 P hP ⟨e⟩ (SheafOfModules.unit (siteModuleRings R)) q hq
  have hpz : IsZero (P.homology q) := hz.of_iso
    ((HomologicalComplex.homologyFunctor (Mod R) (.up ℤ) q).mapIso
      (ringedKoszulRightUnitIso R P)).symm
  exact hpz.of_iso ((coefficientModelCohomology R q).mapIso e.symm ≪≫
    (DerivedCategory.homologyFunctorFactors (Mod R) q).app P)

private theorem model_exact_products (X : Scheme.{u})
    (R : Sheaf (coefficientProEtaleModelTopology.{u, v} X)
      RingCat.{max v (u + 1)}) :
    HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{max v (u + 1)} R) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let e := (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt))
  let : e.functor.IsContinuous (ProEt.topology X) T :=
    coefficientProEtaleModelUp_isContinuous X
  let : e.inverse.IsContinuous T (ProEt.topology X) := by
    change AsSmall.down.IsContinuous T (ProEt.topology X)
    infer_instance
  let F : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X := AsSmall.up
  let S := (F.sheafPushforwardContinuous RingCat.{max v (u + 1)} (ProEt.topology X) T).obj R
  let E : SheafOfModules.{max v (u + 1)} R ≌ SheafOfModules.{max v (u + 1)} S :=
    SheafOfModules.pushforwardPushforwardEquivalence (S := S) (R := R) e (𝟙 S) (𝟙 R)
      (by ext U; dsimp [e, AsSmall.equiv]; erw [R.obj.map_id]; rfl)
      (by ext U; dsimp [e, AsSmall.equiv]; erw [S.obj.map_id]; rfl)
  have : HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{max v (u + 1)} S) :=
    ProEt.products_exact.{u, v, 0} X S ℕ
  exact HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) E.symm

private theorem underlying_cohomology_bounds
    (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A) (a b : ℤ)
    (hTor : ∀ n : ℕ, HasCoefficientProEtaleTorAmplitude.{u, v} X (adicFiniteCoeff J n)
      (adicFiniteReduction.{u, v} X J N n) a b)
    (n : ℕ) (q : ℤ) (hq : q < a ∨ b < q) :
    IsZero ((coefficientModelCohomology
      (constant (coefficientProEtaleModelTopology.{u, v} X) A) q).obj
        (adicFiniteUnderlying.{u, v} X J N n)) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let f := quotient T A J n
  let := HasDerivedCategory.standard (Mod (constant T A))
  let := HasDerivedCategory.standard (Mod (finite T A J n))
  have := (siteRestrictScalars_exact f).1
  have := (siteRestrictScalars_exact f).2
  have hz := tor_cohomology_bounds (constant T (adicFiniteCoeff J n))
    (adicFiniteReduction.{u, v} X J N n) a b (hTor n) q hq
  exact ((res f).map_isZero hz).of_iso
    (((res f).mapDerivedCategoryHomologyFunctorIso q).symm.app _)

/-- A complete complex with uniformly bounded quotient Tor tests is the derived
limit of its normalized reduction tower and has the same cohomology bounds.
Source: Stacks Project, proetale.tex, Tag 09C2 (1), using lemma-naive-completion.
(auxiliary; not a blueprint node).

Proof: Choose a flat-term K-flat representative P of N. The completion
reflector on constant coefficients computes completion as the derived limit of
P tensor A/J^(n+1). Its unit is invertible on a complete object. The normalized
derived tensor unit, restriction composition and balancing comparisons identify
the quotient transitions with adicFiniteTransition, so this gives the stated
IsDerivedLimit, including existence of the product. Testing the nth Tor bound
against its coefficient ring bounds each reduction in [a,b]. Tensor the exact
sequence 0 -> J^(n+1)/J^(n+2) -> A/J^(n+2) -> A/J^(n+1) -> 0 with P.
The first tensor is the residue reduction tested against the displayed
A/J-module. Its cohomology vanishes above b, so H^b of each tower transition
is epic. Exact countable pro-etale products and the strict Roos comparison
identify the derived limit with the shifted cone of 1 minus transition.
The Milnor sequence has zero outer terms outside [a,b], except possibly its
R^1 limit term at b+1. That term vanishes by the epimorphic-tower theorem.
Transport along the completion isomorphism gives the stated cohomology bound.
This also covers J=0, J=A, the zero complex and an empty scheme. -/
theorem adicFiniteCompletion_bounds
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A)
    (hcomplete : adicFiniteComplete.{u, v} X A J N)
    (a b : ℤ)
    (hTor : ∀ n : ℕ, HasCoefficientProEtaleTorAmplitude.{u, v} X (adicFiniteCoeff J n)
      (adicFiniteReduction.{u, v} X J N n) a b) :
    (∃ hp : HasProduct (adicFiniteUnderlying.{u, v} X J N),
      @IsDerivedLimit _ _ _ _ _ _ _ _ hp (adicFiniteTransition.{u, v} X J N) N) ∧
    (∀ q : ℤ, (q < a ∨ b < q) → IsZero ((coefficientModelCohomology
      (constant (coefficientProEtaleModelTopology.{u, v} X) A) q).obj N)) := by
  classical
  let T := coefficientProEtaleModelTopology.{u, v} X
  let R := constant T A
  let B := Mod R
  let := HasDerivedCategory.standard B
  obtain ⟨hp, p, δ, hlim⟩ := adicFiniteCompletion_tower X A J N
  let := hp
  obtain ⟨r, generators, hgen⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing J)
  obtain ⟨_, _, _, _, hunit⟩ := koszul_quotient_reflector T A J false r generators hgen
  have hu : IsIso ((completionUnit T A J false).app N) := (hunit N).mpr hcomplete
  let e : N ≅ (completion T A J false).obj N :=
    asIso ((completionUnit T A J false).app N)
  let pN := e.hom ≫ p
  let δN := δ ≫ (shiftFunctor _ (1 : ℤ)).map e.inv
  let TN : Triangle (adicFiniteAmbient.{u, v} X A) := Triangle.mk pN
    (towerTransitionEndomorphism (adicFiniteTransition.{u, v} X J N)) δN
  let TC := Pretriangulated.Triangle.mk p
    (towerTransitionEndomorphism (adicFiniteTransition.{u, v} X J N)) δ
  have hTN : TN ∈ distTriang _ := by
    exact Pretriangulated.isomorphic_distinguished TC hlim TN
      (Pretriangulated.Triangle.isoMk TN TC e (Iso.refl _) (Iso.refl _)
        (by simp [TN, TC, pN]) (by simp [TN, TC]) (by
          change (δ ≫ (shiftFunctor _ (1 : ℤ)).map e.inv) ≫
            (shiftFunctor _ (1 : ℤ)).map e.hom = 𝟙 _ ≫ δ
          rw [Category.assoc, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]
          simp))
  refine ⟨⟨hp, pN, δN, hTN⟩, ?_⟩
  have : HasExactLimitsOfShape (Discrete ℕ) B := model_exact_products X (siteModuleRings R)
  have : CountableAB4Star B := CountableAB4Star.of_hasExactLimitsOfShape_nat B
  have hH (q : ℤ) : PreservesLimitsOfShape (Discrete ℕ)
      (coefficientModelCohomology R q) :=
    (derivedCategory_countableProducts_core B).choose_spec.2 ℕ q
  have hzero (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((coefficientModelCohomology R q).obj
        (∏ᶜ adicFiniteUnderlying.{u, v} X J N)) := by
    have := hH q
    apply (isLimitOfHasProductOfPreservesLimit
      (coefficientModelCohomology R q) (adicFiniteUnderlying.{u, v} X J N)).isZero_pt
    apply Functor.isZero
    intro n
    exact underlying_cohomology_bounds X A J N a b hTor n.as q hq
  have htop := adicFiniteTop_roos_epi X A J N a b (hTor 0)
  intro q hq
  by_cases hqtop : q = b + 1
  · subst q
    have hd := DerivedCategory.HomologySequence.comp_δ TN hTN b (b + 1) rfl
    have : Epi ((coefficientModelCohomology R b).map TN.mor₂) := htop
    have hex := DerivedCategory.HomologySequence.exact₁ TN hTN b (b + 1) rfl
    apply hex.isZero_of_both_zeros
    · exact (cancel_epi ((coefficientModelCohomology R b).map TN.mor₂)).mp
        (by simpa using hd)
    · exact (hzero (b + 1) hq).eq_zero_of_tgt _
  · have hex := DerivedCategory.HomologySequence.exact₁ TN hTN (q - 1) q (by omega)
    exact hex.isZero_of_both_isZero (hzero (q - 1) (by omega)) (hzero q hq)

end AlgebraicGeometry.Scheme
