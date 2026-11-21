import Langlands.Representation.Plancherel.ActualCommonLeviV3GenericLocus
import Langlands.Representation.Plancherel.FractionMultiplicativeDifferences
import Langlands.Representation.Plancherel.LaurentBlockPrimeDivisors
import Langlands.Representation.Plancherel.LaurentRankOnePrimeDivisors
import Langlands.Representation.Plancherel.RationalRankOneAmbientRegularity
import Langlands.Representation.Plancherel.RationalUnitaryBasisCancellation
import Langlands.Representation.Plancherel.UnramifiedNormalizedModels

/-! # Unitary regularity from finitely many rank-one translation sets -/

noncomputable section

open CategoryTheory AlgebraicGeometry AddMonoidAlgebra
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel.ValuationKernelCoordinates

open LaurentBlockInvariants ActualCommonLeviV3

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

local instance rankOneDifferencePointTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X

set_option hygiene false in
local notation "Λ" => Additive (rationalDiscreteValuationImage H)
set_option hygiene false in
local notation "ν" => (fun ψ => (rationalNormCharacters H ψ).toMul)
set_option hygiene false in
local notation "R" => unramifiedRegularFunctions ν
set_option hygiene false in
local notation "U" => unitaryUnramifiedCharacters ν
local notation "hp" => continuous_rationalValuationImageProjection H

/-- A chart of the actual valuation image with at most one coordinate
outside the block scaled by translations. -/
structure RankOneTranslationChart where
  rank : ℕ
  complementRank : ℕ
  rank_le_one : rank ≤ 1
  coordinates : Λ ≃ₗ[ℤ] (Fin rank → ℤ) × (Fin complementRank → ℤ)

/-- The actual regular-ring translations from the complement block. -/
def RankOneTranslationChart.translations (d : RankOneTranslationChart H) : Set (R ≃+* R) :=
  Set.range fun c : Fin d.complementRank → ℂˣ =>
    (unramifiedRegularTranslation ν (complementParameter d.coordinates c)).toRingEquiv

private theorem exists_basis_root_associated_of_all_translates
    (hH : IsConnectedReductive H)
    {r n : ℕ} (e : Λ ≃ₗ[ℤ] (Fin r → ℤ) × (Fin n → ℤ)) (hr : r ≤ 1)
    (p c : R) (hprime : Prime p) (hc : c ≠ 0)
    (hdiv : ∀ t : Fin n → ℂˣ, p ∣ unramifiedRegularTranslation ν (complementParameter e t) c) :
    ∃ m : ℕ, ∃ B : Module.Basis (Fin (m + 1)) ℤ Λ, ∃ a : ℂˣ,
      Associated p (rationalUnramifiedBasisCoordinateRoot H B a) := by
  let : IsDomain R := rationalUnramifiedRegularFunctions_isDomain H hp hH
  let productAlg := productLaurentAlgebraEquiv e
  have hp' : Prime (productAlg.symm p) := (MulEquiv.prime_iff productAlg.symm.toMulEquiv).mpr hprime
  have hc' : productAlg.symm c ≠ 0 := (map_ne_zero_iff productAlg.symm productAlg.symm.injective).mpr hc
  have hdiv' (t : Fin n → ℂˣ) : productAlg.symm p ∣ productRegularScaling e t (productAlg.symm c) := by
    simpa only [productAlg, productRegularScaling, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply] using
      map_dvd productAlg.symm (hdiv t)
  obtain ⟨a, ha, h⟩ := exists_prime_dvd_firstBlock_of_dvd_all_scalings
    (productRegularScaling e) (productRegularScaling_single e) _ _ hp' hc' hdiv'
  have hr' : r = 0 ∨ r = 1 := by omega
  rcases hr' with rfl | rfl
  · exact (hp'.not_isUnit (isUnit_of_dvd_unit h (isUnit_firstBlock_rank_zero a ha))).elim
  · obtain ⟨z, hz⟩ := exists_prime_dvd_firstLinearFactor _ hp' a ha h
    let joinChart := joinFirstLaurentCoordinate n
    let B := Module.Basis.ofEquivFun (e.trans joinChart)
    let basisAlg := rationalUnramifiedBasisLaurentEquiv H B
    let joinAlg := AddMonoidAlgebra.domCongr ℂ ℂ joinChart.toAddEquiv
    have hcomp : ∀ x, basisAlg (joinAlg x) = productAlg x := by
      intro x
      induction x using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => simp [hx, hy]
      | single v a =>
        simp only [productAlg, basisAlg, joinAlg, B, productLaurentAlgebraEquiv,
          rationalUnramifiedBasisLaurentEquiv, Module.Basis.equivFun_ofEquivFun,
          AlgEquiv.trans_apply, AddMonoidAlgebra.domCongr_single]
        congr 2
        change e.symm (joinChart.symm (joinChart v)) = e.symm v
        rw [LinearEquiv.symm_apply_apply]
    have he : productAlg
        (LaurentBlockInvariants.firstPolynomialMap (n := n) (Polynomial.X - Polynomial.C (z : ℂ))) =
      rationalUnramifiedBasisCoordinateRoot H B z := by
      rw [← hcomp, rationalUnramifiedBasisCoordinateRoot]
      exact congrArg basisAlg (firstPolynomialMap_linearFactor z)
    have hd := map_dvd productAlg hz
    rw [he, AlgEquiv.apply_symm_apply] at hd
    have hpRoot : Prime (rationalUnramifiedBasisCoordinateRoot H B z) :=
      (MulEquiv.prime_iff basisAlg.toMulEquiv).mpr (finiteLaurentCoordinateRoot_prime n z)
    exact ⟨n, B, z, hprime.associated_of_dvd hpRoot hd⟩

/-- A basis-coordinate root that vanishes on the unitary group lies on the unit circle. -/
theorem basis_root_eq_circle_of_eval_zero {n : ℕ}
    (B : Module.Basis (Fin (n + 1)) ℤ Λ) (a : ℂˣ) (w : U)
    (hw : rationalUnitaryRegularRestriction H (rationalUnramifiedBasisCoordinateRoot H B a) w = 0) :
    ∃ t : Circle, a = Circle.toUnits t := by
  obtain ⟨x, rfl⟩ := rationalUnitaryParameterOfBasis_surjective H B w
  let v := (Fin.consEquiv (fun _ : Fin (n + 1) => Circle)).symm x
  have hv : Fin.cons v.1 v.2 = x :=
    (Fin.consEquiv (fun _ : Fin (n + 1) => Circle)).apply_symm_apply x
  rw [← hv, rationalUnramifiedBasisCoordinateRoot_eval_cons] at hw
  refine ⟨v.1, Units.ext ?_⟩
  exact (sub_eq_zero.mp hw).symm

variable (hH : IsConnectedReductive H)

local notation "K" => rationalUnramifiedFunctionField H hp hH

/-- Every prime in the reduced denominator of a fraction with the specified
vanishing differences is associated to a basis-coordinate root. -/
theorem denominator_prime_associated_of_rankOne_differences
    (charts : List (RankOneTranslationChart H)) {a b p : R}
    (ha : a ≠ 0) (hb : b ≠ 0) (hpPrime : Prime p) (hpb : p ∣ b) (hpa : ¬ p ∣ a)
    (hdiff : MultiplicativeDifferencesVanish (charts.map (RankOneTranslationChart.translations H))
      (algebraMap R K a / algebraMap R K b)) :
    ∃ n : ℕ, ∃ B : Module.Basis (Fin (n + 1)) ℤ Λ, ∃ s : ℂˣ,
      Associated p (rationalUnramifiedBasisCoordinateRoot H B s) := by
  let : IsDomain R := rationalUnramifiedRegularFunctions_isDomain H hp hH
  obtain ⟨S, hS, c, hc, hdiv⟩ := exists_translationSet_prime_dvd_every_translate p hpPrime _ a b
    ha hb (Or.inr ⟨hpb, hpa⟩) hdiff
  obtain ⟨data, _, rfl⟩ := List.mem_map.mp hS
  exact exists_basis_root_associated_of_all_translates H hH data.coordinates
    data.rank_le_one p c hpPrime hc (fun t => hdiv _ ⟨t, rfl⟩)

/-- Rank-one translation differences and a dense norm bound exclude every
prime divisor of the reduced denominator at every unitary point. -/
theorem unitaryRegular_of_rankOne_differences
    (charts : List (RankOneTranslationChart H)) (f : K) (hf : f ≠ 0)
    (hdiff : MultiplicativeDifferencesVanish (charts.map (RankOneTranslationChart.translations H)) f)
    (hbound : HasDenseUnitaryNormBound hH f) :
    RationalFunctionUnitaryRegular H hH f := by
  classical
  let : IsDomain R := rationalUnramifiedRegularFunctions_isDomain H hp hH
  let : UniqueFactorizationMonoid R := rationalUnramifiedRegularFunctions_uniqueFactorizationMonoid H hp hH
  obtain ⟨a, b, hcop, hab⟩ := IsFractionRing.exists_reduced_fraction R f
  rw [IsFractionRing.mk'_eq_div] at hab
  have ha : a ≠ 0 := by
    rintro rfl
    exact hf (by rw [← hab, map_zero, zero_div])
  have hb : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.property
  obtain ⟨D, hD, C, hC, hB⟩ := hbound
  let E : Set U := {z | rationalUnitaryRegularRestriction H (b : R) z ≠ 0}
  have hE : Dense E := dense_rationalUnitaryRegularRestriction_ne_zero H hH b hb
  have hEopen : IsOpen E := (isClosed_eq
    ((continuous_unramifiedRegularFunction ν (b : R)).comp
      (continuous_subtype_val.subtype_mk (fun z : U => z.property.1))) continuous_const).isOpen_compl
  have hDE : Dense (D ∩ E) := hD.inter_of_isOpen_right hE hEopen
  have hnorm (z : U) (hz : z ∈ D ∩ E) :
      ‖rationalUnitaryRegularRestriction H a z‖ ≤ C * ‖rationalUnitaryRegularRestriction H (b : R) z‖ := by
    obtain ⟨m, d, hd, hfd, hle⟩ := hB z hz.1
    have hz' : (b : R).val (unitaryToUnramified H z) ≠ 0 := hz.2
    rw [← rationalFunction_value_eq H hp hH hz' hd hab.symm hfd] at hle
    rw [norm_div] at hle
    exact (div_le_iff₀ (norm_pos_iff.mpr hz')).mp hle
  intro z
  let eval := UnramifiedNormalized.evaluation ν (unitaryToUnramified H z)
  have hnonzero (p : R) (hprime : Prime p) (hpb : p ∣ (b : R)) : eval p ≠ 0 := by
    intro hp0
    have hpna : ¬ p ∣ a := fun h => hprime.not_isUnit (hcop h hpb)
    have hd : MultiplicativeDifferencesVanish (charts.map (RankOneTranslationChart.translations H))
        (algebraMap R K a / algebraMap R K (b : R)) := hab.symm ▸ hdiff
    obtain ⟨n, B, s, hassoc⟩ :=
      denominator_prime_associated_of_rankOne_differences H hH charts ha hb hprime hpb hpna hd
    let root := rationalUnramifiedBasisCoordinateRoot H B s
    have hr0 : rationalUnitaryRegularRestriction H root z = 0 :=
      zero_dvd_iff.mp (hp0 ▸ map_dvd eval hassoc.dvd)
    obtain ⟨t, rfl⟩ := basis_root_eq_circle_of_eval_zero H B s z hr0
    have hrb : rationalUnramifiedBasisCoordinateRoot H B (Circle.toUnits t) ^ 1 ∣ (b : R) := by
      rw [pow_one]
      exact hassoc.symm.dvd.trans hpb
    have hra := rationalUnramifiedBasisCoordinateRoot_pow_dvd_of_dense_unitary_bound H B t 1
      a b (D ∩ E) hDE C hnorm hrb
    rw [pow_one] at hra
    exact hpna (hassoc.dvd.trans hra)
  obtain ⟨factors, hprimes, hprod⟩ := rationalUnramifiedRegularFunctions_exists_prime_factors H hp hH b hb
  obtain ⟨v, hv⟩ := hprod
  have hfactors : eval factors.prod ≠ 0 := by
    rw [map_multiset_prod]
    apply Multiset.prod_ne_zero
    intro hzero
    obtain ⟨p, hpMem, hpZero⟩ := Multiset.mem_map.mp hzero
    exact hnonzero p (hprimes p hpMem) ((Multiset.dvd_prod hpMem).trans ⟨v, hv.symm⟩) hpZero
  have hbz : (b : R).val (unitaryToUnramified H z) ≠ 0 := by
    change eval (b : R) ≠ 0
    rw [← hv, map_mul]
    exact mul_ne_zero hfactors ((Units.isUnit v).map eval).ne_zero
  exact ⟨a, b, hbz, hab.symm⟩

end Langlands.Plancherel.ValuationKernelCoordinates
