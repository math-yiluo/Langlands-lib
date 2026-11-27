import Langlands.BaseChange.BorelJacquetNormalization
import Langlands.BaseChange.BorelJacquetWeightTrace
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # The normalized Jacquet expansion of the regular elementary traces -/

noncomputable section

namespace Langlands.BaseChange

open Correspondence Unramified GeneralLinear.BlockShape
open scoped BigOperators NNReal

universe u v uV uW

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

private local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearLocallyCompactSpace n

private local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    TotallyDisconnectedSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier n

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) {r : ℕ}

local notation "D" => F.canonicalTopologicalData

/-- The elementary scalar after inserting the positive Borel half-modulus. -/
def regularElementaryNormalizedFactor (ν : Fin (r + 1) → ℤ) : ℂ :=
  ((D).residueCardinality : ℂ) ^ regularElementaryRho ν *
    (Real.sqrt (((D).residueCardinality : ℝ) ^ (-regularElementaryRho ν)) : ℂ)

theorem regularElementaryNormalizedFactor_ne_zero (ν : Fin (r + 1) → ℤ) :
    regularElementaryNormalizedFactor F ν ≠ 0 := by
  have hq : (0 : ℝ) < (D).residueCardinality := by
    exact_mod_cast zero_lt_one.trans (D).residueCardinality_gt_one
  apply mul_ne_zero
  · exact zpow_ne_zero _ (by exact_mod_cast hq.ne')
  · exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos (zpow_pos hq _)).ne'

set_option backward.isDefEq.respectTransparency false in
private theorem trace_borelJacquetDiagonalAction
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (hρ : IsAdmissible ρ)
    (a : Fin (r + 1) → F.Carrierˣ) (ν : Fin (r + 1) → ℤ)
    (ha : ∀ i, (D).ord (a i : F.Carrier) = ν i) :
    LinearMap.trace ℂ (borelJacquetFixed F ρ) (borelJacquetDiagonalAction F ρ a) =
      (Real.sqrt (((D).residueCardinality : ℝ) ^ (-regularElementaryRho ν)) : ℂ) *
        ((borelJacquetMultiset F ρ).map (fun c => ∏ i, (c i : ℂ) ^ ν i)).sum := by
  let W := borelJacquetIntegralFixed F ρ
  let e : borelJacquetFixed F ρ ≃ₗ[ℂ] W :=
    LinearEquiv.ofEq _ _ (borelJacquetNormalization p F r V ρ)
  let T := borelJacquetLatticeAction F ρ (Multiplicative.ofAdd ν)
  let m := singletonLevi F.Carrier a
  have hConj : e.conj (borelJacquetDiagonalAction F ρ a) =
      ((D).leviHalfModulus (singletons (r + 1)) m : ℂ) • T := by
    ext1 x
    apply Subtype.ext
    rw [LinearEquiv.conj_apply_apply]
    change Parabolic.leviCoinvariants (singletons (r + 1))
        (ρ.comp ((singletons (r + 1)).parabolic F.Carrier).subtype) m x.val =
        ((D).leviHalfModulus (singletons (r + 1)) m : ℂ) •
          (T x : (borelShape r).JacquetModule ρ)
    exact (unnormalizedBorelJacquet_eq_half_smul F ρ m x.val).trans
      (congrArg (((D).leviHalfModulus (singletons (r + 1)) m : ℂ) • ·)
        (borelJacquetLatticeAction_apply_eq_of_ord F ρ _ a ha x).symm)
  rw [← LinearMap.trace_conj' _ e, hConj, map_smul, smul_eq_mul]
  have hScalar : ((D).leviHalfModulus (singletons (r + 1)) m : ℂ) =
      (Real.sqrt (((D).residueCardinality : ℝ) ^ (-regularElementaryRho ν)) : ℂ) := by
    rw [(D).leviHalfModulus_apply, Real.coe_sqrt]
    change (Real.sqrt ((((D).leviModulus (singletons (r + 1))
      (singletonLevi F.Carrier a) : ℝ≥0) : ℝ)) : ℂ) = _
    rw [leviModulus_singletonLevi_of_ord F a ν ha]
  exact congrArg₂ (· * ·) hScalar
    (borelJacquetWeightTrace p F r V ρ (finiteDimensional_borelJacquetIntegralFixed F ρ hρ) ν)

private theorem ord_uniformizer_powers (ϖ : F.Carrierˣ)
    (hϖ : (D).ord (ϖ : F.Carrier) = 1) (ν : Fin (r + 1) → ℤ) (i : Fin (r + 1)) :
    (D).ord ((ϖ ^ ν i : F.Carrierˣ) : F.Carrier) = ν i := by
  rw [Units.val_zpow_eq_zpow_val, (D).ord_zpow, hϖ, mul_one]

private theorem tupleWeightCharacter_eq_prod (c : Fin (r + 1) → ℂˣ) (ν : Fin (r + 1) → ℤ) :
    tupleWeightCharacter c (Multiplicative.ofAdd ν) = ∏ i, (c i : ℂ) ^ ν i := by
  change ((∏ i, c i ^ ν i : ℂˣ) : ℂ) = _
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val]

private theorem normalizedElementaryJacquetTrace_twisted
    (hTrace : RegularElementaryJacquetTraceStatement.{u, uV})
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (hρ : IsAdmissible ρ)
    (hIrr : ρ.IsIrreducible) (τ : F.Carrier ≃ₐ[Padic p] F.Carrier)
    (A : SigmaIntertwiner τ (r + 1) ρ)
    (hA : ∀ x : borelJacquetFixed F ρ,
      jacquetSigmaIntertwiner τ (borelShape r) A x.val = x.val)
    (ϖ : F.Carrierˣ) (hϖ : (D).ord (ϖ : F.Carrier) = 1) (hfix : τ (ϖ : F.Carrier) = ϖ)
    (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν) :
    twistedDistribution (sphericalHaar F r) ρ hρ A.toLinearMap
        (regularElementaryTest F τ ϖ hϖ ν hν) =
      regularElementaryNormalizedFactor F ν *
        ((borelJacquetMultiset F ρ).map (fun c => tupleWeightCharacter c (Multiplicative.ofAdd ν))).sum := by
  have hId : borelJacquetFixedTwist F ρ τ A = LinearMap.id := by
    ext1 x
    exact Subtype.ext (hA x)
  rw [hTrace p F r τ ϖ hϖ hfix ν hν V ρ hρ hIrr A, hId, LinearMap.comp_id,
    trace_borelJacquetDiagonalAction F ρ hρ _ ν (ord_uniformizer_powers F ϖ hϖ ν)]
  simp only [regularElementaryNormalizedFactor, tupleWeightCharacter_eq_prod, mul_assoc]

private theorem normalizedElementaryJacquetTrace_ordinary
    (hTrace : RegularElementaryJacquetTraceStatement.{u, uV})
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (hρ : IsAdmissible ρ)
    (hIrr : ρ.IsIrreducible)
    (ϖ : F.Carrierˣ) (hϖ : (D).ord (ϖ : F.Carrier) = 1)
    (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν) :
    Character.distribution (sphericalHaar F r) ρ hρ
        (regularElementaryTest F 1 ϖ hϖ ν hν) =
      regularElementaryNormalizedFactor F ν *
        ((borelJacquetMultiset F ρ).map (fun c => tupleWeightCharacter c (Multiplicative.ofAdd ν))).sum := by
  rw [regularElementaryJacquetTrace_of_identity F ρ hTrace hρ hIrr ϖ hϖ ν hν,
    trace_borelJacquetDiagonalAction F ρ hρ _ ν (ord_uniformizer_powers F ϖ hϖ ν)]
  simp only [regularElementaryNormalizedFactor, tupleWeightCharacter_eq_prod, mul_assoc]

section BaseChange

variable (E : PadicField.{v} p) [Algebra F.Carrier E.Carrier]
  [IsScalarTower (Padic p) F.Carrier E.Carrier]

private theorem regularElementaryRho_degree_mul (l : ℕ) (ν : Fin (r + 1) → ℤ) :
    regularElementaryRho (fun i => (l : ℤ) * ν i) = (l : ℤ) * regularElementaryRho ν := by
  simp only [regularElementaryRho, ← mul_sub, Finset.mul_sum]

/-- The same normalized factor is used on the two sides of a regular elementary pair. -/
theorem regularElementaryNormalizedFactor_baseChange
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l : ℕ) (hcyc : IsCyclicAlgebra σ l)
    (he : E.canonicalTopologicalData.ramificationIndex = (D).ramificationIndex)
    (ν : Fin (r + 1) → ℤ) :
    regularElementaryNormalizedFactor E ν =
      regularElementaryNormalizedFactor F (fun i => (l : ℤ) * ν i) := by
  let S := E.canonicalTopologicalData
  have hdeg : S.residueDegree = (D).residueDegree * l := by
    apply Nat.eq_of_mul_eq_mul_left (D).ramificationIndex_pos
    rw [← he, S.ramificationIndex_mul_residueDegree, he, ← mul_assoc,
      (D).ramificationIndex_mul_residueDegree,
      ← Module.finrank_mul_finrank (Padic p) F.Carrier E.Carrier, hcyc.2.1]
  have hq : S.residueCardinality = (D).residueCardinality ^ l := by
    rw [S.residueCardinality_eq_pow, (D).residueCardinality_eq_pow, hdeg, pow_mul]
  change (S.residueCardinality : ℂ) ^ regularElementaryRho ν *
      (Real.sqrt ((S.residueCardinality : ℝ) ^ (-regularElementaryRho ν)) : ℂ) = _
  rw [regularElementaryNormalizedFactor, regularElementaryRho_degree_mul, hq]
  push_cast
  rw [← zpow_natCast ((D).residueCardinality : ℂ) l, ← zpow_mul,
    ← zpow_natCast ((D).residueCardinality : ℝ) l, ← zpow_mul, mul_neg]

end BaseChange

/-- The regular elementary distributions have the normalized Jacquet weight expansions
for a common nonzero factor, when the upper twist fixes the integral Jacquet vectors. -/
def RegularElementaryNormalizedJacquetStatement : Prop :=
  RegularElementaryJacquetTraceStatement.{u, uV} →
  RegularElementaryJacquetTraceStatement.{v, uW} →
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l r : ℕ) (hcyc : IsCyclicAlgebra σ l)
    (he : E.canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex),
    let factor (w : StrictWeight (r + 1)) := regularElementaryNormalizedFactor E w.val
    let tests (w : StrictWeight (r + 1)) :=
      regularElementaryBaseChangeTests F E σ l hcyc he w.val w.property
    (∀ w, factor w ≠ 0) ∧
    (∀ (V : Type uW) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (r + 1) E.Carrier) V) (hρ : IsAdmissible ρ),
      ρ.IsIrreducible → ∀ A : SigmaIntertwiner σ (r + 1) ρ,
      (∀ x : borelJacquetFixed E ρ, jacquetSigmaIntertwiner σ (borelShape r) A x.val = x.val) →
      ∀ w, twistedDistribution (sphericalHaar E r) ρ hρ A.toLinearMap (tests w).1 =
        factor w *
          ((borelJacquetMultiset E ρ).map
            (fun c => tupleWeightCharacter c (Multiplicative.ofAdd (1 • w.val)))).sum) ∧
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (hρ : IsAdmissible ρ),
      ρ.IsIrreducible →
      ∀ w, Character.distribution (sphericalHaar F r) ρ hρ (tests w).2 =
        factor w *
          ((borelJacquetMultiset F ρ).map
            (fun c => tupleWeightCharacter c (Multiplicative.ofAdd (l • w.val)))).sum

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem regularElementaryNormalizedJacquet :
    RegularElementaryNormalizedJacquetStatement.{u, v, uV, uW} := by
  intro hTraceF hTraceE p _ F E _ _ σ l r hcyc he factor tests
  refine ⟨fun w => regularElementaryNormalizedFactor_ne_zero E w.val, ?_, ?_⟩
  · intro V _ _ ρ hρ hIrr A hA w
    have hfix : (σ.restrictScalars (Padic p)) (elementaryUpperUniformizer F E : E.Carrier) =
        (elementaryUpperUniformizer F E : E.Carrier) := σ.commutes _
    simpa only [one_smul, factor, tests, regularElementaryBaseChangeTests] using
      normalizedElementaryJacquetTrace_twisted E hTraceE ρ hρ hIrr
      (σ.restrictScalars (Padic p)) A hA (elementaryUpperUniformizer F E)
      (ord_elementaryUpperUniformizer F E he) hfix w.val w.property
  · intro V _ _ ρ hρ hIrr w
    let data := F.canonicalTopologicalData
    let ν (i : Fin (r + 1)) := (l : ℤ) * w.val i
    have hν : StrictAnti ν := fun _ _ hij =>
      mul_lt_mul_of_pos_left (w.property hij) (by exact_mod_cast hcyc.pos)
    have hϖ : data.ord (data.uniformizerUnit : F.Carrier) = 1 := by
      rw [data.uniformizerUnit_val, data.ord_uniformizer]
    have ht : (tests w).2 = regularElementaryTest F 1 data.uniformizerUnit hϖ ν hν := rfl
    change _ = regularElementaryNormalizedFactor E w.val * _
    rw [ht, regularElementaryNormalizedFactor_baseChange F E σ l hcyc he]
    exact normalizedElementaryJacquetTrace_ordinary F hTraceF ρ hρ hIrr data.uniformizerUnit hϖ ν hν

end Langlands.BaseChange
