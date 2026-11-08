import Langlands.Representation.Conductor.ClassLevel
import Langlands.Representation.Conductor.Essential

/-!
# From a level line in a Whittaker model to the conductor clauses

A nonzero model vector at level `m` that spans every level-`m` fixed vector,
with no nonzero fixed vector at lower levels, gives the newvector-conductor
and dimension-one clauses for the original irreducible representation.
An essential vector is never zero.
-/

noncomputable section

namespace Langlands.Conductor

open Matrix Langlands.Whittaker Langlands.HarmonicAnalysis Langlands.RankinSelberg
open MeasureTheory Polynomial Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa

universe uF uV uW

section Line

variable {F : Type uF} [Field F] [ValuativeRel F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- `w` is fixed at level `m`, spans every level-`m` fixed vector, and no lower level
has a nonzero fixed vector. -/
def IsLevelLine (ρ : Representation ℂ (GeneralLinearGroup (Fin (n + 1)) F) V) (m : ℕ)
    (w : V) : Prop :=
  w ∈ levelFixedVectors ρ m ∧ (∀ b < m, ∀ v ∈ levelFixedVectors ρ b, v = 0) ∧
    ∀ v ∈ levelFixedVectors ρ m, ∃ C : ℂ, v = C • w

/-- A nonzero level line makes `m` the newvector conductor with a line of fixed
vectors. -/
theorem isNewvectorConductor_and_finrank_of_line
    (ρ : Representation ℂ (GeneralLinearGroup (Fin (n + 1)) F) V) (m : ℕ) (w : V)
    (hw0 : w ≠ 0) (hL : IsLevelLine ρ m w) :
    IsNewvectorConductor ρ m ∧ Module.finrank ℂ (levelFixedVectors ρ m) = 1 := by
  obtain ⟨hw, hlow, hline⟩ := hL
  have hspan : levelFixedVectors ρ m = Submodule.span ℂ {w} := by
    apply le_antisymm
    · intro v hv
      obtain ⟨C, rfl⟩ := hline v hv
      exact Submodule.smul_mem _ C (Submodule.mem_span_singleton_self w)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hw
  refine ⟨⟨?_, fun b hb => ?_⟩, ?_⟩
  · exact (Submodule.ne_bot_iff _).mpr ⟨w, hw, hw0⟩
  · exact (Submodule.eq_bot_iff _).mpr (hlow b hb)
  · rw [hspan]
    exact finrank_span_singleton hw0

/-- The dimension of a level-fixed space is invariant under representation equivalence. -/
theorem finrank_levelFixedVectors_of_equiv
    {ρ : Representation ℂ (GeneralLinearGroup (Fin (n + 1)) F) V}
    {σ : Representation ℂ (GeneralLinearGroup (Fin (n + 1)) F) W}
    (e : ρ.Equiv σ) (a : ℕ) :
    Module.finrank ℂ (levelFixedVectors ρ a) = Module.finrank ℂ (levelFixedVectors σ a) :=
  (fixedVectorsEquiv e (levelSubgroup F n a)).finrank_eq

/-- Both conductor clauses pass along a representation equivalence. -/
theorem isNewvectorConductor_and_finrank_of_equiv
    {ρ : Representation ℂ (GeneralLinearGroup (Fin (n + 1)) F) V}
    {σ : Representation ℂ (GeneralLinearGroup (Fin (n + 1)) F) W}
    (e : ρ.Equiv σ) (m : ℕ)
    (h : IsNewvectorConductor σ m ∧ Module.finrank ℂ (levelFixedVectors σ m) = 1) :
    IsNewvectorConductor ρ m ∧ Module.finrank ℂ (levelFixedVectors ρ m) = 1 :=
  ⟨(isNewvectorConductor_iff_of_equiv e m).mpr h.1,
    (finrank_levelFixedVectors_of_equiv e m).trans h.2⟩

end Line

section Model

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A level line in the coefficient model of a nonzero functional on an irreducible
representation gives the newvector conductor and the dimension-one clause for the
representation itself. -/
theorem isNewvectorConductor_and_finrank_of_model_line
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hirr : Representation.IsIrreducible π)
    (ℓ : glFunctionals ψ n π) (hℓ : ℓ.val ≠ 0) (m : ℕ)
    (w : (coefficientModel π ℓ).toSubmodule) (hw0 : w ≠ 0)
    (hL : IsLevelLine (modelRepresentation π ℓ) m w) :
    IsNewvectorConductor π m ∧ Module.finrank ℂ (levelFixedVectors π m) = 1 := by
  have := hirr
  exact isNewvectorConductor_and_finrank_of_equiv (glModelEquiv ψ n π ℓ hℓ) m
    (isNewvectorConductor_and_finrank_of_line _ m w hw0 hL)

end Model

/-- The essential factor of a polynomial with constant term one is nonzero. -/
theorem essentialFactor_ne_zero {m : ℕ} {P : ℂ[X]} (hP : P.coeff 0 = 1)
    (x : Fin m → ℂˣ) : essentialFactor P x ≠ 0 := by
  rw [essentialFactor, Finset.prod_ne_zero_iff]
  intro i _
  apply inv_ne_zero
  rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective ℂ[X] _)]
  intro hc
  have h0 := congrArg (fun R : ℂ[X] => R.coeff 0) hc
  simp only [coeff_zero_eq_eval_zero, eval_comp, eval_mul, eval_C, eval_X, mul_zero,
    eval_zero] at h0
  rw [← coeff_zero_eq_eval_zero, hP] at h0
  exact one_ne_zero h0

section Essential

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ} {ϖ : Fˣ}
  {μ : Measure (LeftUnipotentQuotient n F)}

omit [MeasurableSpace (Langlands.GeneralLinear 1 F)]
  [BorelSpace (Langlands.GeneralLinear 1 F)] in
/-- Jacquet's residue cardinality exceeds one. -/
theorem IsJacquetNormalization.one_lt_q (h : IsJacquetNormalization q ψ abv ϖ μ) : 1 < q := by
  rw [h.residueCardinality]
  exact Finite.one_lt_card

omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)]
  [BorelSpace (Langlands.GeneralLinear 1 F)] in
/-- The corank-one integral of the zero Whittaker function vanishes. -/
theorem corankOneIntegral_zero_left (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    corankOneIntegral ψ abv μ 0 W' s = 0 := by
  have hz : corankOneIntegrand ψ abv (0 : WhittakerFunctions ψ (n + 1)) W' s = 0 := by
    funext x
    induction x using Quotient.inductionOn with
    | h g =>
      rw [corankOneIntegrand_mk]
      simp
  rw [corankOneIntegral, hz]
  exact integral_zero _ _

/-- An essential vector is not the zero vector of the model. -/
theorem IsEssentialVector.ne_zero (h : IsJacquetNormalization q ψ abv ϖ μ)
    (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
    (ℓ : glFunctionals ψ (n + 1) π) {w : (coefficientModel π ℓ).toSubmodule}
    (hw : IsEssentialVector h π ℓ w) : w ≠ 0 := by
  rintro rfl
  obtain ⟨⟨P, hP, hid⟩, -⟩ := hw
  let x : Fin (n + 1) → ℂˣ := fun _ => 1
  have hcont := (hid x).2
  have hzero : HasRationalContinuation q
      (corankOneIntegral ψ abv μ (0 : (coefficientModel π ℓ).toSubmodule).val
        (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x)) 0 := by
    refine ⟨0, fun s _ => ⟨by simp, ?_⟩⟩
    rw [ZeroMemClass.coe_zero, corankOneIntegral_zero_left]
    simp
  exact essentialFactor_ne_zero hP.1 x (hcont.unique h.one_lt_q hzero)

/-- For an essential vector of a generic representation, a level line in its Whittaker
model gives the newvector conductor and the dimension-one clause for the
representation itself. -/
theorem isNewvectorConductor_and_finrank_of_essential
    (h : IsJacquetNormalization q ψ abv ϖ μ)
    (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
    (hπ : IsGeneric ψ (n + 1) π) (ℓ : glFunctionals ψ (n + 1) π) (hℓ : ℓ.val ≠ 0)
    (w : (coefficientModel π ℓ).toSubmodule) (hw : IsEssentialVector h π ℓ w) (m : ℕ)
    (hL : IsLevelLine (modelRepresentation π ℓ) m w) :
    IsNewvectorConductor π m ∧ Module.finrank ℂ (levelFixedVectors π m) = 1 :=
  isNewvectorConductor_and_finrank_of_model_line ψ π hπ.1 ℓ hℓ m w
    (IsEssentialVector.ne_zero h π ℓ hw) hL

end Essential

end Langlands.Conductor
