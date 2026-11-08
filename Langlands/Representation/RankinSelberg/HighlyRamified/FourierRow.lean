import Langlands.HarmonicAnalysis.PadicLatticeFourierProof
import Mathlib.MeasureTheory.Integral.Pi
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.RankinSelberg.InducedTailIntermediateCanonicalMeasures

/-!
# Character integrals over integral rows

For an additive character `ψ` of conductor `O`, the integral of `x ↦ ψ(Σ_j u_j x_j)` over
the integral row vectors `x ∈ O^(m+1)` is `vol(O)^(m+1)` if `u` is integral and `0`
otherwise. Consequently the finite exponential sum `S₂(ξ) = Σ_(z ∈ T) Φ(z) ψ(⟨z, ξ⟩)`
(restricted to integral `ξ`) satisfies the inversion formula
`∫ S₂(rev x) ψ(⟨v, x⟩) dx = vol(O)^(m+1) Σ_(z ∈ T, z∘rev + v ∈ O) Φ(z)`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance fourierRowFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance fourierRowValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance fourierRowLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance fourierRowFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance fourierRowFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩

variable {m : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier) (η : AdditiveHaarMeasure F.Carrier)

/-- `ψ` has conductor `O`: trivial on `O`, and nontrivial on `z t` for some integral `z`
whenever `t` is not integral. -/
structure HasIntegerConductorAt : Prop where
  trivial : ∀ t ∈ (ValuativeRel.valuation F.Carrier).integer, ψ t = 1
  nontrivial : ∀ t : F.Carrier, t ∉ (ValuativeRel.valuation F.Carrier).integer →
    ∃ z ∈ (ValuativeRel.valuation F.Carrier).integer, ψ.complex (z * t) ≠ 1

/-- The integer ring as an additive subgroup. -/
abbrev integerAddSubgroup : AddSubgroup F.Carrier :=
  (ValuativeRel.valuation F.Carrier).integer.toAddSubgroup

open Classical in
/-- The one-variable integral `∫_O ψ(t y) dt`. -/
theorem integral_integer_character (hψ : HasIntegerConductorAt F ψ) (y : F.Carrier) :
    ∫ t, ψ.complex (t * y) * ((integerAddSubgroup F : AddSubgroup F.Carrier) :
        Set F.Carrier).indicator (fun _ => (1 : ℂ)) t ∂η.measure =
      if y ∈ (ValuativeRel.valuation F.Carrier).integer then
        ((η.measure ((integerAddSubgroup F : AddSubgroup F.Carrier) : Set F.Carrier)).toReal : ℂ)
      else 0 := by
  split_ifs with hy
  · exact subgroup_character_integral_of_trivial ψ η _
      (Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier)) y
      (fun t ht => hψ.trivial _ (Subring.mul_mem _ ht hy))
  · obtain ⟨z, hz, hne⟩ := hψ.nontrivial y hy
    exact subgroup_character_integral_of_nontrivial ψ η _ y z hz (by
      intro h
      apply hne
      simp [h])

/-- An additive character turns finite sums into products. -/
theorem addChar_finset_sum {ι : Type*} (χ : AddChar F.Carrier ℂ) (s : Finset ι)
    (a : ι → F.Carrier) : χ (∑ i ∈ s, a i) = ∏ i ∈ s, χ (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]

/-- The one-coordinate factor `t ↦ ψ(t a) 1_O(t)`. -/
def integerCharacterFactor (a : F.Carrier) (t : F.Carrier) : ℂ :=
  ψ.complex (t * a) * ((integerAddSubgroup F : AddSubgroup F.Carrier) : Set F.Carrier).indicator
    (fun _ => (1 : ℂ)) t

open Classical in
/-- The row integral `∫ ∏_j ψ(x_j u_j) 1_O(x_j) dx = ∏_j vol(O)[u_j ∈ O]`. -/
theorem integral_row_character (hψ : HasIntegerConductorAt F ψ) (u : Fin (m + 1) → F.Carrier) :
    ∫ x : Matrix (Fin 1) (Fin (m + 1)) F.Carrier, ∏ j, integerCharacterFactor F ψ (u j) (x 0 j)
        ∂RankinSelberg.rectangularMeasure η 1 (m + 1) =
      ∏ j, (if u j ∈ (ValuativeRel.valuation F.Carrier).integer then
        ((η.measure ((integerAddSubgroup F : AddSubgroup F.Carrier) :
          Set F.Carrier)).toReal : ℂ) else 0) := by
  have : SigmaFinite η.measure :=
    InducedTailIntermediate.scalarHaar_sigmaFinite F.canonicalTopologicalData η
  have hinner : ∫ r : Fin (m + 1) → F.Carrier, ∏ j, integerCharacterFactor F ψ (u j) (r j)
      ∂(Measure.pi fun _ : Fin (m + 1) => η.measure) =
      ∏ j, (if u j ∈ (ValuativeRel.valuation F.Carrier).integer then
        ((η.measure ((integerAddSubgroup F : AddSubgroup F.Carrier) :
          Set F.Carrier)).toReal : ℂ) else 0) := by
    rw [integral_fintype_prod_eq_prod (fun j => integerCharacterFactor F ψ (u j))]
    exact Finset.prod_congr rfl fun j _ => integral_integer_character F ψ η hψ (u j)
  have key : ∫ x : Fin 1 → Fin (m + 1) → F.Carrier, ∏ i : Fin 1,
      (fun (_ : Fin 1) (r : Fin (m + 1) → F.Carrier) =>
        ∏ j, integerCharacterFactor F ψ (u j) (r j)) i (x i)
      ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin (m + 1) => η.measure) =
      ∏ j, (if u j ∈ (ValuativeRel.valuation F.Carrier).integer then
        ((η.measure ((integerAddSubgroup F : AddSubgroup F.Carrier) :
          Set F.Carrier)).toReal : ℂ) else 0) := by
    have h := integral_fintype_prod_eq_prod
      (μ := fun _ : Fin 1 => Measure.pi fun _ : Fin (m + 1) => η.measure)
      (fun (_ : Fin 1) (r : Fin (m + 1) → F.Carrier) =>
        ∏ j, integerCharacterFactor F ψ (u j) (r j))
    exact h.trans (by rw [Fin.prod_univ_one]; exact hinner)
  simp only [Fin.prod_univ_one] at key
  exact key

/-- Integrability of the factor `t ↦ ψ(t a) 1_O(t)`. -/
theorem integrable_integerCharacterFactor (a : F.Carrier) :
    Integrable (integerCharacterFactor F ψ a) η.measure := by
  have := localField_t2 F.Carrier
  have hc : IsCompact ((integerAddSubgroup F : AddSubgroup F.Carrier) : Set F.Carrier) :=
    isCompact_iff_compactSpace.mpr
      (inferInstanceAs (CompactSpace (ValuativeRel.valuation F.Carrier).integer))
  have hm : MeasurableSet ((integerAddSubgroup F : AddSubgroup F.Carrier) : Set F.Carrier) :=
    (Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier)).measurableSet
  have hcont : Continuous fun t : F.Carrier => ψ.complex (t * a) :=
    ψ.continuous_complex.comp (continuous_id.mul continuous_const)
  have h1 : IntegrableOn (fun t : F.Carrier => ψ.complex (t * a))
      ((integerAddSubgroup F : AddSubgroup F.Carrier) : Set F.Carrier) η.measure :=
    hcont.continuousOn.integrableOn_compact hc
  have h2 := (integrable_indicator_iff hm).mpr h1
  refine h2.congr (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ ((integerAddSubgroup F : AddSubgroup F.Carrier) : Set F.Carrier)
  · rw [integerCharacterFactor, Set.indicator_of_mem ht, Set.indicator_of_mem ht, mul_one]
  · rw [integerCharacterFactor, Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]

/-- Integrability of the row products. -/
theorem integrable_row_character (u : Fin (m + 1) → F.Carrier) :
    Integrable (fun x : Matrix (Fin 1) (Fin (m + 1)) F.Carrier =>
      ∏ j, integerCharacterFactor F ψ (u j) (x 0 j))
      (RankinSelberg.rectangularMeasure η 1 (m + 1)) := by
  have : SigmaFinite η.measure :=
    InducedTailIntermediate.scalarHaar_sigmaFinite F.canonicalTopologicalData η
  unfold RankinSelberg.rectangularMeasure
  have hrw : (fun x : Matrix (Fin 1) (Fin (m + 1)) F.Carrier =>
      ∏ j, integerCharacterFactor F ψ (u j) (x 0 j)) =
      fun x => ∏ i : Fin 1,
        (fun (_ : Fin 1) (r : Fin (m + 1) → F.Carrier) =>
          ∏ j, integerCharacterFactor F ψ (u j) (r j)) i (x i) := by
    funext x
    rw [Fin.prod_univ_one]
  rw [hrw]
  exact Integrable.fintype_prod fun _ =>
    Integrable.fintype_prod fun j => integrable_integerCharacterFactor F ψ η (u j)

open Classical in
/-- The row product of character factors, as a restricted character. -/
theorem prod_integerCharacterFactor (x : Matrix (Fin 1) (Fin (m + 1)) F.Carrier)
    (a : Fin (m + 1) → F.Carrier) :
    ∏ j, integerCharacterFactor F ψ (a j) (x 0 j) =
      if ∀ j, x 0 j ∈ (ValuativeRel.valuation F.Carrier).integer then
        ψ.complex (∑ j, x 0 j * a j) else 0 := by
  unfold integerCharacterFactor
  rw [Finset.prod_mul_distrib, ← addChar_finset_sum]
  by_cases hx : ∀ j, x 0 j ∈ (ValuativeRel.valuation F.Carrier).integer
  · rw [if_pos hx, Finset.prod_eq_one fun j _ => Set.indicator_of_mem (hx j) _, mul_one]
  · rw [if_neg hx]
    push Not at hx
    obtain ⟨j, hj⟩ := hx
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _), mul_zero]

open Classical in
/-- Inversion for the restricted finite exponential sum:
`∫ S₂(rev x) ψ(⟨v, x⟩) dx = Σ_(z ∈ T) Φ(z) ∏_j vol(O)[z_(rev j) + v_j ∈ O]`, where
`S₂(ξ) = Σ_(z ∈ T) Φ(z) ψ(Σ_k z_k ξ_k)` for integral `ξ` and `0` otherwise. -/
theorem integral_restrictedFourier_character (hψ : HasIntegerConductorAt F ψ)
    (T : Finset (Fin (m + 1) → F.Carrier)) (Φ : (Fin (m + 1) → F.Carrier) → ℂ)
    (v : Fin (m + 1) → F.Carrier) :
    ∫ x : Matrix (Fin 1) (Fin (m + 1)) F.Carrier,
        (if ∀ k : Fin (m + 1), x 0 k.rev ∈ (ValuativeRel.valuation F.Carrier).integer then
          ∑ z ∈ T, Φ z * ψ.complex (∑ k, z k * x 0 k.rev) else 0) *
          ψ.complex (∑ j, v j * x 0 j) ∂RankinSelberg.rectangularMeasure η 1 (m + 1) =
      ∑ z ∈ T, Φ z * ∏ j, (if z j.rev + v j ∈ (ValuativeRel.valuation F.Carrier).integer then
        ((η.measure ((integerAddSubgroup F : AddSubgroup F.Carrier) :
          Set F.Carrier)).toReal : ℂ) else 0) := by
  have hpt : ∀ x : Matrix (Fin 1) (Fin (m + 1)) F.Carrier,
      (if ∀ k : Fin (m + 1), x 0 k.rev ∈ (ValuativeRel.valuation F.Carrier).integer then
          ∑ z ∈ T, Φ z * ψ.complex (∑ k, z k * x 0 k.rev) else 0) *
          ψ.complex (∑ j, v j * x 0 j) =
        ∑ z ∈ T, Φ z * ∏ j, integerCharacterFactor F ψ (z j.rev + v j) (x 0 j) := by
    intro x
    simp_rw [prod_integerCharacterFactor]
    by_cases hx : ∀ j, x 0 j ∈ (ValuativeRel.valuation F.Carrier).integer
    · have hx' : ∀ k : Fin (m + 1), x 0 k.rev ∈ (ValuativeRel.valuation F.Carrier).integer :=
        fun k => hx _
      rw [if_pos hx', Finset.sum_mul]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [if_pos hx, mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      rw [← Equiv.sum_comp Fin.revPerm (fun k => z k * x 0 k.rev), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Fin.revPerm_apply, Fin.rev_rev]
      ring
    · have hx' : ¬ ∀ k : Fin (m + 1), x 0 k.rev ∈ (ValuativeRel.valuation F.Carrier).integer := by
        intro h; exact hx fun j => by simpa using h j.rev
      rw [if_neg hx', zero_mul]
      refine (Finset.sum_eq_zero fun z _ => ?_).symm
      rw [if_neg hx, mul_zero]
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [integral_const_mul, integral_row_character F ψ η hψ (fun j => z j.rev + v j)]
  · intro z _
    exact (integrable_row_character F ψ η (fun j => z j.rev + v j)).const_mul _

end Langlands.RankinSelberg.HighlyRamified
