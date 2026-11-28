import Langlands.Representation.Shahidi.OpenCellHecke

/-! # The minuscule Hecke relations of the unramified two-block section

For `ψ` of conductor `𝒪`, the lift `F` of `δ_P(m₁, m₂)^(1/2 + s/N) W°(m₁; a) W°(m₂; c)` to
`GL_((r+1)+(t+1))(K)` satisfies, at the torus points that are antitone on each block, the
normalized minuscule Hecke relations of the Satake parameter
`χ = (a q^(-s(t+1)/N), c q^(s(r+1)/N))`: the sum of its translates by the labelled minuscule
coset representatives of size `k` is `q^(k(N-k)/2) e_k(χ)` times its value. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor Langlands.Unramified.MinusculeCosets
open Langlands.GeneralLinear.Iwasawa
open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit)

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocHeckeRelTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance ocHeckeRelValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocHeckeRelLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField

section Parameter

variable (K)

theorem residueCardinality_pos : 0 < K.canonicalTopologicalData.residueCardinality := by
  have := K.canonicalTopologicalData.residueCardinality_gt_one
  omega

/-- The unit `q ^ z` of `ℂ`, `q` the residue cardinality. -/
def residuePowUnit (z : ℂ) : ℂˣ :=
  Units.mk0 ((K.canonicalTopologicalData.residueCardinality : ℂ) ^ z) (by
    intro h
    have h' := (Complex.cpow_eq_zero_iff _ _).1 h
    exact (Nat.cast_ne_zero.2 (residueCardinality_pos K).ne') h'.1)

@[simp] theorem residuePowUnit_val (z : ℂ) :
    (residuePowUnit K z : ℂ) = (K.canonicalTopologicalData.residueCardinality : ℂ) ^ z := rfl

/-- The Satake parameter `χ = (a q^(-s(t+1)/N), c q^(s(r+1)/N))` of the two-block section,
`N = r + t + 2`. -/
def sectionParameter {r t : ℕ} (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ) :
    Fin ((r + 1) + (t + 1)) → ℂˣ :=
  Fin.append (fun i => a i * residuePowUnit K (-(s * ((t + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ))))
    (fun j => c j * residuePowUnit K (s * ((r + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ)))

theorem sectionParameter_castAdd {r t : ℕ} (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    (i : Fin (r + 1)) :
    (sectionParameter K a c s (i.castAdd (t + 1)) : ℂ) = (a i : ℂ) *
      (K.canonicalTopologicalData.residueCardinality : ℂ) ^
        (-(s * ((t + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ))) := by
  simp [sectionParameter]

theorem sectionParameter_natAdd {r t : ℕ} (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    (j : Fin (t + 1)) :
    (sectionParameter K a c s (j.natAdd (r + 1)) : ℂ) = (c j : ℂ) *
      (K.canonicalTopologicalData.residueCardinality : ℂ) ^
        (s * ((r + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ)) := by
  simp [sectionParameter]

end Parameter

section Powers

theorem sqrt_pow_eq_cpow (q n : ℕ) :
    ((Real.sqrt q : ℝ) : ℂ) ^ n = (q : ℂ) ^ ((n : ℂ) * (1 / 2)) := by
  rw [Complex.cpow_nat_mul]
  congr 1
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]
  norm_num

/-- **The scalar identity of the Hecke relation.** -/
theorem heckeScalar_eq (q : ℕ) (hq : 0 < q) (r t k₁ k₂ : ℕ) (hk₁ : k₁ ≤ r + 1) (hk₂ : k₂ ≤ t + 1)
    (s : ℂ) :
    (q : ℂ) ^ (k₁ * (t + 1 - k₂)) *
        (((q : ℝ) ^ (((r + 1 : ℕ) : ℤ) * k₂ - ((t + 1 : ℕ) : ℤ) * k₁) : ℝ) : ℂ) ^
          ((1 : ℂ) / 2 + s / ((r + t + 2 : ℕ) : ℂ)) *
        ((Real.sqrt q : ℝ) : ℂ) ^ (k₁ * (r + 1 - k₁)) *
        ((Real.sqrt q : ℝ) : ℂ) ^ (k₂ * (t + 1 - k₂)) =
      ((Real.sqrt q : ℝ) : ℂ) ^ ((k₁ + k₂) * (r + 1 + t + 1 - (k₁ + k₂))) *
        ((q : ℂ) ^ (-(s * ((t + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ)))) ^ k₁ *
        ((q : ℂ) ^ (s * ((r + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ))) ^ k₂ := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [Base.natCast_cpow_eq q hq, sqrt_pow_eq_cpow, sqrt_pow_eq_cpow, sqrt_pow_eq_cpow,
    ← Complex.cpow_natCast (q : ℂ) (k₁ * (t + 1 - k₂)), ← Complex.cpow_nat_mul,
    ← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0,
    ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]
  congr 1
  have hN : ((r + t + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : r + t + 2 ≠ 0)
  have e1 : ((k₁ * (t + 1 - k₂) : ℕ) : ℂ) = (k₁ : ℂ) * ((t : ℂ) + 1 - k₂) := by
    rw [Nat.cast_mul, Nat.cast_sub hk₂]
    push_cast
    ring
  have e2 : ((k₁ * (r + 1 - k₁) : ℕ) : ℂ) = (k₁ : ℂ) * ((r : ℂ) + 1 - k₁) := by
    rw [Nat.cast_mul, Nat.cast_sub hk₁]
    push_cast
    ring
  have e3 : ((k₂ * (t + 1 - k₂) : ℕ) : ℂ) = (k₂ : ℂ) * ((t : ℂ) + 1 - k₂) := by
    rw [Nat.cast_mul, Nat.cast_sub hk₂]
    push_cast
    ring
  have e4 : (((k₁ + k₂) * (r + 1 + t + 1 - (k₁ + k₂)) : ℕ) : ℂ) =
      ((k₁ : ℂ) + k₂) * ((r : ℂ) + 1 + t + 1 - (k₁ + k₂)) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [e1, e2, e3, e4]
  push_cast
  field_simp
  ring

end Powers

section Section

variable {ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology}
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
variable {r t : ℕ}

include hϖ in
theorem determinantNorm_unipotent_mul {n : ℕ} {u : Langlands.GeneralLinear n K.Carrier}
    (hu : u ∈ upperUnipotent n K.Carrier) (g : Langlands.GeneralLinear n K.Carrier) :
    ((K.canonicalTopologicalData.determinantNorm n (u * g) : NNReal) : ℝ) =
      ((K.canonicalTopologicalData.determinantNorm n g : NNReal) : ℝ) := by
  rw [map_mul, Units.val_mul, NNReal.coe_mul]
  have h := determinantNorm_unipotent_mul_torus K hϖ hu (0 : Fin n → ℤ)
  have h0 : Iwasawa.torus ϖ (0 : Fin n → ℤ) = 1 := by
    rw [Iwasawa.torus]
    simp only [Pi.zero_apply, zpow_zero]
    exact map_one Iwasawa.diagonalUnits
  rw [h0, mul_one] at h
  rw [h]
  simp

include hϖ in
theorem twoBlockModulus_torus (μ₁ : Fin (r + 1) → ℤ) (μ₂ : Fin (t + 1) → ℤ) :
    twoBlockModulus K (Iwasawa.torus ϖ μ₁) (Iwasawa.torus ϖ μ₂) =
      (K.canonicalTopologicalData.residueCardinality : ℝ) ^
        (((r + 1 : ℕ) : ℤ) * ∑ j, μ₂ j - ((t + 1 : ℕ) : ℤ) * ∑ i, μ₁ i) := by
  have hq : (K.canonicalTopologicalData.residueCardinality : ℝ) ≠ 0 := by
    have := residueCardinality_pos K
    positivity
  have h₁ := determinantNorm_unipotent_mul_torus K hϖ (one_mem _) μ₁
  have h₂ := determinantNorm_unipotent_mul_torus K hϖ (one_mem _) μ₂
  rw [one_mul] at h₁ h₂
  rw [twoBlockModulus, h₁, h₂, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
    ← zpow_sub₀ hq]
  congr 1
  push_cast
  ring

theorem sum_subsetExponent {m : ℕ} (S : Finset (Fin m)) :
    ∑ i, subsetExponent S i = (S.card : ℤ) := by
  simp only [subsetExponent]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

include hϖ in
theorem isLeviEquivariant_fullΦ (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ) :
    IsLeviEquivariant (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
      (Base.fullΦ ψ hϖ a c s) := by
  intro u₁ u₂ m₁ m₂
  simp only [Base.fullΦ, twoBlockModulus, determinantNorm_unipotent_mul hϖ u₁.2,
    determinantNorm_unipotent_mul hϖ u₂.2]
  rw [GeneralLinear.Spherical.sphericalWhittaker_mem hϖ _ a
      (isIntegrallyTrivial_of_additiveConductor K hψ r) u₁ m₁,
    GeneralLinear.Spherical.sphericalWhittaker_mem hϖ _ c
      (isIntegrallyTrivial_of_additiveConductor K hψ t) u₂ m₂]
  ring

/-- The Hecke relation of a spherical Whittaker function at a dominant torus point, in subset
form, for `ψ` of conductor `𝒪` and a system of representatives `σ` of the residue field. -/
theorem sum_sphericalWhittaker_torus_subsetExponent {n : ℕ}
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) (x : Fin (n + 1) → ℂˣ)
    {Λ : Type*} [Fintype Λ] (σ : Λ → K.Carrier)
    (hcard : Fintype.card Λ = K.canonicalTopologicalData.residueCardinality)
    (hσ : ∀ x, σ x ∈ (ValuativeRel.valuation K.Carrier).integer)
    (hinj : ∀ x y, ValuativeRel.valuation K.Carrier (σ x - σ y) < 1 → x = y)
    (hsurj : ∀ z ∈ (ValuativeRel.valuation K.Carrier).integer,
      ∃ x, ValuativeRel.valuation K.Carrier (z - σ x) < 1)
    {ν : Fin (n + 1) → ℤ} (hν : Antitone ν) (k : ℕ) :
    ∑ S : {S : Finset (Fin (n + 1)) // S.card = k},
        (K.canonicalTopologicalData.residueCardinality : ℂ) ^ Fintype.card (RadicalPairs S.1) *
          GeneralLinear.Spherical.sphericalWhittaker hϖ
            (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ n)
            K.canonicalTopologicalData.residueCardinality x
            (Iwasawa.torus ϖ (ν + subsetExponent S.1)) =
      ((Real.sqrt (K.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) ^ (k * (n + 1 - k)) *
        Langlands.Unramified.elementaryCoefficient
          (Langlands.Unramified.Eigenvalues.ofTuple x) k) *
        GeneralLinear.Spherical.sphericalWhittaker hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ n)
          K.canonicalTopologicalData.residueCardinality x (Iwasawa.torus ϖ ν) := by
  have hψI := RankinSelberg.HighlyRamified.hasIntegerConductor_of_additiveConductor_eq_zero K ψ hψ
  have hθK := isIntegrallyTrivial_of_additiveConductor K hψ n
  have h1 := RankinSelberg.UnramifiedWhittaker.sum_eval_torus_mul_labelledRep (Λ := Λ) hϖ.1.le
    hθK (fun u g => GeneralLinear.Spherical.sphericalWhittaker_mem hϖ
      K.canonicalTopologicalData.residueCardinality x hθK u g) hσ hν k
  have h2 := sum_sphericalWhittaker_mul_labelledRep hϖ (residueCardinality_pos K) hcard σ hσ hinj
    hsurj hθK (fun i => Base.standardCharacter_nondegenerate' hϖ hψI i) x k (Iwasawa.torus ϖ ν)
  rw [h1, hcard] at h2
  exact h2

include hϖ in
/-- The Levi function at shifted block torus points. -/
theorem fullΦ_torus_add (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    (ν₁ : Fin (r + 1) → ℤ) (ν₂ : Fin (t + 1) → ℤ) (S₁ : Finset (Fin (r + 1)))
    (S₂ : Finset (Fin (t + 1))) :
    Base.fullΦ ψ hϖ a c s (Iwasawa.torus ϖ (ν₁ + subsetExponent S₁))
        (Iwasawa.torus ϖ (ν₂ + subsetExponent S₂)) =
      (((K.canonicalTopologicalData.residueCardinality : ℝ) ^
          (((r + 1 : ℕ) : ℤ) * S₂.card - ((t + 1 : ℕ) : ℤ) * S₁.card) : ℝ) : ℂ) ^
          ((1 : ℂ) / 2 + s / ((r + t + 2 : ℕ) : ℂ)) *
        (((twoBlockModulus K (Iwasawa.torus ϖ ν₁) (Iwasawa.torus ϖ ν₂) : ℝ) : ℂ) ^
          ((1 : ℂ) / 2 + s / ((r + t + 2 : ℕ) : ℂ))) *
        GeneralLinear.Spherical.sphericalWhittaker (n := r) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
          K.canonicalTopologicalData.residueCardinality a
          (Iwasawa.torus ϖ (ν₁ + subsetExponent S₁)) *
        GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
          K.canonicalTopologicalData.residueCardinality c
          (Iwasawa.torus ϖ (ν₂ + subsetExponent S₂)) := by
  have hq : (0 : ℝ) < K.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast residueCardinality_pos K
  simp only [Base.fullΦ]
  rw [twoBlockModulus_torus hϖ, twoBlockModulus_torus hϖ]
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_subsetExponent, sum_subsetExponent]
  have e : (((r + 1 : ℕ) : ℤ) * (∑ j, ν₂ j + (S₂.card : ℤ)) -
      ((t + 1 : ℕ) : ℤ) * (∑ i, ν₁ i + (S₁.card : ℤ))) =
      (((r + 1 : ℕ) : ℤ) * S₂.card - ((t + 1 : ℕ) : ℤ) * S₁.card) +
        (((r + 1 : ℕ) : ℤ) * ∑ j, ν₂ j - ((t + 1 : ℕ) : ℤ) * ∑ i, ν₁ i) := by
    ring
  rw [e, zpow_add₀ hq.ne', Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (zpow_nonneg hq.le _) (zpow_nonneg hq.le _)]

include hϖ in
/-- The block-split coset sum for one pair of subset sizes, for `ψ` of conductor `𝒪` and a
system of representatives `σ` of the residue field. -/
theorem sum_fullΦ_torus_split (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    {Λ : Type*} [Fintype Λ] (σ : Λ → K.Carrier)
    (hcard : Fintype.card Λ = K.canonicalTopologicalData.residueCardinality)
    (hσ : ∀ x, σ x ∈ (ValuativeRel.valuation K.Carrier).integer)
    (hinj : ∀ x y, ValuativeRel.valuation K.Carrier (σ x - σ y) < 1 → x = y)
    (hsurj : ∀ z ∈ (ValuativeRel.valuation K.Carrier).integer,
      ∃ x, ValuativeRel.valuation K.Carrier (z - σ x) < 1)
    {ν₁ : Fin (r + 1) → ℤ} {ν₂ : Fin (t + 1) → ℤ} (h₁ : Antitone ν₁) (h₂ : Antitone ν₂)
    (k₁ k₂ : ℕ) :
    ∑ S₁ : {S₁ : Finset (Fin (r + 1)) // S₁.card = k₁},
      ∑ S₂ : {S₂ : Finset (Fin (t + 1)) // S₂.card = k₂},
        (K.canonicalTopologicalData.residueCardinality : ℂ) ^
            (Fintype.card (RadicalPairs S₁.1) + Fintype.card (RadicalPairs S₂.1) +
              S₁.1.card * (t + 1 - S₂.1.card)) *
          Base.fullΦ ψ hϖ a c s (Iwasawa.torus ϖ (ν₁ + subsetExponent S₁.1))
            (Iwasawa.torus ϖ (ν₂ + subsetExponent S₂.1)) =
      ((K.canonicalTopologicalData.residueCardinality : ℂ) ^ (k₁ * (t + 1 - k₂)) *
          (((K.canonicalTopologicalData.residueCardinality : ℝ) ^
            (((r + 1 : ℕ) : ℤ) * k₂ - ((t + 1 : ℕ) : ℤ) * k₁) : ℝ) : ℂ) ^
            ((1 : ℂ) / 2 + s / ((r + t + 2 : ℕ) : ℂ))) *
        (((Real.sqrt (K.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) ^
            (k₁ * (r + 1 - k₁)) *
          Langlands.Unramified.elementaryCoefficient
            (Langlands.Unramified.Eigenvalues.ofTuple a) k₁) *
        ((Real.sqrt (K.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) ^
            (k₂ * (t + 1 - k₂)) *
          Langlands.Unramified.elementaryCoefficient
            (Langlands.Unramified.Eigenvalues.ofTuple c) k₂)) *
        Base.fullΦ ψ hϖ a c s (Iwasawa.torus ϖ ν₁) (Iwasawa.torus ϖ ν₂) := by
  have hA := sum_sphericalWhittaker_torus_subsetExponent hϖ hψ a σ hcard hσ hinj hsurj h₁ k₁
  have hC := sum_sphericalWhittaker_torus_subsetExponent hϖ hψ c σ hcard hσ hinj hsurj h₂ k₂
  have hrhs : ∀ X E₁ E₂ : ℂ, X * (E₁ * E₂) * Base.fullΦ ψ hϖ a c s (Iwasawa.torus ϖ ν₁)
        (Iwasawa.torus ϖ ν₂) =
      (X * ((twoBlockModulus K (Iwasawa.torus ϖ ν₁) (Iwasawa.torus ϖ ν₂) : ℝ) : ℂ) ^
          ((1 : ℂ) / 2 + s / ((r + t + 2 : ℕ) : ℂ))) *
        (E₁ * GeneralLinear.Spherical.sphericalWhittaker (n := r) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
          K.canonicalTopologicalData.residueCardinality a (Iwasawa.torus ϖ ν₁)) *
        (E₂ * GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
          K.canonicalTopologicalData.residueCardinality c (Iwasawa.torus ϖ ν₂)) := by
    intro X E₁ E₂
    simp only [Base.fullΦ]
    ring
  rw [hrhs, ← hA, ← hC, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S₂ _ => ?_
  rw [fullΦ_torus_add hϖ, S₁.2, S₂.2]
  ring

include hϖ in
/-- **The minuscule Hecke relation at block-dominant torus points**, for `ψ` of conductor `𝒪`
and a system of representatives `σ` of the residue field. -/
theorem sum_liftFunction_fullΦ_torus (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    {Λ : Type*} [Fintype Λ] (σ : Λ → K.Carrier)
    (hcard : Fintype.card Λ = K.canonicalTopologicalData.residueCardinality)
    (hσ : ∀ x, σ x ∈ (ValuativeRel.valuation K.Carrier).integer)
    (hinj : ∀ x y, ValuativeRel.valuation K.Carrier (σ x - σ y) < 1 → x = y)
    (hsurj : ∀ z ∈ (ValuativeRel.valuation K.Carrier).integer,
      ∃ x, ValuativeRel.valuation K.Carrier (z - σ x) < 1)
    {ν : Fin ((r + 1) + (t + 1)) → ℤ} (h₁ : Antitone fun i : Fin (r + 1) => ν (i.castAdd (t + 1)))
    (h₂ : Antitone fun j : Fin (t + 1) => ν (j.natAdd (r + 1))) (k : ℕ) :
    ∑ α : CosetIndex Λ ((r + 1) + (t + 1)) k,
        liftFunction hϖ (Base.fullΦ ψ hϖ a c s) (Iwasawa.torus ϖ ν * labelledRep ϖ σ α) =
      ((Real.sqrt (K.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) ^
          (k * (r + 1 + t + 1 - k)) *
        Langlands.Unramified.elementaryCoefficient
          (Langlands.Unramified.Eigenvalues.ofTuple (sectionParameter K a c s)) k) *
        liftFunction hϖ (Base.fullΦ ψ hϖ a c s) (Iwasawa.torus ϖ ν) := by
  set q := K.canonicalTopologicalData.residueCardinality with hq
  have hΦ := Base.isLeviInvariant_fullΦ hϖ hψ a c s
  have hθ := isLeviEquivariant_fullΦ hϖ hψ a c s
  rw [sum_liftFunction_torus_mul_labelledRep hϖ hΦ hθ
    (isIntegrallyTrivial_of_additiveConductor K hψ r)
    (isIntegrallyTrivial_of_additiveConductor K hψ t) hσ h₁ h₂ k, hcard]
  simp only [liftFunction_torus hϖ hΦ]
  set ν₁ : Fin (r + 1) → ℤ := fun i => ν (i.castAdd (t + 1)) with hν₁
  set ν₂ : Fin (t + 1) → ℤ := fun j => ν (j.natAdd (r + 1)) with hν₂
  have e₁ : ∀ S : Finset (Fin ((r + 1) + (t + 1))),
      (fun i : Fin (r + 1) => (ν + subsetExponent S) (i.castAdd (t + 1))) =
        ν₁ + subsetExponent (firstPart S) := by
    intro S
    funext i
    simp [ν₁, subsetExponent, mem_firstPart]
  have e₂ : ∀ S : Finset (Fin ((r + 1) + (t + 1))),
      (fun j : Fin (t + 1) => (ν + subsetExponent S) (j.natAdd (r + 1))) =
        ν₂ + subsetExponent (secondPart S) := by
    intro S
    funext j
    simp [ν₂, subsetExponent, mem_secondPart]
  simp only [e₁, e₂, card_radicalPairs_split (m := r + 1) (n := t + 1)]
  have hsplit := sum_card_eq_split (R := ℂ) k (fun S₁ S₂ =>
    (q : ℂ) ^ (Fintype.card (RadicalPairs S₁) + Fintype.card (RadicalPairs S₂) +
      S₁.card * (t + 1 - S₂.card)) *
      Base.fullΦ ψ hϖ a c s (Iwasawa.torus ϖ (ν₁ + subsetExponent S₁))
        (Iwasawa.torus ϖ (ν₂ + subsetExponent S₂)))
  rw [hsplit, Langlands.Unramified.elementaryCoefficient_ofTuple]
  simp only [prod_mem_split (m := r + 1) (n := t + 1)]
  have hsplit2 := sum_card_eq_split (R := ℂ) k (fun S₁ S₂ =>
    (∏ i ∈ S₁, (sectionParameter K a c s (i.castAdd (t + 1)) : ℂ)) *
      ∏ j ∈ S₂, (sectionParameter K a c s (j.natAdd (r + 1)) : ℂ))
  rw [hsplit2, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hk : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  by_cases hp₁ : p.1 ≤ r + 1
  · by_cases hp₂ : p.2 ≤ t + 1
    · rw [sum_fullΦ_torus_split hϖ hψ a c s σ hcard hσ hinj hsurj h₁ h₂ p.1 p.2]
      set u₁ := (q : ℂ) ^ (-(s * ((t + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ)))
      set u₂ := (q : ℂ) ^ (s * ((r + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ))
      have hsum : ∑ S₁ : {S₁ : Finset (Fin (r + 1)) // S₁.card = p.1},
          ∑ S₂ : {S₂ : Finset (Fin (t + 1)) // S₂.card = p.2},
            (∏ i ∈ S₁.1, (sectionParameter K a c s (i.castAdd (t + 1)) : ℂ)) *
              ∏ j ∈ S₂.1, (sectionParameter K a c s (j.natAdd (r + 1)) : ℂ) =
          (Langlands.Unramified.elementaryCoefficient
              (Langlands.Unramified.Eigenvalues.ofTuple a) p.1 * u₁ ^ p.1) *
            (Langlands.Unramified.elementaryCoefficient
              (Langlands.Unramified.Eigenvalues.ofTuple c) p.2 * u₂ ^ p.2) := by
        rw [Langlands.Unramified.elementaryCoefficient_ofTuple,
          Langlands.Unramified.elementaryCoefficient_ofTuple]
        simp only [Finset.sum_mul, Finset.mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun S₁ _ => ?_
        refine Finset.sum_congr rfl fun S₂ _ => ?_
        simp only [sectionParameter_castAdd, sectionParameter_natAdd, Finset.prod_mul_distrib,
          Finset.prod_const, S₁.2, S₂.2]
        rfl
      rw [hsum]
      have hscalar := heckeScalar_eq q (residueCardinality_pos K) r t p.1 p.2 hp₁ hp₂ s
      rw [hk] at hscalar
      rw [← hk] at *
      linear_combination
        (Langlands.Unramified.elementaryCoefficient
            (Langlands.Unramified.Eigenvalues.ofTuple a) p.1 *
          Langlands.Unramified.elementaryCoefficient
            (Langlands.Unramified.Eigenvalues.ofTuple c) p.2 *
          Base.fullΦ ψ hϖ a c s (Iwasawa.torus ϖ ν₁) (Iwasawa.torus ϖ ν₂)) * hscalar
    · have : IsEmpty {S₂ : Finset (Fin (t + 1)) // S₂.card = p.2} :=
        ⟨fun S => hp₂ (S.2 ▸ (Finset.card_le_univ _).trans (by simp))⟩
      simp [Finset.univ_eq_empty]
  · have : IsEmpty {S₁ : Finset (Fin (r + 1)) // S₁.card = p.1} :=
      ⟨fun S => hp₁ (S.2 ▸ (Finset.card_le_univ _).trans (by simp))⟩
    simp [Finset.univ_eq_empty]

end Section

end Langlands.Shahidi.OpenCell
