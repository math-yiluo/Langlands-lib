import Langlands.Representation.Shahidi.OpenCellShellSum
import Langlands.Representation.Shahidi.OpenCellPowerSeries

/-! # Product Levi functions, the rank-one shells for Whittaker-type test functions, and the
graded Shintani identity

`prodΦ s Ψ₁ Ψ₂ = δ_P^(1/2 + s/N) Ψ₁ ⊗ Ψ₂`; the two-block section is `prodΦ s W°_a W°_c`. For a
first block of rank one and any Whittaker-type `Ψ` on the second block, the Jacquet function at
`1` of the degree-`e` piece of `prodΦ s W°_a Ψ` is the explicit rank-one shell value (for `ψ` of
conductor `𝒪`). If `ψ` has conductor `𝒪` and the shell identities hold for a pair of ranks at
`s = 0`, then for small `X` the degree pieces of the
section with parameters `(a, c, 0)` satisfy
`∑_e X^e J_e(g) = ∏_(i,j) (1 - X a_i c_j⁻¹ q⁻¹) · W°(g; (X a, c))` at every point `g`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor Langlands.GeneralLinear.Spherical
open Langlands.GeneralLinear.Iwasawa MeasureTheory
open scoped ENNReal NNReal

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocGradedTopologicalSpace : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance ocGradedValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocGradedLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance ocGradedT2Space : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocGradedSecondCountableTopology : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocGradedMeasurableSpace : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocGradedBorelSpace : BorelSpace K.Carrier := ⟨rfl⟩

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology)
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
variable {r t : ℕ}

section Product

/-- The product Levi function `δ_P(m₁, m₂)^(1/2 + s/N) Ψ₁(m₁) Ψ₂(m₂)`, `N = r + t + 2`. -/
def prodΦ (s : ℂ) (Ψ₁ : Langlands.GeneralLinear (r + 1) K.Carrier → ℂ)
    (Ψ₂ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ)
    (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier) (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) :
    ℂ :=
  ((twoBlockModulus K m₁ m₂ : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + s / ((r + t + 2 : ℕ) : ℂ)) * Ψ₁ m₁ * Ψ₂ m₂

theorem fullΦ_eq_prodΦ (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ) :
    Base.fullΦ ψ hϖ a c s = prodΦ s
      (GeneralLinear.Spherical.sphericalWhittaker (n := r) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
        K.canonicalTopologicalData.residueCardinality a)
      (GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
        K.canonicalTopologicalData.residueCardinality c) := rfl

theorem isLeviInvariant_prodΦ (s : ℂ) {Ψ₁ : Langlands.GeneralLinear (r + 1) K.Carrier → ℂ}
    {Ψ₂ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}
    (h₁ : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers r, Ψ₁ (g * k) = Ψ₁ g)
    (h₂ : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers t, Ψ₂ (g * k) = Ψ₂ g) :
    IsLeviInvariant (prodΦ (K := K) s Ψ₁ Ψ₂) := by
  intro m₁ μ₁ m₂ μ₂ hμ₁ hμ₂
  simp only [prodΦ, twoBlockModulus, Base.determinantNorm_mul_integral' m₁ μ₁ hμ₁,
    Base.determinantNorm_mul_integral' m₂ μ₂ hμ₂, h₁ m₁ μ₁ hμ₁, h₂ m₂ μ₂ hμ₂]

end Product

section RankOne

variable {ψ} {t : ℕ}

include hϖ in
/-- **The product Levi function on a rank-one shell**, for `ψ` of conductor `𝒪` and `Ψ` right
invariant under `GL_(t+1)(𝒪)`. -/
theorem liftFunction_prodΦ_eq (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (a : Fin (0 + 1) → ℂˣ) (s : ℂ) {Ψ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}
    (hΨ : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers t, Ψ (g * k) = Ψ g)
    (Y : Matrix (Fin (t + 1)) (Fin (0 + 1)) K.Carrier) {D : ℕ} (hD : openCellDepth hϖ Y = D) :
    liftFunction hϖ (prodΦ s (GeneralLinear.Spherical.sphericalWhittaker (n := 0) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ 0)
        K.canonicalTopologicalData.residueCardinality a) Ψ) (lower (0 + 1) (t + 1) K.Carrier Y) =
      Base.baseCoef (K := K) t D a s * liftFunction hϖ (Base.shellΦ D Ψ)
        (lower (0 + 1) (t + 1) K.Carrier Y) := by
  have hW1 : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers 0,
      GeneralLinear.Spherical.sphericalWhittaker (n := 0) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ 0)
        K.canonicalTopologicalData.residueCardinality a (g * k) =
      GeneralLinear.Spherical.sphericalWhittaker (n := 0) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ 0)
        K.canonicalTopologicalData.residueCardinality a g := fun g _k hk =>
    GeneralLinear.Spherical.sphericalWhittaker_mul_integral hϖ _ a
      (isIntegrallyTrivial_of_additiveConductor K hψ 0) g hk
  obtain ⟨u₁, hu₁, u₂, hu₂, h⟩ := liftFunction_lower hϖ
    (Base.isLeviInvariant_sub_mul (isLeviInvariant_prodΦ s hW1 hΨ)
      (Base.isLeviInvariant_shellΦ (D : ℤ) hΨ) (Base.baseCoef (K := K) t D a s)) Y
  rw [Base.liftFunction_sub_mul] at h
  rw [← sub_eq_zero, h]
  set q := (K.canonicalTopologicalData.residueCardinality : ℝ)
  have hq : q ≠ 0 := by
    have := K.canonicalTopologicalData.residueCardinality_gt_one
    positivity
  have hlam : openCellExponent hϖ Y (Fin.castAdd (t + 1) (0 : Fin (0 + 1))) = D := by
    have := hD
    rw [openCellDepth, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at this
    exact this
  have hsumlam : ∑ i : Fin (0 + 1), openCellExponent hϖ Y (i.castAdd (t + 1)) = D := hD
  have hsummu : ∑ j : Fin (t + 1), openCellExponent hϖ Y (j.natAdd (0 + 1)) = -(D : ℤ) := by
    rw [sum_openCellExponent_natAdd, hD]
  have hd1 := determinantNorm_unipotent_mul_torus K hϖ hu₁
    (fun i : Fin (0 + 1) => openCellExponent hϖ Y (i.castAdd (t + 1)))
  have hd2 := determinantNorm_unipotent_mul_torus K hϖ hu₂
    (fun j : Fin (t + 1) => openCellExponent hϖ Y (j.natAdd (0 + 1)))
  rw [hsumlam] at hd1
  rw [hsummu, neg_neg] at hd2
  have hmod : twoBlockModulus K
      (u₁ * Iwasawa.torus ϖ fun i : Fin (0 + 1) => openCellExponent hϖ Y (i.castAdd (t + 1)))
      (u₂ * Iwasawa.torus ϖ fun j : Fin (t + 1) => openCellExponent hϖ Y (j.natAdd (0 + 1))) =
      q ^ (-(((0 + t + 2 : ℕ) : ℤ) * (D : ℤ))) := by
    rw [twoBlockModulus, hd1, hd2, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      ← zpow_sub₀ hq]
    congr 1
    push_cast
    ring
  simp only [prodΦ, Base.shellΦ, Base.baseCoef]
  rw [hmod, hd1, ite_eq_left_iff.2 (fun h => absurd rfl h), Base.sphericalWhittaker_rankOne hϖ hψ a hu₁,
    hlam, zpow_natCast]
  simp only [q]
  ring

include hϖ in
/-- **The rank-one shells for a Whittaker-type test function**, for `ψ` of conductor `𝒪`. -/
theorem jacquetFunction_degreePiece_prodΦ_rankOne
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (a : Fin (0 + 1) → ℂˣ) (s : ℂ) {Ψ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}
    (hΨ : Base.IsWhittakerType ψ Ψ) (D : ℕ) :
    jacquetFunction ψ hϖ (degreePiece hϖ D (prodΦ s
        (GeneralLinear.Spherical.sphericalWhittaker (n := 0) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ 0)
          K.canonicalTopologicalData.residueCardinality a) Ψ)) 1 =
      Base.baseCoef (K := K) t D a s * Base.baseValue ϖ t D Ψ := by
  have hψI := RankinSelberg.HighlyRamified.hasIntegerConductor_of_additiveConductor_eq_zero K ψ hψ
  have hW1 : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers 0,
      GeneralLinear.Spherical.sphericalWhittaker (n := 0) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ 0)
        K.canonicalTopologicalData.residueCardinality a (g * k) =
      GeneralLinear.Spherical.sphericalWhittaker (n := 0) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ 0)
        K.canonicalTopologicalData.residueCardinality a g := fun g _k hk =>
    GeneralLinear.Spherical.sphericalWhittaker_mul_integral hϖ _ a
      (isIntegrallyTrivial_of_additiveConductor K hψ 0) g hk
  have hΦ := isLeviInvariant_prodΦ s hW1 hΨ.2
  have e : jacquetIntegrandAt ψ hϖ (degreePiece hϖ D (prodΦ s
      (GeneralLinear.Spherical.sphericalWhittaker (n := 0) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ 0)
        K.canonicalTopologicalData.residueCardinality a) Ψ)) 1 =
      fun Y => Base.baseCoef (K := K) t D a s * Base.baseIntegrand ψ hϖ (D : ℤ) Ψ Y := by
    funext Y
    rw [jacquetIntegrandAt_degreePiece_one ψ hϖ hΦ]
    split_ifs with h
    · rw [liftFunction_prodΦ_eq hϖ hψ a s hΨ.2 Y h, Base.baseIntegrand,
        intertwiningJacquetKernel_eq_conj]
      ring
    · rw [Base.baseIntegrand_eq_zero_of_depth_ne hϖ hΨ.2 Y h, mul_zero]
  rw [jacquetFunction, e, integral_const_mul, Base.integral_baseIntegrand hϖ hψI t (D : ℤ) hΨ]

end RankOne

section Graded

variable {ψ}

theorem torus_zero_eq_one {n : ℕ} : Iwasawa.torus ϖ (0 : Fin n → ℤ) = 1 := by
  rw [Iwasawa.torus]
  simp only [Pi.zero_apply, zpow_zero]
  exact map_one Iwasawa.diagonalUnits

theorem sectionParameter_zero (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) :
    sectionParameter K a c 0 = Fin.append a c := by
  funext i
  induction i using Fin.addCases with
  | left i =>
    apply Units.ext
    simp [sectionParameter]
  | right j =>
    apply Units.ext
    simp [sectionParameter]

theorem pairParameter_smul (q : ℕ) (X : ℂˣ) (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    (x : Fin (r + 1) × Fin (t + 1)) :
    pairParameter q (fun i => X * a i) c s x = (X : ℂ) * pairParameter q a c s x := by
  simp only [pairParameter, Units.val_mul]
  ring

variable (ψ) in
/-- The shell identities at `s = 0` for one pair of ranks, as identities of degree pieces. -/
def CoreAt (r t : ℕ) : Prop :=
  ∀ (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (D : ℕ),
    jacquetFunction ψ hϖ (degreePiece hϖ D (Base.fullΦ ψ hϖ a c 0)) 1 =
      shellCoefficient (pairParameter K.canonicalTopologicalData.residueCardinality a c 0) D

/-- **The Jacquet function at `1` from the shell identities**, for small first parameters and `ψ`
of conductor `𝒪`. -/
theorem jacquetFunction_one_eq_prod_of_core
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) (hcore : CoreAt ψ hϖ r t)
    (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ X : ℂˣ, ‖(X : ℂ)‖ < r₀ →
      jacquetFunction ψ hϖ (Base.fullΦ ψ hϖ (fun i => X * a i) c 0) 1 =
        ∏ x, (1 - (X : ℂ) * pairParameter K.canonicalTopologicalData.residueCardinality a c 0 x) := by
  obtain ⟨r₀, hr₀, hint⟩ := exists_integrable_jacquetIntegrandAt_fullΦ ψ hϖ hψ a c 0
  refine ⟨r₀, hr₀, fun X hX => ?_⟩
  have hΦ := Base.isLeviInvariant_fullΦ hϖ hψ (fun i => X * a i) c 0
  have h1 := hasSum_jacquetFunction_degreePiece_torus ψ hϖ hΦ 0 (hint X hX 0)
  rw [torus_zero_eq_one] at h1
  have hn := hasSum_shellCoefficient
    (pairParameter K.canonicalTopologicalData.residueCardinality (fun i => X * a i) c 0)
  have h2 : HasSum (fun e : ℤ => jacquetFunction ψ hϖ
      (degreePiece hϖ e (Base.fullΦ ψ hϖ (fun i => X * a i) c 0)) 1)
      (∏ x, (1 - pairParameter K.canonicalTopologicalData.residueCardinality
        (fun i => X * a i) c 0 x)) := by
    have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := Nat.cast_injective
    refine (hinj.hasSum_iff ?_).1 ?_
    · intro x hx
      apply jacquetFunction_degreePiece_one_of_neg ψ hϖ hψ hΦ
      by_contra hx'
      exact hx ⟨x.toNat, by simp only; omega⟩
    · convert hn using 1
      funext n
      exact hcore _ c n
  rw [h1.unique h2]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [pairParameter_smul]

/-- **The graded Shintani identity from the shell identities**, for `ψ` of conductor `𝒪`. -/
theorem exists_hasSum_degreePiece_of_core
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) (hcore : CoreAt ψ hϖ r t)
    (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ X : ℂˣ, ‖(X : ℂ)‖ < r₀ →
      ∀ g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier,
        HasSum (fun e : ℤ => (X : ℂ) ^ e *
            jacquetFunction ψ hϖ (degreePiece hϖ e (Base.fullΦ ψ hϖ a c 0)) g)
          ((∏ x, (1 - (X : ℂ) * pairParameter K.canonicalTopologicalData.residueCardinality a c 0 x)) *
            GeneralLinear.Spherical.sphericalWhittaker (n := r + 1 + t) hϖ
              (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ (r + 1 + t))
              K.canonicalTopologicalData.residueCardinality
              (Fin.append (m := r + 1) (n := t + 1) (fun i => X * a i) c) g) := by
  obtain ⟨r₁, hr₁, h₁⟩ := exists_hasSum_degreePiece ψ hϖ hψ a c 0
  obtain ⟨r₂, hr₂, h₂⟩ := jacquetFunction_one_eq_prod_of_core hϖ hψ hcore a c
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun X hX g => ?_⟩
  have h := h₁ X (lt_of_lt_of_le hX (min_le_left _ _)) g
  rw [h₂ X (lt_of_lt_of_le hX (min_le_right _ _)), sectionParameter_zero] at h
  exact h

end Graded

end Langlands.Shahidi.OpenCell
