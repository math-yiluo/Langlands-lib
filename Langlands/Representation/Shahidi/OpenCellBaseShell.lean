import Langlands.Representation.Shahidi.OpenCellBaseSchur
import Langlands.Representation.Shahidi.OpenCellBaseCoef
import Langlands.Representation.Shahidi.OpenCellAssembly

/-! # The shell identities for the `(1, n)` parabolic

For `ψ` of conductor `𝒪` and the section `f` of the target statement with first block of rank
one, the classes of depth
`D` of the open-cell sum add up to `(-a q^(-(1+s)))^D e_D(c⁻¹)`, the degree-`D` part of
`∏_j (1 - a c_j⁻¹ q^(-(1+s)))`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell.Base

open Langlands.GeneralLinear Langlands.Conductor MeasureTheory
open scoped NNReal

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocBaseShellTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance ocBaseShellValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocBaseShellLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance ocBaseShellT2 : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocBaseShellSecondCountable : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocBaseShellMeasurable : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocBaseShellBorel : BorelSpace K.Carrier := ⟨rfl⟩

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology)
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)

section Levi

variable {r t : ℕ}

/-- The Levi function `δ_P(m₁, m₂)^(1/2 + s/N) W°(m₁; a) W°(m₂; c)` of the target statement. -/
def fullΦ (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier) (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) :
    ℂ :=
  ((twoBlockModulus K m₁ m₂ : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + s / ((r + t + 2 : ℕ) : ℂ)) *
    GeneralLinear.Spherical.sphericalWhittaker (n := r) hϖ
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
      K.canonicalTopologicalData.residueCardinality a m₁ *
    GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
      K.canonicalTopologicalData.residueCardinality c m₂

variable {ψ}

theorem isLeviInvariant_fullΦ (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ) :
    IsLeviInvariant (fullΦ ψ hϖ a c s) := by
  intro m₁ μ₁ m₂ μ₂ hμ₁ hμ₂
  simp only [fullΦ, twoBlockModulus, determinantNorm_mul_integral' m₁ μ₁ hμ₁,
    determinantNorm_mul_integral' m₂ μ₂ hμ₂,
    GeneralLinear.Spherical.sphericalWhittaker_mul_integral hϖ _ _
      (isIntegrallyTrivial_of_additiveConductor K hψ r) m₁ hμ₁,
    GeneralLinear.Spherical.sphericalWhittaker_mul_integral hϖ _ _
      (isIntegrallyTrivial_of_additiveConductor K hψ t) m₂ hμ₂]

theorem eq_liftFunction_of_isOpenCellSection
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) {a : Fin (r + 1) → ℂˣ}
    {c : Fin (t + 1) → ℂˣ} {s : ℂ} {f : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier → ℂ}
    (hf : IsOpenCellSection K ψ hϖ a c s f) : f = liftFunction hϖ (fullΦ ψ hϖ a c s) :=
  eq_liftFunction hϖ (isLeviInvariant_fullΦ hϖ hψ a c s) hf

theorem openCellSummand_eq_lower (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    {a : Fin (r + 1) → ℂˣ} {c : Fin (t + 1) → ℂˣ} {s : ℂ}
    {f : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier → ℂ}
    (hf : IsOpenCellSection K ψ hϖ a c s f) (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) :
    openCellSummand K ψ f Y =
      liftFunction hϖ (fullΦ ψ hϖ a c s) (lower (r + 1) (t + 1) K.Carrier Y) *
        starRingEnd ℂ (ψ (Y (Fin.last t) 0) : ℂ) := by
  rw [openCellSummand, eq_liftFunction_of_isOpenCellSection hϖ hψ hf,
    blockWeyl_mul_intertwiningUnipotent,
    liftFunction_mul_integral hϖ (isLeviInvariant_fullΦ hϖ hψ a c s) _ _
      (blockWeyl_mem_integralSubgroup K r t)]

/-- Lifts are evaluations at a common Levi pair, hence linear in the Levi function. -/
theorem liftFunction_sub_mul (Φ Φ' : Langlands.GeneralLinear (r + 1) K.Carrier →
      Langlands.GeneralLinear (t + 1) K.Carrier → ℂ) (z : ℂ)
    (x : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    liftFunction hϖ (fun m₁ m₂ => Φ m₁ m₂ - z * Φ' m₁ m₂) x =
      liftFunction hϖ Φ x - z * liftFunction hϖ Φ' x := rfl

theorem isLeviInvariant_sub_mul {Φ Φ' : Langlands.GeneralLinear (r + 1) K.Carrier →
      Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}
    (hΦ : IsLeviInvariant Φ) (hΦ' : IsLeviInvariant Φ') (z : ℂ) :
    IsLeviInvariant (fun m₁ m₂ => Φ m₁ m₂ - z * Φ' m₁ m₂) := by
  intro m₁ μ₁ m₂ μ₂ hμ₁ hμ₂
  simp only [hΦ _ _ _ _ hμ₁ hμ₂, hΦ' _ _ _ _ hμ₁ hμ₂]

end Levi

section RankOne

variable {ψ}

theorem sphericalWhittaker_rankOne (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (a : Fin (0 + 1) → ℂˣ) {u : Langlands.GeneralLinear (0 + 1) K.Carrier}
    (hu : u ∈ upperUnipotent (0 + 1) K.Carrier) (lam : Fin (0 + 1) → ℤ) :
    GeneralLinear.Spherical.sphericalWhittaker (n := 0) hϖ
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ 0)
      K.canonicalTopologicalData.residueCardinality a (u * Iwasawa.torus ϖ lam) =
      (a 0 : ℂ) ^ lam 0 := by
  have hanti : Antitone lam := by
    intro i j _
    rw [zero_fin_one i, zero_fin_one j]
  rw [sphericalWhittaker_unipotent_mul_torus hϖ (isIntegrallyTrivial_of_additiveConductor K hψ 0)
    _ a hu hanti]
  have hθ : (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ 0 ⟨u, hu⟩ : ℂ) =
      1 := by
    rw [Whittaker.standardCharacter_apply, Finset.univ_eq_empty, Finset.sum_empty,
      HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, AddChar.map_zero_eq_one]
    rfl
  have hhm : GeneralLinear.Spherical.halfModulus K.canonicalTopologicalData.residueCardinality lam =
      1 := by
    simp [GeneralLinear.Spherical.halfModulus]
  have hsch : GeneralLinear.Spherical.satakeSchur a lam = (a 0 : ℂ) ^ lam 0 := by
    have hz : (fun i : Fin (0 + 1) => lam i - lam (Fin.last 0)) = 0 := by
      funext i
      rw [zero_fin_one i]
      simp
    rw [GeneralLinear.Spherical.satakeSchur, hz, GeneralLinear.Spherical.jacobiTrudi_zero, map_one,
      mul_one, Fin.prod_univ_one]
    rfl
  rw [hθ, hhm, hsch, one_mul, one_mul]

end RankOne

section Shell

variable {ψ} {t : ℕ}

/-- The constant `δ_P^(1/2+s/N) W°(·; a)` on the shell of depth `D`. -/
def baseCoef (t D : ℕ) (a : Fin (0 + 1) → ℂˣ) (s : ℂ) : ℂ :=
  ((((K.canonicalTopologicalData.residueCardinality : ℝ) ^
      (-(((0 + t + 2 : ℕ) : ℤ) * (D : ℤ))) : ℝ) : ℂ) ^
      ((1 : ℂ) / 2 + s / ((0 + t + 2 : ℕ) : ℂ))) * (a 0 : ℂ) ^ D

theorem isWhittakerType_sphericalWhittaker (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (c : Fin (t + 1) → ℂˣ) :
    IsWhittakerType ψ (GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
      K.canonicalTopologicalData.residueCardinality c) :=
  ⟨fun u g => GeneralLinear.Spherical.sphericalWhittaker_mem hϖ _ c
      (isIntegrallyTrivial_of_additiveConductor K hψ t) u g,
    fun g _k hk => GeneralLinear.Spherical.sphericalWhittaker_mul_integral hϖ _ c
      (isIntegrallyTrivial_of_additiveConductor K hψ t) g hk⟩

/-- **The section on a shell** (for `ψ` of conductor `𝒪`, first block of rank one). -/
theorem liftFunction_fullΦ_eq (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (a : Fin (0 + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    (Y : Matrix (Fin (t + 1)) (Fin (0 + 1)) K.Carrier) {D : ℕ} (hD : openCellDepth hϖ Y = D) :
    liftFunction hϖ (fullΦ ψ hϖ a c s) (lower (0 + 1) (t + 1) K.Carrier Y) =
      baseCoef (K := K) t D a s * liftFunction hϖ (shellΦ D
        (GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
          K.canonicalTopologicalData.residueCardinality c)) (lower (0 + 1) (t + 1) K.Carrier Y) := by
  have hW := isWhittakerType_sphericalWhittaker hϖ hψ c
  obtain ⟨u₁, hu₁, u₂, hu₂, h⟩ := liftFunction_lower hϖ
    (isLeviInvariant_sub_mul (isLeviInvariant_fullΦ hϖ hψ a c s)
      (isLeviInvariant_shellΦ (D : ℤ) hW.2) (baseCoef (K := K) t D a s)) Y
  rw [liftFunction_sub_mul] at h
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
  simp only [fullΦ, shellΦ, baseCoef]
  rw [hmod, hd1, ite_eq_left rfl, sphericalWhittaker_rankOne hϖ hψ a hu₁, hlam, zpow_natCast]
  simp only [q]
  ring

theorem summable_baseIntegrand {d : ℤ}
    {Ψ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}
    (hΨ : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers t, Ψ (g * k) = Ψ g) :
    Summable fun y : Matrix (Fin (t + 1)) (Fin 1) K.Carrier ⧸ integralMatrices K (t + 1) 1 =>
      ‖baseIntegrand ψ hϖ d Ψ (Quotient.out y)‖ := by
  set S : Set (Matrix (Fin (t + 1)) (Fin 1) K.Carrier ⧸ integralMatrices K (t + 1) 1) :=
    {y | ∀ i j, ((ϖ ^ (d.toNat : ℤ) : K.Carrierˣ) : K.Carrier) * (Quotient.out y) i j ∈
      K.canonicalTopologicalData.Integers}
  have hS : S.Finite := (finite_and_ncard_le K hϖ (t + 1) 1 S fun y hy => hy).1
  refine summable_of_ne_finset_zero (s := hS.toFinset) fun y hy => ?_
  rw [Set.Finite.mem_toFinset] at hy
  rw [baseIntegrand_eq_zero_of_depth_ne hϖ hΨ, norm_zero]
  intro hd
  apply hy
  intro i j
  have h := uniformizer_pow_depth_mul_mem hϖ (Quotient.out y) i j
  have hd0 : (d.toNat : ℤ) = d := by
    have := openCellDepth_nonneg hϖ (Quotient.out y)
    omega
  rw [hd] at h
  rw [hd0]
  exact h

theorem shellCoefficient_rankOne (q : ℕ) (a : Fin (0 + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    (D : ℕ) :
    shellCoefficient (pairParameter q a c s) D =
      (-(a 0 : ℂ) * (q : ℂ) ^ (-(1 + s))) ^ D *
        ∑ S ∈ Finset.powersetCard D (Finset.univ : Finset (Fin (t + 1))), ∏ j ∈ S, ((c j : ℂ))⁻¹ := by
  set e : Fin (t + 1) ≃ Fin (0 + 1) × Fin (t + 1) :=
    { toFun := fun j => (0, j), invFun := fun x => x.2, left_inv := fun _ => rfl,
      right_inv := fun x => Prod.ext (zero_fin_one x.1).symm rfl }
  have huniv : (Finset.univ : Finset (Fin (0 + 1) × Fin (t + 1))) =
      (Finset.univ : Finset (Fin (t + 1))).map e.toEmbedding := (Finset.map_univ_equiv e).symm
  rw [shellCoefficient, huniv, Finset.powersetCard_map, Finset.sum_map, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mem_powersetCard] at hS
  change ∏ p ∈ S.map e.toEmbedding, _ = _
  rw [Finset.prod_map]
  have hx : ∀ j ∈ S, -pairParameter q a c s (e.toEmbedding j) =
      (-(a 0 : ℂ) * (q : ℂ) ^ (-(1 + s))) * ((c j : ℂ))⁻¹ := by
    intro j _
    simp only [pairParameter, Equiv.toEmbedding_apply]
    change -((a 0 : ℂ) * ((c j : ℂ))⁻¹ * (q : ℂ) ^ (-(1 + s))) = _
    ring
  rw [Finset.prod_congr rfl hx, Finset.prod_mul_distrib, Finset.prod_const, hS.2]

/-- **The constant times the base value is the shell coefficient.** For `D ≤ t + 1` by the Schur
evaluation `s_κ(c) = e_D(c⁻¹)` and `baseConstant_eq`; for `D > t + 1` both sides vanish. -/
theorem baseCoef_mul_baseValue (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (a : Fin (0 + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ) (D : ℕ) :
    baseCoef (K := K) t D a s * baseValue ϖ t (D : ℤ)
      (GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
        K.canonicalTopologicalData.residueCardinality c) =
      shellCoefficient (pairParameter K.canonicalTopologicalData.residueCardinality a c s) D := by
  rw [shellCoefficient_rankOne, baseValue]
  by_cases hD : D ≤ t + 1
  · rw [ite_eq_left ⟨by omega, by omega⟩, Int.toNat_natCast,
      GeneralLinear.Spherical.sphericalWhittaker_torus hϖ _ _
        (isIntegrallyTrivial_of_additiveConductor K hψ t), ite_eq_left (antitone_baseKappa t D),
      satakeSchur_baseKappa c hD]
    have hq : 0 < K.canonicalTopologicalData.residueCardinality := by
      have := K.canonicalTopologicalData.residueCardinality_gt_one
      omega
    have hc := baseConstant_eq K.canonicalTopologicalData.residueCardinality hq t D hD s
    simp only [baseCoef]
    have hpow : (-(a 0 : ℂ) * (K.canonicalTopologicalData.residueCardinality : ℂ) ^ (-(1 + s))) ^ D =
        (-1) ^ D * (a 0 : ℂ) ^ D *
          ((K.canonicalTopologicalData.residueCardinality : ℂ) ^ (-(1 + s))) ^ D := by ring
    rw [hpow, ← hc]
    ring
  · rw [ite_eq_right (by omega), mul_zero, Finset.powersetCard_eq_empty.2 (by simp; omega),
      Finset.sum_empty, mul_zero]

/-- **The shell identities for a first block of rank one**, for `ψ` of conductor `𝒪` and a
section with the target transformation law. -/
theorem shellIdentity_rankOne (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    {a : Fin (0 + 1) → ℂˣ} {c : Fin (t + 1) → ℂˣ} {s : ℂ}
    {f : Langlands.GeneralLinear ((0 + 1) + (t + 1)) K.Carrier → ℂ}
    (hf : IsOpenCellSection K ψ hϖ a c s f) : ShellIdentity K ψ hϖ a c s f := by
  intro D
  have hψI := RankinSelberg.HighlyRamified.hasIntegerConductor_of_additiveConductor_eq_zero K ψ hψ
  set W := GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
    (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
    K.canonicalTopologicalData.residueCardinality c with hWdef
  have hW := isWhittakerType_sphericalWhittaker hϖ hψ c
  set G : Matrix (Fin (t + 1)) (Fin 1) K.Carrier → ℂ := fun Y =>
    baseCoef (K := K) t D a s * baseIntegrand ψ hϖ (D : ℤ) W Y with hG
  have hper : IsLatticePeriodic K G := by
    intro Y Z hZ
    simp only [hG]
    rw [baseIntegrand_isLatticePeriodic hϖ hψI hW.2 Y Z hZ]
  have hsum : Summable fun y : Matrix (Fin (t + 1)) (Fin 1) K.Carrier ⧸
      integralMatrices K (t + 1) 1 => ‖G (Quotient.out y)‖ := by
    simp only [hG, norm_mul]
    exact (summable_baseIntegrand hϖ hW.2).mul_left _
  obtain ⟨-, hHas⟩ := integrable_and_hasSum_of_isLatticePeriodic K hper hsum
  have hint : ∫ Y, G Y ∂matrixHaar K (t + 1) 1 =
      shellCoefficient (pairParameter K.canonicalTopologicalData.residueCardinality a c s) D := by
    simp only [hG]
    rw [integral_const_mul, integral_baseIntegrand hϖ hψI t (D : ℤ) hW,
      baseCoef_mul_baseValue hϖ hψ a c s D]
  rw [hint] at hHas
  have hsupp : Function.support (fun y : Matrix (Fin (t + 1)) (Fin 1) K.Carrier ⧸
      integralMatrices K (t + 1) 1 => G (Quotient.out y)) ⊆ {y | classDepth K hϖ y = D} := by
    intro y hy
    simp only [Function.mem_support, Set.mem_ofPred_eq] at hy ⊢
    by_contra hne
    apply hy
    simp only [hG]
    rw [baseIntegrand_eq_zero_of_depth_ne hϖ hW.2, mul_zero]
    intro hd
    apply hne
    simp only [classDepth]
    rw [hd]
    rfl
  have h := (hasSum_subtype_iff_of_support_subset hsupp).2 hHas
  refine h.congr_fun fun y => ?_
  have hd : openCellDepth hϖ (Quotient.out y.1) = D := by
    have h1 := y.2
    simp only [Set.mem_ofPred_eq, classDepth] at h1
    have h2 := openCellDepth_nonneg hϖ (Quotient.out y.1)
    omega
  simp only [Function.comp, hG]
  rw [openCellSummand_eq_lower hϖ hψ hf, liftFunction_fullΦ_eq hϖ hψ a c s _ hd, baseIntegrand,
    mul_assoc]

end Shell

end Langlands.Shahidi.OpenCell.Base
