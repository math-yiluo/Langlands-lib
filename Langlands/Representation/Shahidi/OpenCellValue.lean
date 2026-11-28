import Langlands.Representation.Shahidi.OpenCellGeometry
import Langlands.LocalField.SmoothCharacterNormProof
import Langlands.LocalField.Normalization.Proof
import Langlands.Representation.Unramified.StandardHeckeSum
import Langlands.Representation.RankinSelberg.UnramifiedPairTorusCoefficient
import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialInput

/-! # The value of the spherical section on the open cell -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor Matrix

universe u

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local instance ocValueTopologicalSpace : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance ocValueValuativeRel : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
local instance ocValueIsNonarchimedeanLocalField : IsNonarchimedeanLocalField K.Carrier := K.canonicalTopologicalData.localField

/-- The transformation law of the target statement. -/
def IsOpenCellSection {r t : ℕ}
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
      K.canonicalTopologicalData.topology)
    {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
    (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    (f : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier → ℂ) : Prop :=
  ∀ (X : Matrix (Fin (r + 1)) (Fin (t + 1)) K.Carrier)
    (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier)
    (k : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier),
    k ∈ Langlands.Conductor.integralSubgroup K.canonicalTopologicalData.Integers
      (r + 1 + t) →
    f (upper (r + 1) (t + 1) K.Carrier X * GeneralLinear.blockSum (m₁, m₂) * k) =
      ((twoBlockModulus K m₁ m₂ : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + s / ((r + t + 2 : ℕ) : ℂ)) *
        GeneralLinear.Spherical.sphericalWhittaker (n := r) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
          K.canonicalTopologicalData.residueCardinality a m₁ *
        GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
          K.canonicalTopologicalData.residueCardinality c m₂

/-- The block Weyl element is integral. -/
theorem blockWeyl_mem_integralSubgroup (r t : ℕ) :
    blockWeyl (r + 1) (t + 1) K.Carrier ∈
      integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t) := by
  rw [mem_integralSubgroup]
  constructor
  · intro i j
    rw [blockWeyl_entry]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · intro i j
    rw [blockWeyl, permutation_inv, permutation_entry]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

/-- A uniformizing element has the normalized absolute value of the canonical uniformizer:
`|ϖ ^ k| = q ^ (-k)`. -/
theorem normalizedAbs_zpow_of_isUniformizingElement {ϖ : K.Carrierˣ}
    (hϖ : Iwasawa.IsUniformizingElement
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ) (k : ℤ) :
    K.canonicalTopologicalData.normalizedAbs ((ϖ ^ k : K.Carrierˣ) : K.Carrier) =
      (K.canonicalTopologicalData.residueCardinality : ℝ) ^ (-k) := by
  set T := K.canonicalTopologicalData
  set ϖ₀ := LocalFactor.PadicAbelian.uniformizerUnit T
  have h0 : Iwasawa.IsUniformizingElement (ValuativeRel.valuation K.Carrier) ϖ₀ :=
    Langlands.Unramified.uniformizerUnit_isUniformizingElement K
  have hv := RankinSelberg.UnramifiedPairTorus.valuation_eq_of_isUniformizingElement
    (ValuativeRel.valuation K.Carrier) h0 hϖ
  set x : K.Carrierˣ := ϖ / ϖ₀
  have hx : ValuativeRel.valuation K.Carrier (x : K.Carrier) = 1 := by
    rw [Units.val_div_eq_div_val, map_div₀, hv, div_self]
    exact (Valuation.ne_zero_iff _).2 ϖ₀.ne_zero
  have hx1 : T.normalizedAbs ((x ^ k : K.Carrierˣ) : K.Carrier) = 1 := by
    rw [T.normalizedAbs_eq_one_iff_valuation_eq_one, Units.val_zpow_eq_zpow_val, map_zpow₀]
    change ValuativeRel.valuation K.Carrier (x : K.Carrier) ^ k = 1
    rw [hx, one_zpow]
  have hsplit : ϖ ^ k = x ^ k * ϖ₀ ^ k := by
    rw [← mul_zpow, div_mul_cancel]
  rw [hsplit, Units.val_mul, T.normalizedAbs_mul, hx1, one_mul,
    LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs]

/-- `|det(u ϖ^λ)| = q ^ (-∑ λ)` for an upper unipotent `u`. -/
theorem determinantNorm_unipotent_mul_torus {n : ℕ} {ϖ : K.Carrierˣ}
    (hϖ : Iwasawa.IsUniformizingElement
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
    {u : Langlands.GeneralLinear n K.Carrier} (hu : u ∈ upperUnipotent n K.Carrier)
    (lam : Fin n → ℤ) :
    ((K.canonicalTopologicalData.determinantNorm n (u * Iwasawa.torus ϖ lam) : NNReal) : ℝ) =
      (K.canonicalTopologicalData.residueCardinality : ℝ) ^ (-∑ i, lam i) := by
  set T := K.canonicalTopologicalData
  have hq : (T.residueCardinality : ℝ) ≠ 0 := by
    have := T.residueCardinality_gt_one
    positivity
  rw [T.determinantNorm_coe]
  change T.normalizedAbs (u * Iwasawa.torus ϖ lam).val.det = _
  have hu1 : u.val.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hu.1]
    exact Finset.prod_eq_one fun i _ => hu.2 i
  rw [Units.val_mul, Matrix.det_mul, hu1, one_mul, Iwasawa.torus_val, Matrix.det_diagonal]
  change (T.normalizedAbsHom (∏ i, ((ϖ ^ lam i : K.Carrierˣ) : K.Carrier)) : ℝ) = _
  rw [map_prod, NNReal.coe_prod]
  simp only [T.normalizedAbsHom_coe]
  rw [Finset.prod_congr rfl fun i _ => normalizedAbs_zpow_of_isUniformizingElement K hϖ (lam i),
    RankinSelberg.UnramifiedPairTorus.prod_zpow_eq_zpow_sum _ _ hq, Finset.sum_neg_distrib]

/-- **The section on the open cell.** For `lower(Y) = u ϖ^ν k` (Iwasawa), the section `f`
takes at `lower(Y) k'` (`k'` integral) the value `q^(-(r+t+2) D (1/2 + s/(r+t+2)))`
times the two spherical Whittaker functions at the diagonal blocks `u₁ ϖ^λ`, `u₂ ϖ^μ` of
`u ϖ^ν`; here `λ`, `μ` are the two blocks of `ν` and `D = ∑ λ`. -/
theorem exists_openCellSection_value {r t : ℕ}
    {ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
      K.canonicalTopologicalData.topology}
    {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
    {a : Fin (r + 1) → ℂˣ} {c : Fin (t + 1) → ℂˣ} {s : ℂ}
    {f : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier → ℂ}
    (hf : IsOpenCellSection K ψ hϖ a c s f)
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) :
    ∃ u₁ ∈ upperUnipotent (r + 1) K.Carrier, ∃ u₂ ∈ upperUnipotent (t + 1) K.Carrier,
      ∀ k' ∈ integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t),
      f (lower (r + 1) (t + 1) K.Carrier Y * k') =
        (((K.canonicalTopologicalData.residueCardinality : ℝ) ^
            (-(((r + t + 2 : ℕ) : ℤ) * openCellDepth hϖ Y)) : ℝ) : ℂ) ^
            ((1 : ℂ) / 2 + s / ((r + t + 2 : ℕ) : ℂ)) *
          GeneralLinear.Spherical.sphericalWhittaker (n := r) hϖ
            (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
            K.canonicalTopologicalData.residueCardinality a
            (u₁ * Iwasawa.torus ϖ fun i => openCellExponent hϖ Y (i.castAdd (t + 1))) *
          GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
            (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
            K.canonicalTopologicalData.residueCardinality c
            (u₂ * Iwasawa.torus ϖ fun j => openCellExponent hϖ Y (j.natAdd (r + 1))) := by
  obtain ⟨u, hu, k, hk, h⟩ := exists_eq_openCellExponent hϖ Y
  have hb := isUpperTriangular_mul_torus hu ϖ (openCellExponent hϖ Y)
  have hb' := eq_upper_mul_blockSum (u * Iwasawa.torus ϖ (openCellExponent hϖ Y)) hb
  rw [topLeft_mul_torus hu, botRight_mul_torus hu] at hb'
  refine ⟨topLeft u hu.1, topLeft_mem_upperUnipotent hu, botRight u hu.1,
    botRight_mem_upperUnipotent hu, fun k' hk' => ?_⟩
  have hdec : lower (r + 1) (t + 1) K.Carrier Y * k' =
      upper (r + 1) (t + 1) K.Carrier (radicalCoordinate _ hb) *
        GeneralLinear.blockSum
          (topLeft u hu.1 * Iwasawa.torus ϖ fun i => openCellExponent hϖ Y (i.castAdd (t + 1)),
            botRight u hu.1 * Iwasawa.torus ϖ fun j => openCellExponent hϖ Y (j.natAdd (r + 1))) *
        (k * k') := by
    rw [h, ← hb', mul_assoc]
  rw [hdec, hf _ _ _ _ (mul_mem hk hk')]
  congr 4
  set q := (K.canonicalTopologicalData.residueCardinality : ℝ)
  have hq : q ≠ 0 := by
    have := K.canonicalTopologicalData.residueCardinality_gt_one
    positivity
  rw [twoBlockModulus, determinantNorm_unipotent_mul_torus K hϖ (topLeft_mem_upperUnipotent hu),
    determinantNorm_unipotent_mul_torus K hϖ (botRight_mem_upperUnipotent hu),
    sum_openCellExponent_natAdd, ← openCellDepth, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
    ← zpow_mul, ← zpow_sub₀ hq]
  congr 1
  push_cast
  ring

end Langlands.Shahidi.OpenCell
