import Langlands.Representation.RankinSelberg.HighlyRamified.ZeroCellDualIntegral
import Langlands.Representation.RankinSelberg.HighlyRamified.UnitarySpherical
import Langlands.Representation.RankinSelberg.HighlyRamified.ForwardConstant
import Langlands.Representation.RankinSelberg.HighlyRamified.DualShellIntegral
import Langlands.Representation.RankinSelberg.HighlyRamified.KirillovShell

/-!
# The forward integral of a dual-translated zero-cell vector

Let `π` be a representation of `GL_(n+3)(F)` with nonzero Whittaker functional `ℓ`, and let
`v'` be a vector whose Whittaker function for the inverse-transpose pullback agrees with
the zero-cell function on the mirabolic subgroup. Put `d = diag(ϖ^m I_(n+2), 1)` and let
`Y` be the Whittaker function of `π(ᵗd⁻¹) v'`; its first dual function is the right
translate of the zero-cell lift by `d`. Assume that for a norm-one tuple `z` the gamma
factor of `(π, I(z))` is `c^(n+2) (∏ z_i)^m X^((n+2) m)`.

The dual corank-one integral of `Y` against the spherical function of `I(z)` is computed
explicitly by the zero-cell formula: it is `(∏ z_i)^m q^((n+2) m (s - 1/2))`. The
functional equation then makes the corank-one integral of `Y` against Jacquet's spherical
function `W(·; z; ψ̄)` equal on a right half-plane to the constant
`q^(-(n+2) m / 2) q^((n+2) m) / c^(n+2)`, which does not depend on `z`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

/-- `(q^N)^(s - 1/2) = q^(-N/2) (q^(-s))^(-N)` for a positive integer `q`. -/
theorem ofReal_zpow_cpow_eq {q : ℕ} (hq : 0 < q) (N : ℤ) (s : ℂ) :
    ((((q : ℝ) ^ N : ℝ)) : ℂ) ^ (s - 1 / 2) =
      (q : ℂ) ^ (-(N : ℂ) / 2) * (spectralPoint q s) ^ (-N) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqN : (((q : ℝ) ^ N : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (zpow_pos hqR N).ne'
  have hlog : Complex.log (q : ℂ) = (Real.log q : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hqR.le]
  have hlogN : Complex.log (((q : ℝ) ^ N : ℝ) : ℂ) = (N : ℂ) * (Real.log q : ℂ) := by
    rw [← Complex.ofReal_log (zpow_pos hqR N).le, Real.log_zpow]
    push_cast
    ring
  rw [Complex.cpow_def_of_ne_zero hqN, hlogN, spectralPoint, Complex.cpow_def_of_ne_zero hq0,
    Complex.cpow_def_of_ne_zero hq0, hlog, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance essentialDualFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance essentialDualValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance essentialDualLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance essentialDualFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance essentialDualFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance essentialDualGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance essentialDualGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance essentialDualUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance essentialDualUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance essentialDualQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance essentialDualQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "ϖF" => F.canonicalTopologicalData.uniformizerUnit

/-- The inverse transpose preserves `GL_(r+1)(O)`. -/
theorem inverseTranspose_mem_integralSubgroup {r : ℕ} {k : GeneralLinear (r + 1) F.Carrier}
    (hk : k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r) :
    inverseTranspose (r + 1) F.Carrier k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r := by
  rw [← isIntegralMatrix_iff_mem_integralSubgroup] at hk ⊢
  exact isIntegralMatrix_inverseTranspose F hk

/-- The long Weyl element lies in `GL_(r+1)(O)`. -/
theorem weylLong_mem_integralSubgroup {r : ℕ} :
    weylLong (r + 1) F.Carrier ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r := by
  rw [← isIntegralMatrix_iff_mem_integralSubgroup]
  exact isIntegralMatrix_weylLong F

/-- The element `-1` lies in `GL_(r+1)(O)`. -/
theorem neg_one_mem_integralSubgroup {r : ℕ} :
    (-1 : GeneralLinear (r + 1) F.Carrier) ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r := by
  have h : ∀ i j, (-1 : GeneralLinear (r + 1) F.Carrier) i j ∈ (ValuativeRel.valuation F.Carrier).integer := by
    intro i j
    rw [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply]
    split_ifs
    · exact Subring.neg_mem _ (Subring.one_mem _)
    · rw [neg_zero]
      exact Subring.zero_mem _
  rw [Conductor.mem_integralSubgroup]
  exact ⟨h, by rw [inv_neg_one]; exact h⟩

/-- The absolute determinant of `diag(ϖ^m, ..., ϖ^m)⁻¹` on `GL_(n+2)` is `q^((n+2) m)`. -/
theorem abv_det_scalar_inv (n m : ℕ) :
    abv (Matrix.det ((scalar (n := n + 2) (ϖF ^ (m : ℤ)))⁻¹ :
        GeneralLinear (n + 2) F.Carrier).val) =
      (qF : ℝ) ^ (((n + 2 : ℕ) : ℤ) * (m : ℤ)) := by
  have hu : determinant ((scalar (n := n + 2) (ϖF ^ (m : ℤ)))⁻¹ :
      GeneralLinear (n + 2) F.Carrier) = ϖF ^ (-(((n + 2 : ℕ) : ℤ) * (m : ℤ))) := by
    rw [map_inv]
    change (determinant (Matrix.GeneralLinearGroup.scalar (Fin (n + 1 + 1))
      (ϖF ^ (m : ℤ))))⁻¹ = _
    rw [determinant_scalar, ← zpow_natCast, ← zpow_mul, ← zpow_neg]
    congr 1
    push_cast
    ring
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  change abv ((determinant ((scalar (n := n + 2) (ϖF ^ (m : ℤ)))⁻¹ :
      GeneralLinear (n + 2) F.Carrier) : F.Carrierˣ) : F.Carrier) = _
  rw [hu, normalizedAbsoluteValue_apply, LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs,
    neg_neg]

set_option maxHeartbeats 1000000 in
/-- The forward corank-one integral of the dual translate of a zero-cell lift. Let `v'` have
Whittaker function, for the inverse-transpose pullback and its first dual functional, equal
to the zero-cell function on the mirabolic subgroup, and let `Y` be the Whittaker function
of `π(ᵗd⁻¹) v'` with `d = diag(ϖ^m I_(n+2), 1)`. If, for a norm-one tuple `z`, the gamma
factor of `(π, I(z))` is `c^(n+2) (∏ z_i)^m X^((n+2) m)`, then the corank-one integral of
`Y` against `W(·; z; ψ̄)` equals `q^(-N/2) q^N / c^(n+2)`, `N = (n+2) m`, on a right
half-plane, and converges there. -/
theorem forward_corankOne_dualTranslate_eq
    (ψ : UnitaryAdditiveCharacter F.Carrier) (hψ : Conductor.HasIntegerConductor ψ)
    (ν : AdditiveHaarMeasure F.Carrier) {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 2 + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ (n + 2) π) (hℓ : ℓ.val ≠ 0) (c : ℂˣ) (m : ℕ) (v' : V)
    (hv' : ∀ g : Langlands.GeneralLinear (n + 2 + 1) F.Carrier,
      (∀ j, g.val (Fin.last (n + 2)) j = if j = Fin.last (n + 2) then 1 else 0) →
      (coefficientMap (inverseTransposePullback π) (firstDualFunctional ψ π ℓ) v').val g =
        (zeroCellWhittaker (Unramified.uniformizerUnit_isUniformizingElement F)
          (Conductor.hasIntegerConductor_scale_neg_one hψ).1 (n + 2)).val g)
    (z : Fin (n + 1 + 1) → ℂˣ) (hz : ∀ i, ‖(z i : ℂ)‖ = 1)
    (hG : IsPadicSymmetricGammaFactor F ψ ν π (Unramified.principalSeriesOfTuple F z)
      (rationalEpsilonMonomial (c ^ (n + 2) * (∏ i, z i) ^ (m : ℤ))
        (((n + 2 : ℕ) : ℤ) * (m : ℤ)))) :
    ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      CorankOneConverges ψ abv (unipotentQuotientHaar F.Carrier (n + 1))
          (coefficientMap π ℓ (inverseTransposePullback π
            (rankInclusion 1 (scalar (n := n + 2) (ϖF ^ (m : ℤ)))) v'))
          (Conductor.inverseSphericalWhittaker hψ.1
            (Unramified.uniformizerUnit_isUniformizingElement F) qF z) s ∧
        corankOneIntegral ψ abv (unipotentQuotientHaar F.Carrier (n + 1))
          (coefficientMap π ℓ (inverseTransposePullback π
            (rankInclusion 1 (scalar (n := n + 2) (ϖF ^ (m : ℤ)))) v'))
          (Conductor.inverseSphericalWhittaker hψ.1
            (Unramified.uniformizerUnit_isUniformizingElement F) qF z) s =
          (qF : ℂ) ^ (-((((n + 2 : ℕ) : ℤ) * (m : ℤ) : ℤ) : ℂ) / 2) *
            (qF : ℂ) ^ (((n + 2 : ℕ) : ℤ) * (m : ℤ)) / (c : ℂ) ^ (n + 2) := by
  let T := F.canonicalTopologicalData
  have hϖ := Unramified.uniformizerUnit_isUniformizingElement F
  have hq : 1 < qF := PadicField.TopologicalData.residueCardinality_gt_one _
  have hq0 : 0 < qF := by omega
  have hnr : n + 1 < n + 1 + 1 := Nat.lt_succ_self _
  set σ := Unramified.principalSeriesOfTuple F z with hσ
  set μ := unipotentQuotientHaar F.Carrier (n + 1) with hμdef
  have hμ := unipotentQuotientHaar_isCompatible F.Carrier (n + 1)
  set N : ℤ := ((n + 2 : ℕ) : ℤ) * (m : ℤ) with hN
  set K : ℂˣ := (∏ i, z i) ^ (m : ℤ) with hK
  set C : ℂˣ := c ^ (n + 2) * K with hC
  set u : F.Carrierˣ := ϖF ^ (m : ℤ) with hu
  set a : GeneralLinear (n + 2) F.Carrier := scalar (n := n + 2) u with ha
  set d : GeneralLinear (n + 2 + 1) F.Carrier := rankInclusion 1 a with hd
  set π'' := inverseTransposePullback π with hπ''
  set ℓ'' := firstDualFunctional ψ π ℓ with hℓ''
  set y : V := π'' d v' with hy
  -- The pair gamma relation and a nonzero functional of `I(z)`.
  have hG' : IsPadicPairGammaFactor F ψ ν π σ (rationalEpsilonMonomial C N) :=
    (isPadicSymmetricGammaFactor_of_le (by omega)).mp hG
  have e : IsPairGammaFactor qF ψ abv ν π σ (rationalEpsilonMonomial C N) := hG'
  rw [isPairGammaFactor_of_lt hnr] at e
  obtain ⟨-, -, ⟨ℓσ, hℓσ⟩, -⟩ := e
  obtain ⟨wσ⟩ := principalSeriesOfTuple_nonempty_sphericalTest F ψ hψ z hz ℓσ hℓσ
  set f' : (coefficientModel σ ℓσ).toSubmodule := wσ.val.val with hf'
  have hf'fun : f'.val = Conductor.inverseSphericalWhittaker hψ.1 hϖ qF z :=
    Subtype.ext (principalSeriesOfTuple_sphericalTest_eq F ψ hψ z hz ℓσ hℓσ wσ)
  -- The test function is right `GL(O)`-invariant with value `1` at the identity.
  have hinv : ∀ (g k : GeneralLinear (n + 1 + 1) F.Carrier),
      k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer (n + 1) → f'.val.val (g * k) = f'.val.val g :=
    fun g k hk => Conductor.sphericalTestFunction_right_invariant σ ℓσ wσ ⟨k, hk⟩ g
  have hone : f'.val.val 1 = 1 := Conductor.sphericalTestFunction_one σ ℓσ wσ
  -- The central character of `I(z)` on `ϖ^m` is `(∏ z_i)^m`.
  have hωu : ((((∏ i, (Unramified.characterTuple F z i).toMonoidHom) u : ℂˣ)) : ℂ) =
      (K : ℂ) := by
    have h1 := prod_characterTuple_uniformizer F z
    rw [Unramified.characterValues_characterTuple] at h1
    rw [hu, map_zpow, hK, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, h1,
      Units.coe_prod]
  have hcent : ∀ h : GeneralLinear (n + 1 + 1) F.Carrier,
      f'.val.val (h * scalar (n := n + 1 + 1) u) = (K : ℂ) * f'.val.val h := by
    intro h
    rw [← hωu]
    exact model_mul_scalar (Unramified.principalSeriesOfTuple F z) _
      (principalSeriesOfTuple_hasGLCentralCharacter F z) ℓσ f' u h
  -- The second dual of the spherical test.
  set X := secondDualFunction ψ (n + 1) f'.val with hX
  have hXint : ∀ g k, k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer (n + 1) → X.val (g * k) = X.val g := by
    intro g k hk
    change f'.val.val (weylLong _ _ * inverseTranspose _ _ (g * k)) =
      f'.val.val (weylLong _ _ * inverseTranspose _ _ g)
    rw [map_mul, ← mul_assoc]
    exact hinv _ _ (inverseTranspose_mem_integralSubgroup F hk)
  have hX1 : X.val 1 = 1 := by
    change f'.val.val (weylLong _ _ * inverseTranspose _ _ 1) = 1
    rw [map_one, mul_one]
    have h := hinv 1 _ (weylLong_mem_integralSubgroup F (r := n + 1))
    rw [one_mul] at h
    rw [h, hone]
  have hXa : ∀ g, X.val (g * a⁻¹) = (K : ℂ) * X.val g := by
    intro g
    change f'.val.val (weylLong _ _ * inverseTranspose _ _ (g * a⁻¹)) =
      (K : ℂ) * f'.val.val (weylLong _ _ * inverseTranspose _ _ g)
    have hia : inverseTranspose (n + 1 + 1) F.Carrier a⁻¹ = scalar (n := n + 1 + 1) u := by
      rw [map_inv, ha]
      change (inverseTranspose (n + 1 + 1) F.Carrier
        (Matrix.GeneralLinearGroup.scalar (Fin (n + 1 + 1)) u))⁻¹ = _
      rw [inverseTranspose_scalar, map_inv, inv_inv]
    rw [map_mul, hia, ← mul_assoc, hcent]
  -- The first dual of `Y` is the translate of the zero-cell lift by `d`.
  set Y : (coefficientModel π ℓ).toSubmodule := ⟨coefficientMap π ℓ y, y, rfl⟩ with hY
  have hcd : firstDualFunction ψ (n + 2) Y.val =
      translateWhittaker (ψ.scale (-1)) (n + 2) (coefficientMap π'' ℓ'' v') d := by
    change firstDualFunction ψ (n + 2) (coefficientMap π ℓ y) = _
    rw [firstDualFunction_coefficient]
    apply Subtype.ext
    funext g
    change ℓ''.val (π'' g y) = ℓ''.val (π'' (g * d) v')
    rw [map_mul, Module.End.mul_apply]
  -- The dual integral is explicit.
  have hJ : ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      corankOneIntegral (ψ.scale (-1)) abv μ (firstDualFunction ψ (n + 1 + 1) Y.val)
          (secondDualFunction ψ (n + 1) f'.val) s =
        ((K : ℂ) * (qF : ℂ) ^ (-(N : ℂ) / 2)) * (spectralPoint qF s) ^ (-N) := by
    refine ⟨0, fun s _ => ?_⟩
    have h4 := (zeroCell_translate_corankOne F (n + 1) μ hμ hϖ
      (Conductor.hasIntegerConductor_scale_neg_one hψ).1 (coefficientMap π'' ℓ'' v') hv' X
      hXint hX1 a (K : ℂ) hXa s).2
    change corankOneIntegral (ψ.scale (-1)) abv μ (firstDualFunction ψ (n + 2) Y.val) X s = _
    rw [hcd]
    change corankOneIntegral (ψ.scale (-1)) abv μ
      (translateWhittaker (ψ.scale (-1)) (n + 1 + 1) (coefficientMap π'' ℓ'' v')
        (rankInclusion 1 a)) X s = _
    rw [h4, determinantWeight, abv_det_scalar_inv F n m, ofReal_zpow_cpow_eq hq0]
    ring
  obtain ⟨ζ, hζ, b, hb⟩ := corankOne_eq_const_of_gamma_monomial F ψ ν hG' ℓ hℓ ℓσ hℓσ Y f'
    C N rfl _ hJ
  -- The minus-one scalar of the model of `I(z)` is `1`.
  have hζ1 : (ζ : ℂ) = 1 := by
    have h1 := hζ f' 1
    have hm : f'.val.val ((-1) * 1) = 1 := by
      rw [mul_one]
      have h := hinv 1 _ (neg_one_mem_integralSubgroup F (r := n + 1))
      rw [one_mul] at h
      rw [h, hone]
    rw [hm, hone, mul_one] at h1
    exact h1.symm
  refine ⟨b, fun s hs => ?_⟩
  have hval := hb s hs
  rw [hζ1, one_pow, inv_one, one_mul] at hval
  have hC0 : (C : ℂ) = (c : ℂ) ^ (n + 2) * (K : ℂ) := by
    rw [hC, Units.val_mul, Units.val_pow_eq_pow_val]
  have hK0 : (K : ℂ) ≠ 0 := K.ne_zero
  have hc0 : (c : ℂ) ^ (n + 2) ≠ 0 := pow_ne_zero _ c.ne_zero
  have hconst : (C : ℂ)⁻¹ * ((K : ℂ) * (qF : ℂ) ^ (-(N : ℂ) / 2)) * (qF : ℂ) ^ N =
      (qF : ℂ) ^ (-(N : ℂ) / 2) * (qF : ℂ) ^ N / (c : ℂ) ^ (n + 2) := by
    rw [hC0]
    field_simp
  rw [hconst, hf'fun] at hval
  have hne : (qF : ℂ) ^ (-(N : ℂ) / 2) * (qF : ℂ) ^ N / (c : ℂ) ^ (n + 2) ≠ 0 := by
    have hq0' : (qF : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
    refine div_ne_zero (mul_ne_zero ?_ (zpow_ne_zero _ hq0')) hc0
    exact fun h => hq0' ((Complex.cpow_eq_zero_iff _ _).mp h).1
  refine ⟨?_, hval⟩
  · by_contra hni
    apply hne
    rw [← hval]
    exact integral_undef hni

end Padic

end Langlands.RankinSelberg.HighlyRamified
