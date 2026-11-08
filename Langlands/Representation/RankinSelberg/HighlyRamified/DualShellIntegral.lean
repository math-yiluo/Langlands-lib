import Langlands.Representation.RankinSelberg.HighlyRamified.DualShell
import Langlands.Representation.RankinSelberg.HighlyRamified.DualJValue
import Langlands.Representation.GodementJacquet.InverseTransposeMatrixIntegral
import Langlands.Representation.Conductor.SphericalIntegrals
import Langlands.Group.GL.IntegralSubgroup

/-!
# The dual integral of the Kirillov test vector

Let `f'` be an inverse Whittaker function on `GL_(m+2)` whose restriction to `diag(B,1)` is
supported on `N ϖ^(-c) GL_(m+1)(O)`, with value `κ₁ χ(det k)⁻¹` at `diag(k ϖ^(-c), 1)` for
`k ∈ GL_(m+1)(O)`. Then the dual corank-one integral of the twisted smeared function `F`
(`twistedSmear`) against the second dual of `W''` is a constant times
`∫_(K⁰(f)) ω(k₀₀) W''(k) dk`.

The proof translates by the central element `ϖ^(-c)`, restricts to `GL_(m+1)(O)`
(`integral_out_of_support`), substitutes `k ↦ w ᵗk⁻¹`, and evaluates the weight `Φ₂` with
`unitLastWeight_firstColumn`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis QuotientIntegration GeneralLinear

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance dualShellIntFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance dualShellIntValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance dualShellIntLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance dualShellIntFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance dualShellIntFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance dualShellIntGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance dualShellIntGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance dualShellIntUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance dualShellIntUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance dualShellIntQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := borel _
local instance dualShellIntQuotientBorel (r : ℕ) : BorelSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable {m : ℕ}

section Matrices

variable {K : Type*} [Field K]

theorem scalar_commute (u : Kˣ) (g : Matrix.GeneralLinearGroup (Fin (m + 1)) K) :
    Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u * g =
      g * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u := by
  apply Units.ext
  change Matrix.scalar (Fin (m + 1)) (u : K) * (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) * Matrix.scalar (Fin (m + 1)) (u : K)
  exact (Matrix.scalar_commute (u : K) (fun _ => mul_comm _ _) _)

theorem inverseTranspose_scalar (u : Kˣ) :
    inverseTranspose (m + 1) K (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u) =
      Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u⁻¹ := by
  apply Units.ext
  rw [inverseTranspose_coe, ← map_inv]
  ext i j
  simp only [Matrix.GeneralLinearGroup.scalar, Matrix.transpose_apply]
  change (Matrix.scalar (Fin (m + 1)) ((u⁻¹ : Kˣ) : K)) j i =
    (Matrix.scalar (Fin (m + 1)) ((u⁻¹ : Kˣ) : K)) i j
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply, eq_comm]

theorem determinant_scalar (u : Kˣ) :
    determinant (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u) = u ^ (m + 1) := by
  apply Units.ext
  simp [determinant, Matrix.GeneralLinearGroup.scalar]

theorem weylLong_inverseTranspose_last (k : GeneralLinear (m + 1) K) (j : Fin (m + 1)) :
    (weylLong (m + 1) K * inverseTranspose (m + 1) K k) (Fin.last m) j =
      (k⁻¹ : GeneralLinear (m + 1) K) j 0 := by
  rw [weylLong_mul_entry, inverseTranspose_entry, Fin.rev_last]

theorem weylLong_inverseTranspose_involutive (k : GeneralLinear (m + 1) K) :
    weylLong (m + 1) K * inverseTranspose (m + 1) K
      (weylLong (m + 1) K * inverseTranspose (m + 1) K k) = k := by
  rw [map_mul, inverseTranspose_weylLong, inverseTranspose_involutive, ← mul_assoc,
    weylLong_mul_self, one_mul]

end Matrices

theorem isIntegralMatrix_iff_mem_level (k : GeneralLinear (m + 1) F.Carrier) :
    IsIntegralMatrix k ↔ k ∈ Conductor.levelOpenSubgroup F.Carrier m 0 := by
  change _ ↔ k ∈ Conductor.levelSubgroup F.Carrier m 0
  rw [Conductor.levelSubgroup_zero, Conductor.mem_integralSubgroup]

theorem isIntegralMatrix_weylLong :
    IsIntegralMatrix (weylLong (m + 1) F.Carrier) := by
  have hw : ∀ i j, weylLong (m + 1) F.Carrier i j ∈ (ValuativeRel.valuation F.Carrier).integer := by
    intro i j
    rw [weylLong_entry]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  refine ⟨hw, ?_⟩
  rw [weylLong_inv]
  exact hw

theorem isIntegralMatrix_inverseTranspose {k : GeneralLinear (m + 1) F.Carrier}
    (hk : IsIntegralMatrix k) : IsIntegralMatrix (inverseTranspose (m + 1) F.Carrier k) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [inverseTranspose_entry]
    exact hk.2 j i
  · rw [← map_inv, inverseTranspose_entry, inv_inv]
    exact hk.1 j i

theorem isIntegralMatrix_weylLong_inverseTranspose_iff (k : GeneralLinear (m + 1) F.Carrier) :
    IsIntegralMatrix (weylLong (m + 1) F.Carrier * inverseTranspose (m + 1) F.Carrier k) ↔
      IsIntegralMatrix k := by
  have hw := (isIntegralMatrix_iff_mem_level F _).1 (isIntegralMatrix_weylLong F (m := m))
  constructor
  · intro h
    have h1 := (isIntegralMatrix_iff_mem_level F _).1 h
    have h2 : inverseTranspose (m + 1) F.Carrier k ∈ Conductor.levelOpenSubgroup F.Carrier m 0 := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hw) h1
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    have h3 := isIntegralMatrix_inverseTranspose F ((isIntegralMatrix_iff_mem_level F _).2 h2)
    rwa [inverseTranspose_involutive] at h3
  · intro h
    exact (isIntegralMatrix_iff_mem_level F _).2 (Subgroup.mul_mem _ hw
      ((isIntegralMatrix_iff_mem_level F _).1 (isIntegralMatrix_inverseTranspose F h)))

theorem abv_eq_one_of_valuation (x : F.Carrier) (hx : ValuativeRel.valuation F.Carrier x = 1) :
    abv x = 1 := by
  have hne : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hx
    exact zero_ne_one hx
  have h1 : abv x ≤ 1 :=
    (F.canonicalTopologicalData.normalizedAbs_le_one_iff_mem_integers x).mpr (le_of_eq hx)
  have h2 : abv x⁻¹ ≤ 1 :=
    (F.canonicalTopologicalData.normalizedAbs_le_one_iff_mem_integers x⁻¹).mpr
      (show ValuativeRel.valuation F.Carrier x⁻¹ ≤ 1 from le_of_eq (by rw [map_inv₀, hx, inv_one]))
  have hprod : abv x * abv x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hne, map_one]
  nlinarith [AbsoluteValue.nonneg (normalizedAbsoluteValue F.canonicalTopologicalData) x,
    AbsoluteValue.nonneg (normalizedAbsoluteValue F.canonicalTopologicalData) x⁻¹]

section Shell

variable (ψ : UnitaryAdditiveCharacter F.Carrier) (η : AdditiveHaarMeasure F.Carrier)
  (χ : F.Carrierˣ →* ℂˣ) (ω : F.Carrierˣ →* ℂˣ) (ϖ : F.Carrierˣ) (c f : ℕ)

/-- The constant of the dual integral on the shell `ϖ^(-c) GL_(m+1)(O)`. -/
def dualShellConstant (m : ℕ) (κ₁ ωτ : ℂ) (s : ℂ) : ℂ :=
  ((χ (determinant (weylLong (m + 1 + 1) F.Carrier)) : ℂ))⁻¹ * ((χ ((ϖ ^ c)⁻¹) : ℂ)) ^ (m + 1) *
    ((η.measure ((integerAddSubgroup F : AddSubgroup F.Carrier) :
      Set F.Carrier)).toReal : ℂ) ^ (m + 1) * κ₁ * ωτ *
    RankinSelberg.determinantWeight abv
      (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹) (s - 1 / 2)

variable {ψ η χ ω ϖ c f}

/-- The dual corank-one function at `k ϖ^(-c)`, `k ∈ GL_(m+1)(O)`. -/
theorem corankOneFunction_dualShell (hψ : HasIntegerConductorAt F ψ)
    (hf : 0 < f) (hω : TrivialOnPrincipalUnits ω f)
    (hscale : ∀ o ∈ (ValuativeRel.valuation F.Carrier).integer,
      InPow f ((ϖ : F.Carrier) ^ c * o))
    (T : Finset (Fin (m + 1) → F.Carrier))
    (hT : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ integerLattice F m → t = t')
    (hcov : ∀ y, dualWeight ω (ϖ : F.Carrier) c f y ≠ 0 → ∃ t ∈ T, y - t ∈ integerLattice F m)
    (f' : RankinSelberg.InverseWhittakerFunctions ψ (m + 1)) (κ₁ : ℂ)
    (hval : ∀ k : GeneralLinear (m + 1) F.Carrier, IsIntegralMatrix k →
      f'.val (rankInclusion 1 (k * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹)) =
        κ₁ * ((χ (determinant k) : ℂ))⁻¹)
    (Fbig : RankinSelberg.WhittakerFunctions ψ (m + 1))
    (hFbig : ∀ g, Fbig.val g = twistedSmear F ψ η χ ω (ϖ : F.Carrier) c f T f' g)
    (W'' : RankinSelberg.InverseWhittakerFunctions ψ m) (ωτ : ℂ)
    (hWc : ∀ g, W''.val (g * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)) =
      ωτ * W''.val g)
    (s : ℂ) (k : GeneralLinear (m + 1) F.Carrier) (hk : IsIntegralMatrix k) :
    RankinSelberg.corankOneFunction (ψ.scale (-1)) abv
        (RankinSelberg.firstDualFunction ψ (m + 1) Fbig)
        (RankinSelberg.secondDualFunction ψ m W'') s
        (k * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹) =
      dualShellConstant F η χ ϖ c m κ₁ ωτ s *
        unitLastWeight ω f (fun i => -k (Fin.last m) i.rev) *
        W''.val (weylLong (m + 1) F.Carrier * inverseTranspose (m + 1) F.Carrier k) := by
  set z := Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹ with hz
  unfold RankinSelberg.corankOneFunction
  rw [RankinSelberg.firstDualFunction_apply, RankinSelberg.secondDualFunction_apply, hFbig,
    twistedSmear_at_dual F ψ η hψ χ hf hω hscale T hT hcov f', hval k hk]
  -- the second dual factor
  have hW : W''.val (weylLong (m + 1) F.Carrier * inverseTranspose (m + 1) F.Carrier (k * z)) =
      ωτ * W''.val (weylLong (m + 1) F.Carrier * inverseTranspose (m + 1) F.Carrier k) := by
    rw [map_mul, hz, inverseTranspose_scalar, inv_inv, ← mul_assoc, hWc]
  -- the determinant weight
  have hdW : RankinSelberg.determinantWeight abv (k * z) (s - 1 / 2) =
      RankinSelberg.determinantWeight abv z (s - 1 / 2) := by
    rw [← scalar_commute]
    exact Conductor.determinantWeight_mul_integral
      (abv_eq_one_of_valuation F) z k
      (by rw [← Conductor.levelSubgroup_zero]; exact (isIntegralMatrix_iff_mem_level F k).1 hk) _
  -- the character factor
  have hχ : (χ (determinant (k * z)) : ℂ) =
      (χ (determinant k) : ℂ) * ((χ ((ϖ ^ c)⁻¹) : ℂ)) ^ (m + 1) := by
    rw [map_mul, hz, determinant_scalar, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]
  -- the weight
  have hwt : dualWeight ω (ϖ : F.Carrier) c f (fun j => -(k * z) (Fin.last m) j.rev) =
      unitLastWeight ω f (fun i => -k (Fin.last m) i.rev) := by
    unfold dualWeight
    congr 1
    funext i
    show (ϖ : F.Carrier) ^ c * -((k * z : GeneralLinear (m + 1) F.Carrier) (Fin.last m) i.rev) = _
    rw [hz, mul_scalar_apply]
    have hϖ : ((ϖ : F.Carrier) ^ c) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
    simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    field_simp
  rw [hW, hdW, hχ, hwt, hz]
  unfold dualShellConstant
  have hχk : (χ (determinant k) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

/-- The substitution `k ↦ w ᵗk⁻¹` preserves the Haar integral. -/
theorem integral_weylLong_inverseTranspose (φ : GeneralLinear (m + 1) F.Carrier → ℂ) :
    ∫ g, φ (weylLong (m + 1) F.Carrier * inverseTranspose (m + 1) F.Carrier g)
        ∂generalLinearHaar F.Carrier m =
      ∫ g, φ g ∂generalLinearHaar F.Carrier m := by
  have hIT := GodementJacquet.Padic.generalLinearHaar_measurePreserving_inverseTranspose F m
  have he := (GodementJacquet.inverseTransposeMeasurableEquiv hIT.measurable).measurableEmbedding
  rw [hIT.integral_comp he (fun h => φ (weylLong (m + 1) F.Carrier * h))]
  exact integral_mul_left_eq_self φ _

theorem inFirstColumn_isIntegralMatrix {k : GeneralLinear (m + 1) F.Carrier}
    (hk : InFirstColumn f k) : IsIntegralMatrix k :=
  ((inFirstColumn_iff k).1 hk).1

/-- The dual integral of the twisted smeared Kirillov test vector. -/
theorem dual_shell_integral (hψ : HasIntegerConductorAt F ψ)
    (hf : 0 < f) (hω : TrivialOnPrincipalUnits ω f)
    (hscale : ∀ o ∈ (ValuativeRel.valuation F.Carrier).integer,
      InPow f ((ϖ : F.Carrier) ^ c * o))
    (T : Finset (Fin (m + 1) → F.Carrier))
    (hT : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ integerLattice F m → t = t')
    (hcov : ∀ y, dualWeight ω (ϖ : F.Carrier) c f y ≠ 0 → ∃ t ∈ T, y - t ∈ integerLattice F m)
    (f' : RankinSelberg.InverseWhittakerFunctions ψ (m + 1)) (κ₁ : ℂ)
    (hsupp : ∀ B : GeneralLinear (m + 1) F.Carrier, f'.val (rankInclusion 1 B) ≠ 0 →
      ∃ u : upperUnipotent (m + 1) F.Carrier,
        IsIntegralMatrix (u.val * B * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)))
    (hval : ∀ k : GeneralLinear (m + 1) F.Carrier, IsIntegralMatrix k →
      f'.val (rankInclusion 1 (k * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹)) =
        κ₁ * ((χ (determinant k) : ℂ))⁻¹)
    (Fbig : RankinSelberg.WhittakerFunctions ψ (m + 1))
    (hFbig : ∀ g, Fbig.val g = twistedSmear F ψ η χ ω (ϖ : F.Carrier) c f T f' g)
    (LF : OpenSubgroup (GeneralLinear (m + 1 + 1) F.Carrier))
    (hFL : ∀ g l, l ∈ LF → Fbig.val (g * l) = Fbig.val g)
    (W'' : RankinSelberg.InverseWhittakerFunctions ψ m)
    (LW : OpenSubgroup (GeneralLinear (m + 1) F.Carrier))
    (hWL : ∀ g l, l ∈ LW → W''.val (g * l) = W''.val g) (ωτ : ℂ)
    (hWc : ∀ g, W''.val (g * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)) =
      ωτ * W''.val g)
    (s : ℂ) :
    RankinSelberg.corankOneIntegral (ψ.scale (-1)) abv (unipotentQuotientHaar F.Carrier m)
        (RankinSelberg.firstDualFunction ψ (m + 1) Fbig)
        (RankinSelberg.secondDualFunction ψ m W'') s =
      dualShellConstant F η χ ϖ c m κ₁ ωτ s * ((ω (-1) : ℂ))⁻¹ *
        ∫ g, (firstColumnOpenSubgroup F.Carrier m f :
            Set (GeneralLinear (m + 1) F.Carrier)).indicator
          (fun k => (firstColumnCharacter ω hf k)⁻¹ * W''.val k) g
          ∂generalLinearHaar F.Carrier m := by
  classical
  set Φ := RankinSelberg.corankOneFunction (ψ.scale (-1)) abv
    (RankinSelberg.firstDualFunction ψ (m + 1) Fbig)
    (RankinSelberg.secondDualFunction ψ m W'') s with hΦ
  set z := Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹ with hz
  set K := Conductor.levelOpenSubgroup F.Carrier m 0 with hK
  set C := dualShellConstant F η χ ϖ c m κ₁ ωτ s with hC
  have hcompat := unipotentQuotientHaar_isCompatible F.Carrier m
  have hΦN : ∀ (u : upperUnipotent (m + 1) F.Carrier) g, Φ (u.val * g) = Φ g :=
    fun u g => RankinSelberg.corankOneFunction_invariant _ _ _ _ _ u g
  -- the quotient integral as an integral of representatives
  have h1 : RankinSelberg.corankOneIntegral (ψ.scale (-1)) abv
      (unipotentQuotientHaar F.Carrier m) (RankinSelberg.firstDualFunction ψ (m + 1) Fbig)
      (RankinSelberg.secondDualFunction ψ m W'') s =
      ∫ q, Φ q.out ∂unipotentQuotientHaar F.Carrier m := by
    unfold RankinSelberg.corankOneIntegral
    congr 1
    funext q
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have h2 := integral_out_mul_right (unipotentQuotientHaar F.Carrier m)
    hcompat.right_invariant Φ hΦN z
  -- continuity through a common open subgroup
  set L : OpenSubgroup (GeneralLinear (m + 1) F.Carrier) :=
    LF.comap ((inverseTranspose (m + 1 + 1) F.Carrier).toMonoidHom.comp (rankInclusion 1))
      ((continuous_inverseTranspose (m + 1 + 1) F.Carrier).comp
        (rankInclusionContinuous (R := F.Carrier) (n := m + 1) 1).continuous_toFun) ⊓
    LW.comap (inverseTranspose (m + 1) F.Carrier).toMonoidHom
      (continuous_inverseTranspose (m + 1) F.Carrier) ⊓ K with hL
  have hΦL : ∀ g l, l ∈ L → Φ (g * l) = Φ g := by
    intro g l hl
    obtain ⟨⟨hl1, hl2⟩, hl3⟩ := hl
    simp only [hΦ, RankinSelberg.corankOneFunction, RankinSelberg.firstDualFunction_apply,
      RankinSelberg.secondDualFunction_apply]
    rw [map_mul, map_mul, ← mul_assoc,
      hFL _ _ (show inverseTranspose (m + 1 + 1) F.Carrier (rankInclusion 1 l) ∈ LF from hl1),
      map_mul, ← mul_assoc,
      hWL _ _ (show inverseTranspose (m + 1) F.Carrier l ∈ LW from hl2)]
    congr 1
    exact Conductor.determinantWeight_mul_integral (abv_eq_one_of_valuation F) g l
      (by rw [← Conductor.levelSubgroup_zero]; exact hl3) _
  have hφc : Continuous (fun g => Φ (g * z)) := by
    apply LastRowReductionLocal.continuous_of_rightInvariant L
    intro x j hj
    change Φ (x * j * z) = Φ (x * z)
    rw [mul_assoc, ← scalar_commute, ← mul_assoc, hΦL _ _ hj]
  -- support in `N GL(O)`
  have hzz : z * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c) = 1 := by
    rw [hz, ← map_mul, inv_mul_cancel, map_one]
  have hsupp' : ∀ g, Φ (g * z) ≠ 0 → ∃ u : upperUnipotent (m + 1) F.Carrier, u.val * g ∈ K := by
    intro g hg
    have hf'ne : f'.val (rankInclusion 1 (g * z)) ≠ 0 := by
      intro h0
      apply hg
      simp only [hΦ, RankinSelberg.corankOneFunction, RankinSelberg.firstDualFunction_apply]
      rw [hFbig, twistedSmear_at_dual F ψ η hψ χ hf hω hscale T hT hcov f', h0]
      ring
    obtain ⟨u, hu⟩ := hsupp _ hf'ne
    refine ⟨u, (isIntegralMatrix_iff_mem_level F _).1 ?_⟩
    rwa [mul_assoc, mul_assoc, hzz, mul_one] at hu
  have hHK : unipotentHaar F.Carrier m {u : upperUnipotent (m + 1) F.Carrier |
      u.val ∈ (K : Set (GeneralLinear (m + 1) F.Carrier))} = 1 := by
    have hset : {u : upperUnipotent (m + 1) F.Carrier |
        u.val ∈ (K : Set (GeneralLinear (m + 1) F.Carrier))} =
        (unipotentIntegralOpen F.Carrier m : Set (upperUnipotent (m + 1) F.Carrier)) := by
      ext u
      rfl
    rw [hset, unipotentHaar_integral]
  have hKc : IsCompact (K : Set (GeneralLinear (m + 1) F.Carrier)) := by
    have := localField_t2 F.Carrier
    have hO : IsCompact ((ValuativeRel.valuation F.Carrier).integer : Set F.Carrier) :=
      isCompact_integer F
    have h := Langlands.GeneralLinearGroup.isCompact_integralSubgroup (Fin (m + 1))
      (ValuativeRel.valuation F.Carrier).integer hO
    convert h using 1
    ext g
    rw [SetLike.mem_coe, SetLike.mem_coe, Langlands.GeneralLinearGroup.mem_integralSubgroup,
      ← isIntegralMatrix_iff_mem_level]
  have h3 := integral_out_of_support (upperUnipotent (m + 1) F.Carrier)
    (generalLinearHaar F.Carrier m) (unipotentHaar F.Carrier m) _ hcompat K hKc hHK
    (fun g => Φ (g * z)) hφc (fun u g => by simp only [mul_assoc]; exact hΦN u (g * z)) hsupp'
  -- pointwise on `GL(O)`, then substitute and evaluate
  have h4 : (K : Set (GeneralLinear (m + 1) F.Carrier)).indicator (fun g => Φ (g * z)) =
      (K : Set (GeneralLinear (m + 1) F.Carrier)).indicator (fun k =>
        C * unitLastWeight ω f (fun i => -k (Fin.last m) i.rev) *
          W''.val (weylLong (m + 1) F.Carrier * inverseTranspose (m + 1) F.Carrier k)) := by
    funext g
    by_cases hg : g ∈ (K : Set (GeneralLinear (m + 1) F.Carrier))
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg]
      exact corankOneFunction_dualShell F hψ hf hω hscale T hT hcov f' κ₁ hval Fbig hFbig W'' ωτ
        hWc s g ((isIntegralMatrix_iff_mem_level F g).2 hg)
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]
  have h5 : ∫ g, (K : Set (GeneralLinear (m + 1) F.Carrier)).indicator (fun k =>
        C * unitLastWeight ω f (fun i => -k (Fin.last m) i.rev) *
          W''.val (weylLong (m + 1) F.Carrier * inverseTranspose (m + 1) F.Carrier k)) g
        ∂generalLinearHaar F.Carrier m =
      ∫ g, C * ((ω (-1) : ℂ))⁻¹ * (firstColumnOpenSubgroup F.Carrier m f :
            Set (GeneralLinear (m + 1) F.Carrier)).indicator
          (fun k => (firstColumnCharacter ω hf k)⁻¹ * W''.val k) g
        ∂generalLinearHaar F.Carrier m := by
    rw [← integral_weylLong_inverseTranspose F]
    congr 1
    funext g
    by_cases hg : IsIntegralMatrix g
    · have hg' : weylLong (m + 1) F.Carrier * inverseTranspose (m + 1) F.Carrier g ∈
          (K : Set (GeneralLinear (m + 1) F.Carrier)) :=
        (isIntegralMatrix_iff_mem_level F _).1
          ((isIntegralMatrix_weylLong_inverseTranspose_iff F g).2 hg)
      rw [Set.indicator_of_mem hg', weylLong_inverseTranspose_involutive]
      simp only [weylLong_inverseTranspose_last]
      rw [unitLastWeight_firstColumn hf hω g hg]
      by_cases h0 : InFirstColumn f g
      · simp only [h0, ↓reduceDIte]
        rw [Set.indicator_of_mem (show g ∈ (firstColumnOpenSubgroup F.Carrier m f :
            Set (GeneralLinear (m + 1) F.Carrier)) from h0), firstColumnCharacter_of_mem ω hf h0,
          inv_inv]
        ring
      · simp only [h0, ↓reduceDIte]
        rw [Set.indicator_of_notMem (show g ∉ (firstColumnOpenSubgroup F.Carrier m f :
            Set (GeneralLinear (m + 1) F.Carrier)) from h0)]
        ring
    · have hg' : weylLong (m + 1) F.Carrier * inverseTranspose (m + 1) F.Carrier g ∉
          (K : Set (GeneralLinear (m + 1) F.Carrier)) := fun h =>
        hg ((isIntegralMatrix_weylLong_inverseTranspose_iff F g).1
          ((isIntegralMatrix_iff_mem_level F _).2 h))
      have h0 : g ∉ (firstColumnOpenSubgroup F.Carrier m f :
          Set (GeneralLinear (m + 1) F.Carrier)) := fun h =>
        hg (inFirstColumn_isIntegralMatrix F h)
      rw [Set.indicator_of_notMem hg', Set.indicator_of_notMem h0]
      ring
  rw [h1, ← h2, h3, h4, h5, integral_const_mul]

end Shell

end Langlands.RankinSelberg.HighlyRamified
