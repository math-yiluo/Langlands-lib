import Langlands.Representation.RankinSelberg.HighlyRamified.ShellIdentity
import Langlands.Representation.RankinSelberg.HighlyRamified.CompletenessStep
import Langlands.Representation.RankinSelberg.HighlyRamified.TestSide
import Langlands.Representation.RankinSelberg.AdjacentRankProductContinuation
import Langlands.Representation.Whittaker.CharacterChange

/-!
# Discharging the shell identities for all test representations

The completeness step (`rightAverage_eq_target_of_shells`) needs, for every representation `π`
generic for `ψ⁻¹` and every model vector `w`, the shell identities
`∫ (F_A · 1_(ord det = j)) w_avg = [j = 0] c ∫ t w` with one constant `c`. This module derives
them from `shell_identity`.

* If the inverse `K⁰(f)`-average `w_avg` vanishes, both sides vanish.
* Otherwise `π` has a principal level vector of level `f` and its central character is `ω⁻¹`
  on the integral units, so `shell_identity` applies to `π` and to `w_avg`.
* For `j = 0` the constant of `shell_identity` depends on the central character of `π`. An
  unramified twist moves the central character to a fixed `ω₀` without changing the two sides.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration Matrix Langlands.GeneralLinear

universe uF uV

section Generic

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Genericity for `ψ⁻¹` gives genericity for `ψ` (change of additive character by `-1`). -/
theorem isGeneric_of_scale_neg_one (ψ : UnitaryAdditiveCharacter F)
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    (hπ : IsGeneric (ψ.scale (-1)) n π) : IsGeneric ψ n π := by
  refine ⟨hπ.1, hπ.2.1, ?_⟩
  obtain ⟨ℓ, hℓ⟩ := hπ.2.2
  have hψ : (ψ.scale (-1)).scale (-1) = ψ := by
    rw [UnitaryAdditiveCharacter.scale_scale]
    simp [UnitaryAdditiveCharacter.scale_one]
  set ℓ' := characterChangeFunctionalEquiv (ψ.scale (-1)) π (-1) ℓ with hℓ'
  have hne : ℓ' ≠ 0 := by
    intro h0
    apply hℓ
    have : ℓ = 0 := (characterChangeFunctionalEquiv (ψ.scale (-1)) π (-1)).map_eq_zero_iff.mp h0
    rw [this]
    rfl
  have key : HasFunctional (N := upperUnipotent (n + 1) F)
      (θ := standardCharacter ((ψ.scale (-1)).scale (-1)) n) π :=
    ⟨ℓ', fun h0 => hne (Subtype.ext h0)⟩
  rw [hψ] at key
  exact key

end Generic

section Canonical

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance shellDischargeFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance shellDischargeValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance shellDischargeLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance shellDischargeFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance shellDischargeFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance shellDischargeGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance shellDischargeGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance shellDischargeUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance shellDischargeUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance shellDischargeQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := borel _
local instance shellDischargeQuotientBorel (r : ℕ) : BorelSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable {m : ℕ} {ω : F.Carrierˣ →* ℂˣ} {f : ℕ} (hf : 0 < f)

/-- The inverse `K⁰(f)`-average transforms by `ω(k₀₀)⁻¹` under right translation by
`k ∈ K⁰(f)`. -/
theorem inverseAverage_firstColumn_mul (hω : TrivialOnPrincipalUnits ω f)
    (W : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ)
    (LW : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hWL : ∀ g l, l ∈ LW → W (g * l) = W g)
    (g : Langlands.GeneralLinear (m + 1) F.Carrier) {k₀ : Langlands.GeneralLinear (m + 1) F.Carrier}
    (hk₀ : InFirstColumn f k₀) :
    inverseAverage (generalLinearHaar F.Carrier m) W LW hWL (firstColumnWeight ω hf)
        (firstColumnWeight_isLocallyConstant F hf hω)
        (firstColumnWeight_hasCompactSupport F hf) (g * k₀) =
      ((ω (firstEntryUnit hf k₀ hk₀) : ℂ))⁻¹ *
        inverseAverage (generalLinearHaar F.Carrier m) W LW hWL (firstColumnWeight ω hf)
          (firstColumnWeight_isLocallyConstant F hf hω)
          (firstColumnWeight_hasCompactSupport F hf) g := by
  rw [inverseAverage_apply, inverseAverage_apply,
    ← integral_mul_right_eq_self (fun k => firstColumnWeight ω hf k * W (g * k₀ * k⁻¹)) k₀,
    ← integral_const_mul]
  congr 1
  funext k
  have hW : W (g * k₀ * (k * k₀)⁻¹) = W (g * k⁻¹) := by
    congr 1; group
  rw [hW]
  by_cases hk : InFirstColumn f k
  · have hkk : InFirstColumn f (k * k₀) := mul_mem hk hk₀
    rw [firstColumnWeight_of_mem ω hf hkk, firstColumnWeight_of_mem ω hf hk,
      omega_firstEntry_mul hf hω hk hk₀ hkk, mul_inv]
    ring
  · have hkk : ¬ InFirstColumn f (k * k₀) := fun h => hk (by
      simpa using mul_mem h (inv_mem hk₀))
    rw [firstColumnWeight_of_not_mem ω hf hkk, firstColumnWeight_of_not_mem ω hf hk]
    ring

/-- Integral unit scalars lie in `K⁰(f)`, with first entry the scalar. -/
theorem inFirstColumn_scalar {z : F.Carrierˣ} (hz : IsIntegralUnit (z : F.Carrier)) :
    InFirstColumn f (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) z) := by
  rw [inFirstColumn_iff]
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun j hj => ⟨0, Submodule.zero_mem _, ?_⟩⟩
  · change (Matrix.scalar (Fin (m + 1)) (z : F.Carrier)) i j ∈ _
    by_cases h : i = j
    · subst h; simpa [Matrix.scalar_apply] using hz.2.1
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]
  · rw [← map_inv]
    change (Matrix.scalar (Fin (m + 1)) ((z⁻¹ : F.Carrierˣ) : F.Carrier)) i j ∈ _
    by_cases h : i = j
    · subst h; simpa [Matrix.scalar_apply] using hz.2.2
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]
  · change (0 : F.Carrier) = (Matrix.scalar (Fin (m + 1)) (z : F.Carrier)) j 0
    simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hj]

/-- The inverse average transforms by `ω(z)⁻¹` under integral unit scalars. -/
theorem inverseAverage_scalar (hω : TrivialOnPrincipalUnits ω f)
    (W : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ)
    (LW : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hWL : ∀ g l, l ∈ LW → W (g * l) = W g) (z : F.Carrierˣ) (hz : IsIntegralUnit (z : F.Carrier))
    (g : Langlands.GeneralLinear (m + 1) F.Carrier) :
    inverseAverage (generalLinearHaar F.Carrier m) W LW hWL (firstColumnWeight ω hf)
        (firstColumnWeight_isLocallyConstant F hf hω)
        (firstColumnWeight_hasCompactSupport F hf)
        (g * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) z) =
      ((ω z : ℂ))⁻¹ *
        inverseAverage (generalLinearHaar F.Carrier m) W LW hWL (firstColumnWeight ω hf)
          (firstColumnWeight_isLocallyConstant F hf hω)
          (firstColumnWeight_hasCompactSupport F hf) g := by
  have hk := inFirstColumn_scalar F (m := m) (f := f) hz
  rw [inverseAverage_firstColumn_mul F hf hω W LW hWL g hk]
  have hu : firstEntryUnit hf _ hk = z := by
    ext
    rw [firstEntryUnit_val]
    change (Matrix.scalar (Fin (m + 1)) (z : F.Carrier)) 0 0 = _
    simp [Matrix.scalar_apply]
  rw [hu]

/-- An unramified character is trivial on `det g` when `ord det g = 0`. -/
theorem unramified_det_eq_one (y : ℂˣ) {g : Langlands.GeneralLinear (m + 1) F.Carrier}
    (hg : F.canonicalTopologicalData.ord (determinant g : F.Carrier) = 0) :
    F.canonicalTopologicalData.unramifiedCharacter y (determinant g) = 1 := by
  rw [PadicField.TopologicalData.unramifiedCharacter_apply, hg, zpow_zero]

theorem ord_det_eq_zero_of_integral {k : Langlands.GeneralLinear (m + 1) F.Carrier}
    (hk : IsIntegralMatrix k) :
    F.canonicalTopologicalData.ord (determinant k : F.Carrier) = 0 := by
  have := ord_det_mul_integral F 1 k hk
  rw [one_mul] at this
  rw [this]
  simp [F.canonicalTopologicalData.ord_one]

/-- The corank-one function at `s = 0` restricted to `diag(g,1)`:
`F_A(g) = U(diag(g,1)) |det g|^(-1/2)`. -/
def corankRestriction (ψ : UnitaryAdditiveCharacter F.Carrier) (U : WhittakerFunctions ψ (m + 1))
    (g : Langlands.GeneralLinear (m + 1) F.Carrier) : ℂ :=
  U.val (rankInclusion 1 g) * determinantWeight abv g (0 - 1 / 2)

/-- Shell integrals of the corank-one integrand at `0` as integrals of the shell
restriction against representatives. -/
theorem setIntegral_corankOneIntegrand_slice (ψ : UnitaryAdditiveCharacter F.Carrier)
    (U : WhittakerFunctions ψ (m + 1)) (W' : InverseWhittakerFunctions ψ m) (j : ℤ) :
    ∫ q in determinantSlice F.canonicalTopologicalData m j,
        corankOneIntegrand ψ abv U W' 0 q ∂unipotentQuotientHaar F.Carrier m =
      ∫ q, shellRestriction F (corankRestriction F ψ U) j q.out * W'.val q.out
        ∂unipotentQuotientHaar F.Carrier m := by
  rw [← integral_indicator (measurableSet_determinantSlice F.canonicalTopologicalData m j)]
  congr 1
  funext q
  conv_lhs => rw [← Quotient.out_eq q]
  by_cases hq : F.canonicalTopologicalData.ord (determinant q.out : F.Carrier) = j
  · rw [Set.indicator_of_mem (show Quotient.mk _ q.out ∈
        determinantSlice F.canonicalTopologicalData m j from hq), corankOneIntegrand_mk]
    simp only [shellRestriction, corankRestriction, hq, ↓reduceIte]
    ring
  · rw [Set.indicator_of_notMem (show Quotient.mk _ q.out ∉
        determinantSlice F.canonicalTopologicalData m j from hq)]
    simp only [shellRestriction, hq, ↓reduceIte, zero_mul]

/-- A Whittaker function for `ψ⁻¹` transforms by `ψ_N⁻¹`. -/
theorem scaled_whittaker_unipotent (ψ : UnitaryAdditiveCharacter F.Carrier)
    (w : WhittakerFunctions (ψ.scale (-1)) m) (u : upperUnipotent (m + 1) F.Carrier)
    (g : Langlands.GeneralLinear (m + 1) F.Carrier) :
    w.val (u.val * g) = ((standardCharacter ψ m u : ℂ))⁻¹ * w.val g := by
  rw [w.property u g]
  congr 1
  rw [standardCharacter_scale_neg_one, inverseStandardCharacter_apply, standardCharacter_apply]

/-- The constant of the `j = 0` shell identity for a test representation with central
character `ω_π`. -/
def shellConstant (η : AdditiveHaarMeasure F.Carrier) (χ : F.Carrierˣ →* ℂˣ)
    (ω : F.Carrierˣ →* ℂˣ) (ϖ : F.Carrierˣ) (c f m : ℕ) (κ₁ : ℂ)
    (C : (F.Carrierˣ →* ℂˣ) → ℂˣ) (ωπ : F.Carrierˣ →* ℂˣ) : ℂ :=
  (((ωπ (-1) : ℂ) ^ (m + 1)))⁻¹ * ((C ωπ : ℂ))⁻¹ *
    (dualShellConstant F η χ ϖ c m κ₁ (ωπ (ϖ ^ c)) 0 * ((ω (-1) : ℂ))⁻¹ *
      ((generalLinearHaar F.Carrier m).real
        (firstColumnOpenSubgroup F.Carrier m f : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) :
          ℂ)) *
    (F.canonicalTopologicalData.residueCardinality : ℂ) ^ (((c * (m + 1) : ℕ) : ℤ))

/-- The shell identities for one test representation `π` (generic for `ψ⁻¹`) whose
inverse `K⁰(f)`-average of `w` does not vanish identically. -/
theorem shell_average_identity (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : HasIntegerConductorAt F ψ)
    (η ν : AdditiveHaarMeasure F.Carrier) (χ : F.Carrierˣ →* ℂˣ)
    {c : ℕ} (hω : TrivialOnPrincipalUnits ω f)
    (ϖ : F.Carrierˣ) (hϖ : F.canonicalTopologicalData.ord (ϖ : F.Carrier) = 1)
    (hscale : ∀ o ∈ (ValuativeRel.valuation F.Carrier).integer,
      InPow f ((ϖ : F.Carrier) ^ c * o))
    (T : Finset (Fin (m + 1) → F.Carrier))
    (hT : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ integerLattice F m → t = t')
    (hcov : ∀ y, dualWeight ω (ϖ : F.Carrier) c f y ≠ 0 → ∃ t ∈ T, y - t ∈ integerLattice F m)
    (f' : InverseWhittakerFunctions ψ (m + 1)) (κ₁ : ℂ)
    (hsupp : ∀ B : Langlands.GeneralLinear (m + 1) F.Carrier, f'.val (rankInclusion 1 B) ≠ 0 →
      ∃ u : upperUnipotent (m + 1) F.Carrier,
        IsIntegralMatrix (u.val * B * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)))
    (hval : ∀ k : Langlands.GeneralLinear (m + 1) F.Carrier, IsIntegralMatrix k →
      f'.val (rankInclusion 1 (k * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹)) =
        κ₁ * ((χ (determinant k) : ℂ))⁻¹)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {Pi : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V}
    (hPi : IsOfWhittakerType (m + 1) (standardCharacter ψ (m + 1)) Pi)
    (ℓ : glFunctionals ψ (m + 1) Pi) (hℓ : ℓ.val ≠ 0)
    (Fbig : (coefficientModel Pi ℓ).toSubmodule)
    (hFbig : ∀ g, Fbig.val.val g = twistedSmear F ψ η χ ω (ϖ : F.Carrier) c f T f' g)
    (LF : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))
    (hFL : ∀ g l, l ∈ LF → Fbig.val.val (g * l) = Fbig.val.val g)
    (C : (F.Carrierˣ →* ℂˣ) → ℂˣ)
    {X : Type uV} [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) X)
    (hπ : IsGeneric (ψ.scale (-1)) m π) (ℓπ : glFunctionals (ψ.scale (-1)) m π)
    (w : (coefficientModel π ℓπ).toSubmodule)
    (Lw : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hwL : ∀ g l, l ∈ Lw → w.val.val (g * l) = w.val.val g)
    (ωπ : F.Carrierˣ →* ℂˣ) (hωπ : Classification.HasGLCentralCharacter F.Carrier (m + 1) π ωπ)
    (hG : HasPrincipalLevelVector F π f → ∃ G : RationalFunctions,
      IsPadicPairGammaFactor F ψ ν Pi π G ∧
        G = rationalEpsilonMonomial (C ωπ) ((c * (m + 1) : ℕ) : ℤ))
    (hne : ∃ g, inverseAverage (generalLinearHaar F.Carrier m) w.val.val Lw hwL
      (firstColumnWeight ω hf) (firstColumnWeight_isLocallyConstant F hf hω)
      (firstColumnWeight_hasCompactSupport F hf) g ≠ 0) (j : ℤ) :
    ∫ q, shellRestriction F (corankRestriction F ψ Fbig.val) j q.out *
        inverseAverage (generalLinearHaar F.Carrier m) w.val.val Lw hwL
          (firstColumnWeight ω hf) (firstColumnWeight_isLocallyConstant F hf hω)
          (firstColumnWeight_hasCompactSupport F hf) q.out ∂unipotentQuotientHaar F.Carrier m =
      (if j = 0 then shellConstant F η χ ω ϖ c f m κ₁ C ωπ else 0) *
        ∫ q, firstColumnTarget ω hf (standardCharacter ψ m) q.out * w.val.val q.out
          ∂unipotentQuotientHaar F.Carrier m := by
  classical
  set Wavg := inverseAverage (generalLinearHaar F.Carrier m) w.val.val Lw hwL
    (firstColumnWeight ω hf) (firstColumnWeight_isLocallyConstant F hf hω)
    (firstColumnWeight_hasCompactSupport F hf) with hWavg
  have hwN := scaled_whittaker_unipotent F ψ w.val
  obtain ⟨hAN, hAL⟩ := inverseAverage_firstColumn_properties F hf hω (standardCharacter ψ m)
    w.val.val Lw hwL hwN
  -- the averaged vector as a model vector
  obtain ⟨Ψ, hΨ⟩ := exists_model_inverseAverage π ℓπ w (generalLinearHaar F.Carrier m) Lw hwL
    (firstColumnWeight ω hf) (firstColumnWeight_isLocallyConstant F hf hω)
    (firstColumnWeight_hasCompactSupport F hf)
  obtain ⟨g₀, hg₀⟩ := hne
  have hΨg₀ : Ψ.val.val g₀ ≠ 0 := by rw [hΨ]; exact hg₀
  have hΨne : Ψ ≠ 0 := by
    intro h0; apply hΨg₀; rw [h0]; rfl
  have hℓπ : ℓπ.val ≠ 0 := by
    intro h0
    apply hΨg₀
    obtain ⟨v, hv⟩ := Ψ.property
    have := congrArg (fun x : WhittakerFunctions (ψ.scale (-1)) m => x.val g₀) hv
    rw [← this]
    change ℓπ.val (π g₀ v) = 0
    rw [h0]
    rfl
  set ℓ'' := functionalsCongr (standardCharacter_scale_neg_one ψ m) ℓπ with hℓ''def
  have hℓ'' : ℓ''.val ≠ 0 := hℓπ
  set W'' := Padic.scaledStandardCoefficientAsInverse F ψ π ℓπ Ψ with hW''def
  have hW''val : ∀ g, W''.val.val g = Wavg g := by
    intro g
    change Ψ.val.val g = _
    rw [hΨ]
  have hπψ : IsGeneric ψ m π := isGeneric_of_scale_neg_one ψ hπ
  have hτ : IsOfWhittakerType m (inverseStandardCharacter ψ m) π :=
    isOfInverseWhittakerType_of_isGeneric F hπψ
  obtain ⟨LW, hLW⟩ := model_rightInvariant hπ.2.1.1 ℓ'' W''
  have hWc : ∀ g, W''.val.val (g * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)) =
      (ωπ (ϖ ^ c) : ℂ) * W''.val.val g :=
    fun g => model_mul_scalar π ωπ hωπ ℓ'' W'' (ϖ ^ c) g
  have hlev : HasPrincipalLevelVector F π f :=
    hasPrincipalLevelVector_of_model F π hπ.1 ℓπ Ψ hΨne f (fun g k hk => by
      rw [hΨ]
      exact hAL g k hk)
  obtain ⟨G, hGcert, hGC⟩ := hG hlev
  obtain ⟨ζ, hζ, hsh⟩ := shell_identity F ψ hψ η ν χ hf hω ϖ hϖ hscale T hT hcov f' κ₁ hsupp hval
    hPi hτ ℓ hℓ ℓ'' hℓ'' Fbig hFbig LF hFL W'' LW hLW (ωπ (ϖ ^ c) : ℂ) hWc hGcert (C ωπ) hGC
  -- the minus-one scalar is `ω_π(-1)`
  have hζω : (ζ : ℂ) = (ωπ (-1) : ℂ) := by
    have h1 := hζ W'' g₀
    have hneg1 : Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (-1 : F.Carrierˣ) =
        (-1 : Langlands.GeneralLinear (m + 1) F.Carrier) := by
      apply Units.ext
      ext i j
      by_cases h : i = j
      · subst h; simp [Matrix.scalar_apply]
      · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    rw [← hneg1, scalar_commute, model_mul_scalar π ωπ hωπ ℓ'' W'' (-1) g₀] at h1
    have hW0 : W''.val.val g₀ ≠ 0 := by rw [hW''val]; exact hg₀
    exact (mul_right_cancel₀ hW0 h1).symm
  have hIK := integral_firstColumn_inverseAverage F hf hω (standardCharacter ψ m)
    (standardCharacter_eq_one_of_integral F ψ hψ) w.val.val Lw hwL hwN
  have hsj := hsh j
  rw [setIntegral_corankOneIntegrand_slice F ψ Fbig.val W''.val j] at hsj
  have hlhs : ∫ q, shellRestriction F (corankRestriction F ψ Fbig.val) j q.out * W''.val.val q.out
      ∂unipotentQuotientHaar F.Carrier m =
      ∫ q, shellRestriction F (corankRestriction F ψ Fbig.val) j q.out * Wavg q.out
        ∂unipotentQuotientHaar F.Carrier m := by
    congr 1; funext q; rw [hW''val]
  rw [hlhs] at hsj
  rw [hsj]
  have hIK' : ∫ k, (firstColumnOpenSubgroup F.Carrier m f :
        Set (Langlands.GeneralLinear (m + 1) F.Carrier)).indicator
        (fun k => (firstColumnCharacter ω hf k)⁻¹ * W''.val.val k) k
        ∂generalLinearHaar F.Carrier m =
      ((generalLinearHaar F.Carrier m).real
        (firstColumnOpenSubgroup F.Carrier m f : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) :
          ℂ) *
        ∫ q, firstColumnTarget ω hf (standardCharacter ψ m) q.out * w.val.val q.out
          ∂unipotentQuotientHaar F.Carrier m := by
    rw [← hIK]
    congr 1; funext k
    simp only [hW''val]
    rfl
  by_cases hj : j = 0
  · simp only [hj, ↓reduceIte]
    rw [hIK', hζω]
    unfold shellConstant
    ring
  · simp only [hj, ↓reduceIte, zero_mul]

/-- The target vanishes off the shell `ord det = 0`. -/
theorem firstColumnTarget_ord_det (ψN : upperUnipotent (m + 1) F.Carrier →* ℂˣ)
    {g : Langlands.GeneralLinear (m + 1) F.Carrier} (hg : firstColumnTarget ω hf ψN g ≠ 0) :
    F.canonicalTopologicalData.ord (determinant g : F.Carrier) = 0 := by
  obtain ⟨u, hu⟩ := firstColumnTarget_support hf ψN hg
  have h1 := ord_det_eq_zero_of_integral F ((inFirstColumn_iff _).1 hu).1
  rwa [determinant_unipotent_mul] at h1

theorem firstColumnVolume_ne_zero :
    ((generalLinearHaar F.Carrier m).real
      (firstColumnOpenSubgroup F.Carrier m f : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) :
        ℂ) ≠ 0 := by
  rw [Complex.ofReal_ne_zero, measureReal_def]
  have hpos := (firstColumnOpenSubgroup F.Carrier m f).isOpen.measure_pos
    (generalLinearHaar F.Carrier m) ⟨1, (firstColumnOpenSubgroup F.Carrier m f).one_mem⟩
  have hfin := (isCompact_firstColumnOpenSubgroup F.Carrier m f).measure_lt_top
    (μ := generalLinearHaar F.Carrier m)
  exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'

/-- The shell identities for every test representation, with the single constant
`shellConstant … ω₀` of a fixed character `ω₀` extending `ω⁻¹` from the integral units. -/
theorem shell_discharge (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : HasIntegerConductorAt F ψ)
    (η ν : AdditiveHaarMeasure F.Carrier) (χ : F.Carrierˣ →* ℂˣ)
    {c : ℕ} (hω : TrivialOnPrincipalUnits ω f)
    (ϖ : F.Carrierˣ) (hϖ : F.canonicalTopologicalData.ord (ϖ : F.Carrier) = 1)
    (hscale : ∀ o ∈ (ValuativeRel.valuation F.Carrier).integer,
      InPow f ((ϖ : F.Carrier) ^ c * o))
    (T : Finset (Fin (m + 1) → F.Carrier))
    (hT : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ integerLattice F m → t = t')
    (hcov : ∀ y, dualWeight ω (ϖ : F.Carrier) c f y ≠ 0 → ∃ t ∈ T, y - t ∈ integerLattice F m)
    (f' : InverseWhittakerFunctions ψ (m + 1)) (κ₁ : ℂ)
    (hsupp : ∀ B : Langlands.GeneralLinear (m + 1) F.Carrier, f'.val (rankInclusion 1 B) ≠ 0 →
      ∃ u : upperUnipotent (m + 1) F.Carrier,
        IsIntegralMatrix (u.val * B * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)))
    (hval : ∀ k : Langlands.GeneralLinear (m + 1) F.Carrier, IsIntegralMatrix k →
      f'.val (rankInclusion 1 (k * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹)) =
        κ₁ * ((χ (determinant k) : ℂ))⁻¹)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {Pi : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V}
    (hPi : IsOfWhittakerType (m + 1) (standardCharacter ψ (m + 1)) Pi)
    (ℓ : glFunctionals ψ (m + 1) Pi) (hℓ : ℓ.val ≠ 0)
    (Fbig : (coefficientModel Pi ℓ).toSubmodule)
    (hFbig : ∀ g, Fbig.val.val g = twistedSmear F ψ η χ ω (ϖ : F.Carrier) c f T f' g)
    (LF : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))
    (hFL : ∀ g l, l ∈ LF → Fbig.val.val (g * l) = Fbig.val.val g)
    (C : (F.Carrierˣ →* ℂˣ) → ℂˣ)
    (hGall : ∀ (X : Type uV) [AddCommGroup X] [Module ℂ X]
      (τ : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) X)
      (ωτ : F.Carrierˣ →* ℂˣ), IsGeneric ψ m τ → HasPrincipalLevelVector F τ f →
      Classification.HasGLCentralCharacter F.Carrier (m + 1) τ ωτ →
      ∃ G : RationalFunctions, IsPadicPairGammaFactor F ψ ν Pi τ G ∧
        G = rationalEpsilonMonomial (C ωτ) ((c * (m + 1) : ℕ) : ℤ))
    (ω₀ : F.Carrierˣ →* ℂˣ)
    (hω₀ : ∀ z : F.Carrierˣ, IsIntegralUnit (z : F.Carrier) → ω₀ z = (ω z)⁻¹) :
    ∀ (X : Type uV) [AddCommGroup X] [Module ℂ X]
      (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) X),
      IsGeneric (ψ.scale (-1)) m π → ∀ (ℓπ : glFunctionals (ψ.scale (-1)) m π)
      (w : (coefficientModel π ℓπ).toSubmodule)
      (Lw : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
      (hwL : ∀ g l, l ∈ Lw → w.val.val (g * l) = w.val.val g) (j : ℤ),
      ∫ q, shellRestriction F (corankRestriction F ψ Fbig.val) j q.out *
          inverseAverage (generalLinearHaar F.Carrier m) w.val.val Lw hwL
            (firstColumnWeight ω hf) (firstColumnWeight_isLocallyConstant F hf hω)
            (firstColumnWeight_hasCompactSupport F hf) q.out ∂unipotentQuotientHaar F.Carrier m =
        (if j = 0 then shellConstant F η χ ω ϖ c f m κ₁ C ω₀ else 0) *
          ∫ q, firstColumnTarget ω hf (standardCharacter ψ m) q.out * w.val.val q.out
            ∂unipotentQuotientHaar F.Carrier m := by
  classical
  intro X _ _ π hπ ℓπ w Lw hwL j
  set Wavg := inverseAverage (generalLinearHaar F.Carrier m) w.val.val Lw hwL
    (firstColumnWeight ω hf) (firstColumnWeight_isLocallyConstant F hf hω)
    (firstColumnWeight_hasCompactSupport F hf) with hWavg
  have hwN := scaled_whittaker_unipotent F ψ w.val
  have hIK := integral_firstColumn_inverseAverage F hf hω (standardCharacter ψ m)
    (standardCharacter_eq_one_of_integral F ψ hψ) w.val.val Lw hwL hwN
  by_cases hne : ∃ g, Wavg g ≠ 0
  · -- the central character and the level of `π`
    obtain ⟨ωq, hωq⟩ := exists_quasicharacter_hasGLCentralCharacter F (ψ.scale (-1)) π hπ
    set ωπ : F.Carrierˣ →* ℂˣ := (ωq : F.Carrierˣ →* ℂˣ) with hωπdef
    obtain ⟨Ψ, hΨ⟩ := exists_model_inverseAverage π ℓπ w (generalLinearHaar F.Carrier m) Lw hwL
      (firstColumnWeight ω hf) (firstColumnWeight_isLocallyConstant F hf hω)
      (firstColumnWeight_hasCompactSupport F hf)
    obtain ⟨g₀, hg₀⟩ := hne
    have hΨne : Ψ ≠ 0 := by
      intro h0; apply hg₀; rw [hWavg, ← hΨ, h0]; rfl
    have hunits : ∀ z : F.Carrierˣ, IsIntegralUnit (z : F.Carrier) → ωπ z = (ω z)⁻¹ :=
      centralCharacter_eq_inv_of_model π ωπ ω hωq ℓπ Ψ hΨne (fun z hz g => by
        rw [hΨ]; exact inverseAverage_scalar F hf hω w.val.val Lw hwL z hz g)
    obtain ⟨hAN, hAL⟩ := inverseAverage_firstColumn_properties F hf hω (standardCharacter ψ m)
      w.val.val Lw hwL hwN
    have hlev : HasPrincipalLevelVector F π f :=
      hasPrincipalLevelVector_of_model F π hπ.1 ℓπ Ψ hΨne f (fun g k hk => by
        rw [hΨ]; exact hAL g k hk)
    have hπψ : IsGeneric ψ m π := isGeneric_of_scale_neg_one ψ hπ
    by_cases hj : j = 0
    · subst hj
      -- twist to the central character `ω₀`
      obtain ⟨y, hy⟩ := exists_unramified_pow_of_eq_on_units F ω₀ ωπ
        (fun z hz => by rw [hω₀ z hz, hunits z hz]) m
      set nu := F.canonicalTopologicalData.unramifiedCharacter y with hnu
      obtain ⟨hπ'gen, hπ'lev, hπ'cent⟩ :=
        unramifiedTwist_properties F (ψ.scale (-1)) π hπ ωπ hωq hlev y
      rw [← hy] at hπ'cent
      set π' := Langlands.twist (nu.comp determinant) π with hπ'
      have hνu : ∀ u : upperUnipotent (m + 1) F.Carrier, (nu.comp determinant) u.val = 1 :=
        fun u => determinantCharacter_unipotent nu u
      set ℓπ' := twistFunctional (upperUnipotent (m + 1) F.Carrier)
        (standardCharacter (ψ.scale (-1)) m) (nu.comp determinant) hνu π ℓπ with hℓπ'
      set w' := twistModelLinearMap (upperUnipotent (m + 1) F.Carrier)
        (standardCharacter (ψ.scale (-1)) m) (nu.comp determinant) hνu π ℓπ w with hw'
      have hw'val : ∀ g, w'.val.val g = (nu (determinant g) : ℂ) * w.val.val g := fun _ => rfl
      set Lw' := Lw ⊓ Conductor.levelOpenSubgroup F.Carrier m 0 with hLw'
      have hwL' : ∀ g l, l ∈ Lw' → w'.val.val (g * l) = w'.val.val g := by
        intro g l hl
        have hl1 : nu (determinant l) = 1 := unramified_det_eq_one F y
          (ord_det_eq_zero_of_integral F ((isIntegralMatrix_iff_mem_level F l).2 hl.2))
        rw [hw'val, hw'val, hwL g l hl.1]
        simp only [map_mul, hl1, mul_one]
      have hWavg' : ∀ g, inverseAverage (generalLinearHaar F.Carrier m) w'.val.val Lw' hwL'
          (firstColumnWeight ω hf) (firstColumnWeight_isLocallyConstant F hf hω)
          (firstColumnWeight_hasCompactSupport F hf) g = (nu (determinant g) : ℂ) * Wavg g := by
        intro g
        rw [inverseAverage_apply, hWavg, inverseAverage_apply, ← integral_const_mul]
        congr 1
        funext k
        by_cases hk : InFirstColumn f k
        · have hk1 : nu (determinant k) = 1 := unramified_det_eq_one F y
            (ord_det_eq_zero_of_integral F ((inFirstColumn_iff k).1 hk).1)
          rw [hw'val]
          simp only [map_mul, map_inv, hk1, inv_one, mul_one]
          ring
        · rw [firstColumnWeight_of_not_mem ω hf hk]
          ring
      have hne' : ∃ g, inverseAverage (generalLinearHaar F.Carrier m) w'.val.val Lw' hwL'
          (firstColumnWeight ω hf) (firstColumnWeight_isLocallyConstant F hf hω)
          (firstColumnWeight_hasCompactSupport F hf) g ≠ 0 :=
        ⟨g₀, by rw [hWavg']; exact mul_ne_zero (Units.ne_zero _) hg₀⟩
      have hmain := shell_average_identity F hf ψ hψ η ν χ hω ϖ hϖ hscale T hT hcov f' κ₁
        hsupp hval hPi ℓ hℓ Fbig hFbig LF hFL C π' hπ'gen ℓπ' w' Lw' hwL' ω₀ hπ'cent
        (fun hl => hGall X π' ω₀ (isGeneric_of_scale_neg_one ψ hπ'gen) hl hπ'cent) hne' 0
      have hlhs : ∫ q, shellRestriction F (corankRestriction F ψ Fbig.val) 0 q.out *
          inverseAverage (generalLinearHaar F.Carrier m) w'.val.val Lw' hwL'
            (firstColumnWeight ω hf) (firstColumnWeight_isLocallyConstant F hf hω)
            (firstColumnWeight_hasCompactSupport F hf) q.out ∂unipotentQuotientHaar F.Carrier m =
          ∫ q, shellRestriction F (corankRestriction F ψ Fbig.val) 0 q.out * Wavg q.out
            ∂unipotentQuotientHaar F.Carrier m := by
        congr 1
        funext q
        rw [hWavg']
        by_cases h0 : F.canonicalTopologicalData.ord (determinant q.out : F.Carrier) = 0
        · have h1 : nu (determinant q.out) = 1 := unramified_det_eq_one F y h0
          rw [h1]; simp
        · simp only [shellRestriction, h0, ↓reduceIte, zero_mul]
      have hrhs : ∫ q, firstColumnTarget ω hf (standardCharacter ψ m) q.out * w'.val.val q.out
          ∂unipotentQuotientHaar F.Carrier m =
          ∫ q, firstColumnTarget ω hf (standardCharacter ψ m) q.out * w.val.val q.out
            ∂unipotentQuotientHaar F.Carrier m := by
        congr 1
        funext q
        rw [hw'val]
        by_cases ht : firstColumnTarget ω hf (standardCharacter ψ m) q.out = 0
        · rw [ht, zero_mul, zero_mul]
        · have h1 : nu (determinant q.out) = 1 :=
            unramified_det_eq_one F y (firstColumnTarget_ord_det F hf _ ht)
          rw [h1]; simp
      rw [hlhs, hrhs] at hmain
      exact hmain
    · have hmain := shell_average_identity F hf ψ hψ η ν χ hω ϖ hϖ hscale T hT hcov f' κ₁
        hsupp hval hPi ℓ hℓ Fbig hFbig LF hFL C π hπ ℓπ w Lw hwL ωπ hωq
        (fun hl => hGall X π ωπ hπψ hl hωq) ⟨g₀, hg₀⟩ j
      simp only [hj, ↓reduceIte, zero_mul] at hmain ⊢
      exact hmain
  · push Not at hne
    have hz : ∫ q, firstColumnTarget ω hf (standardCharacter ψ m) q.out * w.val.val q.out
        ∂unipotentQuotientHaar F.Carrier m = 0 := by
      have h0 : ∫ k, (firstColumnOpenSubgroup F.Carrier m f :
          Set (Langlands.GeneralLinear (m + 1) F.Carrier)).indicator
          (fun k => (firstColumnCharacter ω hf k)⁻¹ * Wavg k) k
          ∂generalLinearHaar F.Carrier m = 0 := by
        simp [hne]
      rw [h0] at hIK
      rcases mul_eq_zero.mp hIK.symm with h | h
      · exact absurd h (firstColumnVolume_ne_zero F)
      · exact h
    rw [hz, mul_zero]
    simp [hne]

end Canonical

end Langlands.RankinSelberg.HighlyRamified
