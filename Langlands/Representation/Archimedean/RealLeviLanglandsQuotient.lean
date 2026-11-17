import Langlands.Representation.Archimedean.RealLeviWitness
import Langlands.Representation.Archimedean.RealTieClasses
import Langlands.Representation.Archimedean.JacquetDual

/-!
# The Langlands quotient of a Langlands-ordered real standard module

Assume the chart integrability along standard parabolic subgroups
(`RealLeviChartIntegrableStatement`), the parabolic integration formula along them
(`RealLeviParabolicIntegrationStatement`) and the irreducibility of standard modules with
constant real exponent (`RealTemperedStandardIrreducibleStatement`). Then every
Langlands-ordered standard module has a largest proper `(𝔤, K)`-submodule
(`RealLeviLanglandsQuotientStatement`, conclusion `RealStandardLanglandsQuotientStatement`).

Proof: cut `ds` into its tie classes (`RealTieClasses.exists_tieData`) and take the witness
`φ_i`, `h₀` of `RealLeviWitnessStatement`. Let `u₀` have the product coefficients of the `φ_i`
(`RealLeviDensityStatement` with `W = ⊥`) and `Λ = Θ(u₀, ·)`. For a proper `(𝔤, K)`-submodule
`W`, `RealLeviDensityStatement` gives an annihilator `u_W` of `W` with the same product
coefficients. Its matrix coefficients with `W` vanish (`integral_mul_eq_zero_of_annihilates`),
so `Θ(u_W, w) = 0` for `w ∈ W` by `RealLeviLimitStatement`, and `Θ(u₀, w) = Θ(u_W, w)`
(`RealLeviPairing.theta_congr`). Hence the sum `R` of all proper `(𝔤, K)`-submodules lies in
`ker Λ`, which does not contain `h₀`.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealLeviLanglandsQuotient

open RealInducedBlockBound RealInducedTorusCore RealLeviChart RealPrincipalSeriesDuality
  RealInducedStandardBound RealStrictCharacterLanglandsQuotient RealLeviSlices RealLeviPairing
  RealLeviDuality RealLeviDensity PartialJacquet

attribute [local instance] measurableSpaceK

/-! ## Matrix coefficients of annihilators -/

section Annihilator

variable {N : ℕ} {ds : List RealBlock}

/-- **Matrix coefficients of annihilators vanish.** If `u` in the `O(N)`-finite dual principal
series annihilates a `(𝔤, K)`-submodule `W` of the standard module, then
`∫_{O(N)} u(κ g) w(κ) dκ = 0` for all `w ∈ W` and `g ∈ GL_N(ℝ)`. -/
theorem integral_mul_eq_zero_of_annihilates {W : Submodule ℂ (StdSpace N ds)}
    (hW : IsGKSubmodule (realStandardRep N ds) (realStandardLie N ds) W)
    {u : Langlands.GeneralLinear N ℝ → ℂ} (hu : u ∈ DualSpace N ds)
    (hann : ∀ w ∈ W, ∫ κ : unitaryCompact ℝ N,
      u κ * (w : Langlands.GeneralLinear N ℝ → ℂ) κ ∂haarK N = 0)
    {w : StdSpace N ds} (hw : w ∈ W) (g : Langlands.GeneralLinear N ℝ) :
    ∫ κ : unitaryCompact ℝ N, u ((κ : Langlands.GeneralLinear N ℝ) * g) *
      (w : Langlands.GeneralLinear N ℝ → ℂ) κ ∂haarK N = 0 := by
  set U : Submodule ℂ (Langlands.GeneralLinear N ℝ → ℂ) :=
    (annW W).map (DualSpace N ds).subtype with hUdef
  have hU : U ≤ kFiniteFunctions (principalSeries ℝ N (dualChar (realPositionCharacter ds)))
      (unitaryCompact ℝ N) := by
    rintro _ ⟨v, -, rfl⟩
    exact v.2
  have hUK : ∀ k ∈ unitaryCompact ℝ N, ∀ u' ∈ U,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) k u' ∈ U := by
    rintro k hk _ ⟨v, hv, rfl⟩
    set k' : Matrix.unitaryGroup (Fin N) ℝ := ⟨(k : Matrix (Fin N) (Fin N) ℝ), hk⟩
    refine ⟨_, annW_rep hW.1 k' hv, ?_⟩
    have hku : (Unitary.toUnits k' : Langlands.GeneralLinear N ℝ) = k := Units.ext rfl
    rw [Submodule.subtype_apply, principalSeriesRep_apply_coe, hku]
    rfl
  have hUD : ∀ (X : Matrix (Fin N) (Fin N) ℝ), ∀ u' ∈ U,
      rightDerivative (matrixModel ℝ N) X u' ∈ U := by
    rintro X _ ⟨v, hv, rfl⟩
    refine ⟨_, annW_lie hW.2 ((1 : ℂ) ⊗ₜ X) hv, ?_⟩
    rw [Submodule.subtype_apply, coe_principalSeriesLie_tmul, one_smul]
    rfl
  have horth : ∀ u' ∈ U, ∫ k : unitaryCompact ℝ N, u' (k : Langlands.GeneralLinear N ℝ) *
      (w : Langlands.GeneralLinear N ℝ → ℂ) k ∂haarK N = 0 := by
    rintro _ ⟨v, hv, rfl⟩
    exact mem_annW.mp hv w hw
  have huU : u ∈ U := ⟨⟨u, hu⟩, mem_annW.mpr hann, rfl⟩
  exact JacquetDual.integral_mul_eq_zero_of_orthogonal (isSignedPower ds) hU hUK hUD
    (continuous_of_mem_stdSpace w.2) horth u huU g

end Annihilator

/-! ## The largest proper submodule -/

section Assembly

variable {c : ℕ} {dss : Fin c → List RealBlock}

/-- The pairing `Θ(u, ·)` with a fixed `u` as a linear functional on the `O(N)`-finite standard
module. -/
def thetaL (hT1 : RealLeviChartIntegrableStatement) (hA : Admissible (sz dss) (flat dss))
    {u : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ}
    (hu : u ∈ DualSpace (∑ j, sz dss j) (flat dss)) :
    StdSpace (∑ j, sz dss j) (flat dss) →ₗ[ℂ] ℂ where
  toFun h := theta (slots (flat dss) (∑ j, sz dss j)) u h
  map_add' h₁ h₂ := theta_add hT1 hA hu h₁.2 h₂.2
  map_smul' a _ := theta_smul a

theorem thetaL_apply (hT1 : RealLeviChartIntegrableStatement)
    (hA : Admissible (sz dss) (flat dss)) {u : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ}
    (hu : u ∈ DualSpace (∑ j, sz dss j) (flat dss)) (h : StdSpace (∑ j, sz dss j) (flat dss)) :
    thetaL hT1 hA hu h = theta (slots (flat dss) (∑ j, sz dss j)) u h := rfl

/-- The `O(N)`-finite standard module is nonzero. -/
theorem bot_ne_top {N : ℕ} {ds : List RealBlock} (hN : realRank ds = N) :
    (⊥ : Submodule ℂ (StdSpace N ds)) ≠ ⊤ := by
  obtain ⟨x, hx, hx1⟩ := RealLeviWitness.exists_std_ne_zero hN
  intro h
  have hmem : (⟨x, hx⟩ : StdSpace N ds) ∈ (⊥ : Submodule ℂ (StdSpace N ds)) := by
    rw [h]
    exact Submodule.mem_top
  rw [Submodule.mem_bot] at hmem
  apply hx1
  have := congrArg (fun v : StdSpace N ds => (v : Langlands.GeneralLinear N ℝ → ℂ) 1) hmem
  simpa using this

/-- The sum of a family of `(𝔤, K)`-submodules is a `(𝔤, K)`-submodule. -/
theorem isGKSubmodule_iSup {N : ℕ} {ds : List RealBlock} {ι : Type*}
    (W : ι → Submodule ℂ (StdSpace N ds))
    (hW : ∀ i, IsGKSubmodule (realStandardRep N ds) (realStandardLie N ds) (W i)) :
    IsGKSubmodule (realStandardRep N ds) (realStandardLie N ds) (⨆ i, W i) := by
  refine ⟨fun k w hw => ?_, fun X w hw => ?_⟩
  · refine Submodule.iSup_induction W (motive := fun w => realStandardRep N ds k w ∈ ⨆ i, W i)
      hw (fun i w hw => Submodule.mem_iSup_of_mem i ((hW i).1 k w hw)) ?_ ?_
    · rw [map_zero]
      exact zero_mem _
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy
  · refine Submodule.iSup_induction W (motive := fun w => realStandardLie N ds X w ∈ ⨆ i, W i)
      hw (fun i w hw => Submodule.mem_iSup_of_mem i ((hW i).2 X w hw)) ?_ ?_
    · rw [map_zero]
      exact zero_mem _
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy

/-- **The largest proper submodule along the tie classes.** Under the hypotheses of the limit
argument along `Q` and the irreducibility of the class standard modules, the sum of all proper
`(𝔤, K)`-submodules of the `O(N)`-finite standard module of `flat dss` is proper. -/
theorem exists_largest (hT1 : RealLeviChartIntegrableStatement)
    (hT3 : RealLeviParabolicIntegrationStatement)
    (hanti : ∀ p q : Fin (∑ i, sz dss i), p ≤ q →
      realPositionBlockExponent (flat dss) q ≤ realPositionBlockExponent (flat dss) p)
    (hstrict : ∀ p q : Fin (∑ i, sz dss i), cls (sz dss) p < cls (sz dss) q →
      realPositionBlockExponent (flat dss) q < realPositionBlockExponent (flat dss) p)
    (hX : ∀ i, IsIrreducibleGKModule (realStandardRep (sz dss i) (cl dss i))
      (realStandardLie (sz dss i) (cl dss i))) :
    ∃ R : Submodule ℂ (StdSpace (∑ j, sz dss j) (flat dss)),
      IsGKSubmodule (realStandardRep (∑ j, sz dss j) (flat dss))
        (realStandardLie (∑ j, sz dss j) (flat dss)) R ∧ R ≠ ⊤ ∧
        ∀ W : Submodule ℂ (StdSpace (∑ j, sz dss j) (flat dss)),
          IsGKSubmodule (realStandardRep (∑ j, sz dss j) (flat dss))
            (realStandardLie (∑ j, sz dss j) (flat dss)) W → W ≠ ⊤ → W ≤ R := by
  have hN : realRank (flat dss) = ∑ j, sz dss j := realRank_flat dss
  have hA : Admissible (sz dss) (flat dss) := ⟨hN, hanti, hstrict⟩
  obtain ⟨φ, hφ, h0, hh0, hθ⟩ := realLeviWitness hT1 c dss hanti hstrict hX
  -- a vector with the product coefficients
  obtain ⟨u0, hu0, -, hprod0⟩ := realLeviDensity c dss hX φ hφ ⊥
    (fun _ w hw => by
      rw [Submodule.mem_bot] at hw ⊢
      rw [hw, map_zero])
    (fun _ w hw => by
      rw [Submodule.mem_bot] at hw ⊢
      rw [hw, map_zero]) (bot_ne_top hN)
  -- every proper `(𝔤, K)`-submodule lies in the kernel of `Θ(u₀, ·)`
  have hker : ∀ W : Submodule ℂ (StdSpace (∑ j, sz dss j) (flat dss)),
      IsGKSubmodule (realStandardRep (∑ j, sz dss j) (flat dss))
        (realStandardLie (∑ j, sz dss j) (flat dss)) W → W ≠ ⊤ →
        W ≤ LinearMap.ker (thetaL hT1 hA hu0) := by
    intro W hW hW' w hw
    obtain ⟨uW, huW, hann, hprodW⟩ := realLeviDensity c dss hX φ hφ W hW.1 hW.2 hW'
    have hlim := realLeviLimit hT1 hT3 c (sz dss) (flat dss) hN hanti hstrict uW huW w w.2
      (integral_mul_eq_zero_of_annihilates hW huW hann hw)
    rw [LinearMap.mem_ker, thetaL_apply,
      theta_congr hu0 huW w.2 (RealLeviWitness.coeffs_eq_of_prodCoeffs hprod0 hprodW)]
    exact hlim
  set S := {W : Submodule ℂ (StdSpace (∑ j, sz dss j) (flat dss)) //
    IsGKSubmodule (realStandardRep (∑ j, sz dss j) (flat dss))
      (realStandardLie (∑ j, sz dss j) (flat dss)) W ∧ W ≠ ⊤}
  refine ⟨⨆ W : S, W.1, isGKSubmodule_iSup _ fun W => W.2.1, ?_,
    fun W hW hW' => le_iSup (fun W : S => W.1) ⟨W, hW, hW'⟩⟩
  intro htop
  have hle : (⨆ W : S, W.1) ≤ LinearMap.ker (thetaL hT1 hA hu0) :=
    iSup_le fun W => hker W.1 W.2.1 W.2.2
  have hmem : (⟨h0, hh0⟩ : StdSpace (∑ j, sz dss j) (flat dss)) ∈ ⨆ W : S, W.1 := by
    rw [htop]
    exact Submodule.mem_top
  have h1 := hle hmem
  rw [LinearMap.mem_ker, thetaL_apply] at h1
  exact hθ u0 hu0 hprod0 h1

end Assembly

end RealLeviLanglandsQuotient

/-- **Statement (the Langlands quotient, conditionally).** Assume
`RealLeviChartIntegrableStatement`, `RealLeviParabolicIntegrationStatement` and
`RealTemperedStandardIrreducibleStatement`. Then `RealStandardLanglandsQuotientStatement`
holds: for every list `ds` of real blocks of total rank `n` in Langlands order, the
`O(n)`-finite functions of the standard module of `ds` have a largest proper
`(𝔤, K)`-submodule. -/
def RealLeviLanglandsQuotientStatement : Prop :=
  RealLeviChartIntegrableStatement → RealLeviParabolicIntegrationStatement →
    RealTemperedStandardIrreducibleStatement → RealStandardLanglandsQuotientStatement

theorem realLeviLanglandsQuotient : RealLeviLanglandsQuotientStatement := by
  intro hT1 hT3 htemp n ds hn hord
  obtain ⟨c, dss, hflat, hanti, hstrict, hX⟩ := RealTieClasses.exists_tieData htemp ds hord
  subst hflat
  obtain rfl : n = ∑ j, RealLeviSlices.sz dss j :=
    hn.symm.trans (RealLeviSlices.realRank_flat dss)
  exact RealLeviLanglandsQuotient.exists_largest hT1 hT3 hanti hstrict hX

end Langlands.Archimedean
