import Langlands.Global.AdelicSpaceLevelTopologyProof
import Langlands.Shimura.Unitary.HarrisSplitPrimeFactorLevels
import Langlands.Shimura.Unitary.LocalDivisionLevels
import Langlands.Global.IntegralFiniteAdeles

/-!
# Harris's level `K(N)_p` at a split prime

At the places `w` of the CM field above the chosen place `𝔭` of the imaginary quadratic field,
assume `K_w ⊗[K] A` is a division algebra. Harris's level
`K(N)_p = C_v^{N,0} × ∏_{j>1} C^(j) × ℤ_pˣ` takes the principal congruence subgroup
`1 + ϖ^N O` at the distinguished place and the maximal compact subgroup `Oˣ` at the others.
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

set_option autoImplicit false

universe u v w z

namespace Langlands.Shimura

open Global AdelicFunctoriality

section Completion

variable {K : Type v} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

/-- The nontrivially normed field structure of the completion `K_w` given by its valuation. -/
abbrev completionNormedField : NontriviallyNormedField (w.adicCompletion K) :=
  Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))

end Completion

section Local

variable {K : Type v} [Field K] [NumberField K] {A : Type z} [Ring A] [Algebra K A]
  [Module.Finite K A] (w : HeightOneSpectrum (𝓞 K))

variable (A) in
/-- `K_w ⊗[K] A` is a division algebra: it is nontrivial and every nonzero element is a
unit. -/
def IsDivisionAt : Prop :=
  Nontrivial (w.adicCompletion K ⊗[K] A) ∧ ∀ x : w.adicCompletion K ⊗[K] A, x ≠ 0 → IsUnit x

variable (A) in
/-- The division ring structure of `K_w ⊗[K] A` under `IsDivisionAt`. -/
abbrev placeDivisionRing (h : IsDivisionAt A w) : DivisionRing (w.adicCompletion K ⊗[K] A) :=
  letI : Nontrivial (w.adicCompletion K ⊗[K] A) := h.1
  DivisionRing.ofIsUnitOrEqZero fun x => (em (x = 0)).elim Or.inr fun hx => Or.inl (h.2 x hx)

variable (A) in
/-- The maximal compact subgroup `O_{D_w}ˣ` of `(K_w ⊗[K] A)ˣ`, for `K_w ⊗[K] A` a division
algebra (`LocalDivision.maximalCompactLevel` over the completion with its valuation norm). -/
def placeMaximalCompactLevel (h : IsDivisionAt A w) :
    CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w.adicCompletion K)) :=
  letI := completionNormedField w
  haveI := Global.AdelicSpaceLevelTopologyProof.finiteCompletion_locallyCompactSpace K w
  letI := placeDivisionRing A w h
  letI : TopologicalSpace (w.adicCompletion K ⊗[K] A) := moduleTopology (w.adicCompletion K) _
  LocalDivision.maximalCompactLevel (w.adicCompletion K) (w.adicCompletion K ⊗[K] A)

theorem mem_placeMaximalCompactLevel (h : IsDivisionAt A w)
    (x : (w.adicCompletion K ⊗[K] A)ˣ) :
    x ∈ (placeMaximalCompactLevel A w h).subgroup ↔
      letI := completionNormedField w
      letI := placeDivisionRing A w h
      CentralDivision.regularAbsoluteValue (w.adicCompletion K) (w.adicCompletion K ⊗[K] A)
          (x : w.adicCompletion K ⊗[K] A) ≤ 1 ∧
        CentralDivision.regularAbsoluteValue (w.adicCompletion K) (w.adicCompletion K ⊗[K] A)
          ((x⁻¹ : (w.adicCompletion K ⊗[K] A)ˣ) : w.adicCompletion K ⊗[K] A) ≤ 1 :=
  Iff.rfl

variable (A) in
/-- The congruence subgroup `{x | |x - 1| ≤ r}` of `(K_w ⊗[K] A)ˣ` for `0 < r < 1`, for
`K_w ⊗[K] A` a division algebra (`LocalDivision.congruenceLevel`). For `r = ‖ϖ‖^N` with a
uniformizer `ϖ` of `K_w` and `N ≥ 1` this is `1 + ϖ^N O_{D_w}`. -/
def placeCongruenceLevel (h : IsDivisionAt A w) (r : ℝ) (hr0 : 0 < r) (hr : r < 1) :
    CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w.adicCompletion K)) :=
  letI := completionNormedField w
  haveI := Global.AdelicSpaceLevelTopologyProof.finiteCompletion_locallyCompactSpace K w
  letI := placeDivisionRing A w h
  letI : TopologicalSpace (w.adicCompletion K ⊗[K] A) := moduleTopology (w.adicCompletion K) _
  LocalDivision.congruenceLevel (w.adicCompletion K) (w.adicCompletion K ⊗[K] A) r hr0 hr

theorem mem_placeCongruenceLevel (h : IsDivisionAt A w) (r : ℝ) (hr0 : 0 < r) (hr : r < 1)
    (x : (w.adicCompletion K ⊗[K] A)ˣ) :
    x ∈ (placeCongruenceLevel A w h r hr0 hr).subgroup ↔
      letI := completionNormedField w
      letI := placeDivisionRing A w h
      CentralDivision.regularAbsoluteValue (w.adicCompletion K) (w.adicCompletion K ⊗[K] A)
          ((x : w.adicCompletion K ⊗[K] A) - 1) ≤ r :=
  Iff.rfl

theorem placeCongruenceLevel_le (h : IsDivisionAt A w) (r : ℝ) (hr0 : 0 < r) (hr : r < 1) :
    (placeCongruenceLevel A w h r hr0 hr).subgroup ≤ (placeMaximalCompactLevel A w h).subgroup :=
  letI := completionNormedField w
  haveI := Global.AdelicSpaceLevelTopologyProof.finiteCompletion_locallyCompactSpace K w
  letI := placeDivisionRing A w h
  letI : TopologicalSpace (w.adicCompletion K ⊗[K] A) := moduleTopology (w.adicCompletion K) _
  LocalDivision.congruenceLevel_le_maximalCompactLevel (w.adicCompletion K)
    (w.adicCompletion K ⊗[K] A) r hr0 hr

/-- For `ϖ ≠ 0` in `K_w` with `‖ϖ‖ < 1` and `N ≥ 1`, the congruence level of radius `‖ϖ‖^N`
consists of the units `1 + ϖ^N y` with `y` in the integer ring of `K_w ⊗[K] A`. -/
theorem mem_placeCongruenceLevel_iff_exists (h : IsDivisionAt A w) (ϖ : w.adicCompletion K)
    (hϖ0 : ϖ ≠ 0) (N : ℕ)
    (hr0 : letI := completionNormedField w; 0 < ‖ϖ‖ ^ N)
    (hr : letI := completionNormedField w; ‖ϖ‖ ^ N < 1)
    (x : (w.adicCompletion K ⊗[K] A)ˣ) :
    x ∈ (placeCongruenceLevel A w h _ hr0 hr).subgroup ↔
      letI := completionNormedField w
      letI := placeDivisionRing A w h
      ∃ y ∈ LocalDivision.integerRing (w.adicCompletion K) (w.adicCompletion K ⊗[K] A),
        (x : w.adicCompletion K ⊗[K] A) = 1 + ϖ ^ N • y :=
  letI := completionNormedField w
  letI := placeDivisionRing A w h
  LocalDivision.mem_congruenceSubgroup_iff_exists (w.adicCompletion K)
    (w.adicCompletion K ⊗[K] A) ϖ hϖ0 N hr x

end Local

section Harris

variable {E : Type u} {K : Type v}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]
variable {F : Type w} [Field F] [NumberField F] [IsCMField F]
variable {A : Type z} [Ring A] [Algebra K A] [Algebra ℚ A] [IsScalarTower ℚ K A]
  [Module.Finite ℚ A]

variable (ι : F →+* K) (v : Global.FinitePlace ℚ) (𝔭 : FinitePlacesAbove F v)
  (h𝔭 : Function.Bijective (FiniteExtension.completionMap v 𝔭.1))

include A in
omit [IsTotallyComplex K] [IsCMField F] in
theorem moduleFinite_of_rat : Module.Finite K A :=
  Module.Finite.of_restrictScalars_finite ℚ K A

variable (A) in
open Classical in
/-- Harris's local levels at the places `w` of `K` above `𝔭`: the congruence level of radius
`r` at the distinguished place `w₀` and the maximal compact level `O_{D_w}ˣ` elsewhere. -/
def harrisLocalLevels
    (hdiv : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1), IsDivisionAt A w.1)
    (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) (r : ℝ) (hr0 : 0 < r) (hr : r < 1)
    (w : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) :
    CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w.1.adicCompletion K)) :=
  haveI := moduleFinite_of_rat (K := K) (A := A)
  if w = w₀ then placeCongruenceLevel A w.1 (hdiv w) r hr0 hr
  else placeMaximalCompactLevel A w.1 (hdiv w)

variable [Algebra E A] [IsScalarTower E K A] [IsScalarTower ℚ E A]
variable [Algebra.IsQuadraticExtension ℚ F]

/-- Harris's level `K(N)_p = C_v^{N,0} × ∏_{j>1} C^(j) × ℤ_pˣ` (Harris 1997, p. 89; 1998,
(A.2); 1999, Section 4), with the congruence radius `r` (for `r = ‖ϖ‖^N`, `C_v^{N,0}`). -/
def SecondKindInvolution.harrisLevel (σ : SecondKindInvolution E K A)
    (hdiv : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1), IsDivisionAt A w.1)
    (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) (r : ℝ) (hr0 : 0 < r) (hr : r < 1) :
    CompactOpenLevel (σ.rationalInvolution.Points (FiniteCompletion ℚ v)) :=
  σ.splitPlaceLevel ι v 𝔭 h𝔭 (harrisLocalLevels A ι v 𝔭 hdiv w₀ r hr0 hr)

omit [IsScalarTower E K A] in
/-- A point of `GG(ℚ_v)` lies in `K(N)_p` exactly when its component at `w₀` lies in the
congruence level, its components at the other places lie in the maximal compact levels, and its
multiplier lies in `ℤ_vˣ`. -/
theorem SecondKindInvolution.mem_harrisLevel (σ : SecondKindInvolution E K A)
    (hdiv : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1), IsDivisionAt A w.1)
    (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) (r : ℝ) (hr0 : 0 < r) (hr : r < 1)
    (g : σ.rationalInvolution.Points (FiniteCompletion ℚ v)) :
    haveI := moduleFinite_of_rat (K := K) (A := A)
    g ∈ (σ.harrisLevel ι v 𝔭 h𝔭 hdiv w₀ r hr0 hr).subgroup ↔
      (σ.splitPlacePoints ι v 𝔭 h𝔭 g).1 w₀ ∈
          (placeCongruenceLevel A w₀.1 (hdiv w₀) r hr0 hr).subgroup ∧
        (∀ w, w ≠ w₀ → (σ.splitPlacePoints ι v 𝔭 h𝔭 g).1 w ∈
          (placeMaximalCompactLevel A w.1 (hdiv w)).subgroup) ∧
        AlgebraInvolution.Points.multiplier σ.rationalInvolution _ g ∈
          (integerUnitsLevel v).subgroup := by
  classical
  rw [SecondKindInvolution.harrisLevel, SecondKindInvolution.mem_splitPlaceLevel]
  constructor
  · rintro ⟨hC, hm⟩
    refine ⟨?_, fun w hw => ?_, hm⟩
    · simpa [harrisLocalLevels] using hC w₀
    · simpa [harrisLocalLevels, hw] using hC w
  · rintro ⟨h0, hrest, hm⟩
    refine ⟨fun w => ?_, hm⟩
    by_cases hw : w = w₀
    · subst hw
      simpa [harrisLocalLevels] using h0
    · simpa [harrisLocalLevels, hw] using hrest w hw

end Harris

end Langlands.Shimura
