import Langlands.Global.Factors.MeromorphicPoleComparisonStatement

/-!
# Conditional Appendix pole counting for a finite family of shifted factors

The functions are actual complex functions. The supercuspidal base-factor
properties, the epsilon unit, and the arithmetic gamma-zero restriction are
explicit inputs.
-/

noncomputable section

namespace Langlands.Global.PoleComparison

universe u

/-- Half the segment length plus the real unramified exponent. -/
def blockHeight {I : Type u} (length : I → ℕ) (exponent : I → ℝ) (i : I) : ℝ :=
  (length i : ℝ) / 2 + exponent i

/-- The shift in the unitary square-integrable pair-factor formula. -/
def blockShift {I : Type u} (length : I → ℕ) (exponent : I → ℝ)
    (i j : I) (k : ℕ) : ℝ :=
  ((length i : ℝ) + (length j : ℝ)) / 2 - (k : ℝ) + exponent i - exponent j

/-- The actual finite product in the Appendix pair-factor formula.
The integer `length i` is one less than the segment's number of terms. -/
def blockLFactor {I : Type u} [Fintype I] (length : I → ℕ) (exponent : I → ℝ)
    (base : I → I → ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∏ i, ∏ j, ∏ k ∈ Finset.range (min (length i) (length j) + 1),
    base i j (z + (blockShift length exponent i j k : ℂ))

/-- The epsilon times reflected-L over L expression for the self-pair. -/
def blockGamma {I : Type u} [Fintype I] (length : I → ℕ) (exponent : I → ℝ)
    (base : I → I → ℂ → ℂ) (epsilon : ℂ → ℂ) : ℂ → ℂ :=
  fun z => epsilon z * blockLFactor length exponent base (1 - z) /
    blockLFactor length exponent base z

/-- The finite Hermitian symmetry and open unitary exponent interval. -/
def SymmetricBlockData {I : Type u} (length : I → ℕ) (exponent : I → ℝ)
    (partner : I → I) : Prop :=
  Function.Involutive partner ∧
  (∀ i, length (partner i) = length i) ∧
  (∀ i, exponent (partner i) = -exponent i) ∧
  (∀ i, -(1 / 2 : ℝ) < exponent i ∧ exponent i < 1 / 2)

/-- The analytic base-pair inputs. All real orders are finite and nonpositive,
positive real points are holomorphic nonzero, and a matched partner supplies
a genuine pole at zero. -/
def BasePairConditions {I : Type u} (partner : I → I)
    (base : I → I → ℂ → ℂ) : Prop :=
  (∀ i j (t : ℝ),
    MeromorphicAt (base i j) (t : ℂ) ∧
    meromorphicOrderAt (base i j) (t : ℂ) ≤ 0) ∧
  (∀ i j (t : ℝ), 0 < t → HolomorphicUnitAt (base i j) (t : ℂ)) ∧
  (∀ i, meromorphicOrderAt (base i (partner i)) 0 < 0)

/-- The elementary bounds on all shifts and an attained maximal shift.
The maximum height is supplied explicitly in this auxiliary statement. -/
def SymmetricBlockShiftStatement (I : Type u) : Prop :=
  ∀ (length : I → ℕ) (exponent : I → ℝ) (partner : I → I) (h : ℝ),
    SymmetricBlockData length exponent partner →
    (∃ i, blockHeight length exponent i = h) →
    (∀ i, blockHeight length exponent i ≤ h) →
    0 ≤ h ∧
    (∀ i j k, k ≤ min (length i) (length j) →
      -1 < blockShift length exponent i j k ∧
      blockShift length exponent i j k ≤ 2 * h) ∧
    ∃ i, blockShift length exponent i (partner i) 0 = 2 * h

/-- At minus twice the maximum height, the L-product has a genuine pole,
the reflected product is a holomorphic unit, and gamma has a genuine zero.
No cancellation is inferred without the base-factor and epsilon hypotheses. -/
def AppendixExtremePoleStatement (I : Type u) [Fintype I] : Prop :=
  ∀ (length : I → ℕ) (exponent : I → ℝ) (partner : I → I)
    (base : I → I → ℂ → ℂ) (epsilon : ℂ → ℂ) (h : ℝ),
    SymmetricBlockData length exponent partner →
    BasePairConditions partner base →
    (∀ t : ℝ, HolomorphicUnitAt epsilon (t : ℂ)) →
    (∃ i, blockHeight length exponent i = h) →
    (∀ i, blockHeight length exponent i ≤ h) →
    meromorphicOrderAt (blockLFactor length exponent base) ((-2 * h : ℝ) : ℂ) < 0 ∧
    HolomorphicUnitAt (fun z => blockLFactor length exponent base (1 - z))
      ((-2 * h : ℝ) : ℂ) ∧
    0 < meromorphicOrderAt (blockGamma length exponent base epsilon)
      ((-2 * h : ℝ) : ℂ)

/-- If the self-pair gamma expression can have a real zero only at zero,
all segments have length parameter zero and all exponents vanish. -/
def AppendixBlockRigidityStatement (I : Type u) [Fintype I] [Nonempty I] : Prop :=
  ∀ (length : I → ℕ) (exponent : I → ℝ) (partner : I → I)
    (base : I → I → ℂ → ℂ) (epsilon : ℂ → ℂ),
    SymmetricBlockData length exponent partner →
    BasePairConditions partner base →
    (∀ t : ℝ, HolomorphicUnitAt epsilon (t : ℂ)) →
    (∀ t : ℝ,
      0 < meromorphicOrderAt (blockGamma length exponent base epsilon) (t : ℂ) →
      t = 0) →
    ∀ i, length i = 0 ∧ exponent i = 0

/-- The shift bounds, actual-function pole calculation, and Appendix
block-rigidity consequence. No classification theorem is asserted here. -/
def AppendixPoleCountingStatement (I : Type u) [Fintype I] [Nonempty I] : Prop :=
  SymmetricBlockShiftStatement I ∧
  AppendixExtremePoleStatement I ∧
  AppendixBlockRigidityStatement I

end Langlands.Global.PoleComparison
