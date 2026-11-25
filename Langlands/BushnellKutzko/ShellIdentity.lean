import Langlands.BushnellKutzko.StratumZetaIntegral
import Langlands.Representation.GodementJacquet.CompactMatrixLaurent
import Langlands.Representation.RankinSelberg.HighlyRamified.ShellExpansion

/-! # The shell identity from a monomial functional equation

Let `K` be a `p`-adic field with residue cardinality `q`, and let `σ` be a representation of
`GL_{n+1}(K)` with Godement–Jacquet functional-equation data with both Euler polynomials `1`,
unit `c` and exponent `a` (`GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData K ψ ν σ
1 1 c a`). Every irreducible supercuspidal representation of rank at least two has such data
(Library theorem `GodementJacquet.Padic.exists_supercuspidalMatrixFunctionalEquationData`).

Let `Φ` be a matrix test function and `f` a bi-smooth coefficient of `σ` whose shifted zeta
integral is the constant `r`. If the Fourier transform `Φ̂` of `Φ` is supported on matrices with
`ord(det g) ≥ j₀`, the functional equation says that the zeta integral of `Φ̂` against
`f^ι(g) = f(g^{-T})` is the monomial `c r q^{-a} X^{-a}` in `X = q^{-s}`. Expanding this integral
over the shells `ord(det g) = j` (Library `RankinSelberg.HighlyRamified.shell_integral_eq_of_const`)
gives the **shell identity**

`∫_{ord(det g) = -a} Φ̂(g) f(g^{-T}) dg = c r (q^{-1} q^{-n/2})^a`

(`setIntegral_ord_det_eq_of_functionalEquation`). When `r ≠ 0` the integrand cannot vanish on
the shell (`exists_ord_det_eq_of_functionalEquation`).

This belongs to the analytic part of the proof of T2 (see `ConductorFormula`).
-/

noncomputable section

open MeasureTheory Topology Langlands.HarmonicAnalysis ValuativeRel
open Langlands.RankinSelberg (spectralPoint)

namespace Langlands.BushnellKutzko

universe uK uV

/-- `q^{-t} q^{-(1-t)} = q^{-1}`. -/
theorem spectralPoint_mul_spectralPoint_one_sub {q : ℕ} (hq : 0 < q) (t : ℂ) :
    spectralPoint q t * spectralPoint q (1 - t) = spectralPoint q 1 := by
  unfold RankinSelberg.spectralPoint
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← Complex.cpow_add _ _ hq0]
  congr 1
  ring

section Padic

local instance shTopologicalSpace {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance shValuativeRel {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance shLocalField {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance shT2 {p : ℕ} [Fact p.Prime] (F : PadicField p) : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2

local instance shMeasurable {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    MeasurableSpace F.Carrier :=
  borel _

local instance shBorel {p : ℕ} [Fact p.Prime] (F : PadicField p) : BorelSpace F.Carrier :=
  ⟨rfl⟩

local instance shGLMeasurable {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) :=
  borel _

local instance shGLBorel {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) :=
  ⟨rfl⟩

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The order of the determinant is a continuous (locally constant) function on `GL_{n+1}(K)`. -/
theorem continuous_ord_det :
    Continuous fun g : GeneralLinear (n + 1) K.Carrier =>
      K.canonicalTopologicalData.ord (Matrix.det g.val) :=
  (RankinSelberg.continuous_ord_units K.canonicalTopologicalData).comp
    (K.canonicalTopologicalData.generalLinearDeterminant (n + 1)).continuous

/-- The determinant shells `{g | ord(det g) = j}` are measurable. -/
theorem measurableSet_ord_det_eq (j : ℤ) :
    MeasurableSet {g : GeneralLinear (n + 1) K.Carrier |
      K.canonicalTopologicalData.ord (Matrix.det g.val) = j} :=
  ((isClosed_discrete ({j} : Set ℤ)).preimage (continuous_ord_det K)).measurableSet

/-- **The shell identity**. Assume functional-equation data for `σ` with both Euler
polynomials `1`, unit `c` and exponent `a`. Let `Φ` be a matrix test function whose Fourier
transform vanishes at every `g ∈ GL_{n+1}(K)` with `ord(det g) < j₀`, and let `f` be a bi-smooth
coefficient of `σ` whose shifted zeta integral against `Φ` has the constant rational value `r`.
Then the integral of `Φ̂(g) f(g^{-T})` over the shell `ord(det g) = -a` is
`c r (q^{-1} q^{-n/2})^a`. -/
theorem setIntegral_ord_det_eq_of_functionalEquation
    (ψ : UnitaryAdditiveCharacter K.Carrier) (ν : AdditiveHaarMeasure K.Carrier)
    (σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V) (c : ℂˣ) (a : ℤ)
    (hFE : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData K ψ ν σ 1 1 c a)
    (Φ : GodementJacquet.MatrixTestFunction n K.Carrier) (j₀ : ℤ)
    (hsupp : ∀ g : GeneralLinear (n + 1) K.Carrier,
      rectangularFourierIntegral ψ ν Φ g.val ≠ 0 →
        j₀ ≤ K.canonicalTopologicalData.ord (Matrix.det g.val))
    (f : GodementJacquet.biSmoothMatrixCoefficients σ) (r : ℂ)
    (hR : GodementJacquet.HasShiftedRationalValue K.canonicalTopologicalData.residueCardinality
      (RankinSelberg.normalizedAbsoluteValue K.canonicalTopologicalData)
      (RankinSelberg.generalLinearHaar K.Carrier n) Φ f.val (RatFunc.C r)) :
    ∫ g in {g : GeneralLinear (n + 1) K.Carrier |
        K.canonicalTopologicalData.ord (Matrix.det g.val) = -a},
        rectangularFourierIntegral ψ ν Φ g.val * GodementJacquet.coefficientIota f.val g
          ∂(RankinSelberg.generalLinearHaar K.Carrier n) =
      (c : ℂ) * r * (spectralPoint K.canonicalTopologicalData.residueCardinality 1 *
        spectralPoint K.canonicalTopologicalData.residueCardinality
          (GodementJacquet.jpssShift n)) ^ a := by
  classical
  set T := K.canonicalTopologicalData with hT
  set q := T.residueCardinality with hq_def
  set μ := RankinSelberg.generalLinearHaar K.Carrier n with hμ
  set abv := RankinSelberg.normalizedAbsoluteValue T with habv
  have hq : 1 < q := T.residueCardinality_gt_one
  have hq0 : 0 < q := by omega
  obtain ⟨ΦHat, hpair, hfe⟩ := hFE.2.2 Φ
  have hHat : ∀ x, ΦHat x = rectangularFourierIntegral ψ ν Φ x := fun x => (hpair x).2
  obtain ⟨RDual, hRD⟩ := hFE.2.1.2.1 ΦHat f
  have hN := hfe f (RatFunc.C r) RDual hR hRD
  obtain ⟨⟨a₂, hconv⟩, ⟨a₁, hcont⟩⟩ := hRD
  let ord : GeneralLinear (n + 1) K.Carrier → ℤ := fun g => T.ord (Matrix.det g.val)
  let Ψ : GeneralLinear (n + 1) K.Carrier → ℂ := fun g =>
    ΦHat g.val * GodementJacquet.coefficientIota f.val g *
      RankinSelberg.determinantWeight abv g (GodementJacquet.jpssShift n)
  let D : GeneralLinear (n + 1) K.Carrier → ℤ := fun g => ord g + a
  have hInt : ∀ (t : ℂ) (g : GeneralLinear (n + 1) K.Carrier),
      GodementJacquet.matrixIntegrand abv ΦHat (t + GodementJacquet.jpssShift n)
        (GodementJacquet.coefficientIota f.val) g = Ψ g * spectralPoint q t ^ ord g := by
    intro t g
    simp only [GodementJacquet.matrixIntegrand, Ψ, ord, abv]
    rw [GodementJacquet.Padic.determinantWeight_shift_spectral K g t]
    ring
  have hIntD : ∀ (t : ℂ) (g : GeneralLinear (n + 1) K.Carrier),
      Ψ g * spectralPoint q t ^ D g =
        GodementJacquet.matrixIntegrand abv ΦHat (t + GodementJacquet.jpssShift n)
          (GodementJacquet.coefficientIota f.val) g * spectralPoint q t ^ a := by
    intro t g
    rw [hInt, zpow_add₀ (RankinSelberg.spectralPoint_ne_zero_of_pos hq0 t)]
    ring
  -- the value of the shifted integral on a right half-plane
  have hval : ∀ t : ℂ, a₁ < t.re →
      ∫ g, Ψ g * spectralPoint q t ^ D g ∂μ = (c : ℂ) * r * spectralPoint q 1 ^ a := by
    intro t ht
    obtain ⟨hden, heq⟩ := hcont t ht
    have heq' : GodementJacquet.matrixIntegral abv μ ΦHat (t + GodementJacquet.jpssShift n)
        (GodementJacquet.coefficientIota f.val) =
          RatFunc.eval (RingHom.id ℂ) (spectralPoint q t) RDual := heq
    have hFEt := hN (1 - t) (by rw [RatFunc.denom_C, Polynomial.eval_one]; exact one_ne_zero)
      (by rw [sub_sub_cancel]; exact hden)
    simp only [sub_sub_cancel, Polynomial.eval_one, one_mul, pow_zero, Units.val_one,
      RatFunc.eval_C, RingHom.id_apply] at hFEt
    simp_rw [hIntD]
    rw [integral_mul_const]
    change GodementJacquet.matrixIntegral abv μ ΦHat (t + GodementJacquet.jpssShift n)
        (GodementJacquet.coefficientIota f.val) * spectralPoint q t ^ a = _
    rw [heq', hFEt, RankinSelberg.epsilonMonomial,
      ← spectralPoint_mul_spectralPoint_one_sub hq0 t, mul_zpow]
    ring
  -- integrability at one real point
  set s₀ : ℝ := max a₂ a₁ + 1 with hs₀
  have hs₀' : a₂ < ((s₀ : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re, hs₀]
    linarith [le_max_left a₂ a₁]
  have hint : Integrable (fun g => Ψ g * spectralPoint q (s₀ : ℂ) ^ D g) μ := by
    simp_rw [hIntD]
    exact (hconv (s₀ : ℂ) hs₀').mul_const _
  -- measurable fibres and the support bound
  have hD : ∀ j : ℤ, MeasurableSet {g | D g = j} := by
    intro j
    have h : {g | D g = j} = {g : GeneralLinear (n + 1) K.Carrier |
        T.ord (Matrix.det g.val) = j - a} := by
      ext g
      simp only [Set.mem_ofPred_eq, D, ord]
      omega
    rw [h]
    exact measurableSet_ord_det_eq K (j - a)
  have hsupp' : ∀ g, Ψ g ≠ 0 → j₀ + a ≤ D g := by
    intro g hg
    have h1 : ΦHat g.val ≠ 0 := fun h => hg (by simp only [Ψ, h, zero_mul])
    rw [hHat] at h1
    have h2 := hsupp g h1
    simp only [D, ord]
    omega
  have hshell := RankinSelberg.HighlyRamified.shell_integral_eq_of_const μ D hq hD Ψ (j₀ + a)
    hsupp' s₀ hint ((c : ℂ) * r * spectralPoint q 1 ^ a) a₁ hval 0
  simp only [↓reduceIte] at hshell
  -- identify the shell and the weight on it
  have hset : {g | D g = 0} = {g : GeneralLinear (n + 1) K.Carrier |
      T.ord (Matrix.det g.val) = -a} := by
    ext g
    simp only [Set.mem_ofPred_eq, D, ord]
    omega
  have hXne : spectralPoint q (GodementJacquet.jpssShift n) ≠ 0 :=
    RankinSelberg.spectralPoint_ne_zero_of_pos hq0 _
  have hcongr : ∫ g in {g : GeneralLinear (n + 1) K.Carrier | T.ord (Matrix.det g.val) = -a},
      Ψ g ∂μ = (∫ g in {g : GeneralLinear (n + 1) K.Carrier | T.ord (Matrix.det g.val) = -a},
        rectangularFourierIntegral ψ ν Φ g.val * GodementJacquet.coefficientIota f.val g ∂μ) *
          spectralPoint q (GodementJacquet.jpssShift n) ^ (-a) := by
    rw [← integral_mul_const]
    refine setIntegral_congr_fun (measurableSet_ord_det_eq K (-a)) fun g hg => ?_
    have hg' : T.ord (Matrix.det g.val) = -a := hg
    simp only [Ψ, abv]
    rw [RankinSelberg.normalizedDeterminantWeight_eq_spectralPoint_zpow T g, hg', hHat]
  rw [hset, hcongr] at hshell
  set I := ∫ g in {g : GeneralLinear (n + 1) K.Carrier | T.ord (Matrix.det g.val) = -a},
    rectangularFourierIntegral ψ ν Φ g.val * GodementJacquet.coefficientIota f.val g ∂μ
  calc I = I * spectralPoint q (GodementJacquet.jpssShift n) ^ (-a) *
        spectralPoint q (GodementJacquet.jpssShift n) ^ a := by
          rw [mul_assoc, ← zpow_add₀ hXne, neg_add_cancel, zpow_zero, mul_one]
    _ = (c : ℂ) * r * spectralPoint q 1 ^ a *
        spectralPoint q (GodementJacquet.jpssShift n) ^ a := by rw [hshell]
    _ = _ := by rw [mul_zpow]; ring

/-- **Nonvanishing on the shell.** Under the hypotheses of
`setIntegral_ord_det_eq_of_functionalEquation`, if `r ≠ 0` then some `g` with
`ord(det g) = -a` has `Φ̂(g) ≠ 0` and `f(g^{-T}) ≠ 0`. -/
theorem exists_ord_det_eq_of_functionalEquation
    (ψ : UnitaryAdditiveCharacter K.Carrier) (ν : AdditiveHaarMeasure K.Carrier)
    (σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V) (c : ℂˣ) (a : ℤ)
    (hFE : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData K ψ ν σ 1 1 c a)
    (Φ : GodementJacquet.MatrixTestFunction n K.Carrier) (j₀ : ℤ)
    (hsupp : ∀ g : GeneralLinear (n + 1) K.Carrier,
      rectangularFourierIntegral ψ ν Φ g.val ≠ 0 →
        j₀ ≤ K.canonicalTopologicalData.ord (Matrix.det g.val))
    (f : GodementJacquet.biSmoothMatrixCoefficients σ) (r : ℂ)
    (hR : GodementJacquet.HasShiftedRationalValue K.canonicalTopologicalData.residueCardinality
      (RankinSelberg.normalizedAbsoluteValue K.canonicalTopologicalData)
      (RankinSelberg.generalLinearHaar K.Carrier n) Φ f.val (RatFunc.C r)) (hr : r ≠ 0) :
    ∃ g : GeneralLinear (n + 1) K.Carrier,
      K.canonicalTopologicalData.ord (Matrix.det g.val) = -a ∧
        rectangularFourierIntegral ψ ν Φ g.val ≠ 0 ∧
          GodementJacquet.coefficientIota f.val g ≠ 0 := by
  have hq0 : 0 < K.canonicalTopologicalData.residueCardinality :=
    Nat.zero_lt_one.trans K.canonicalTopologicalData.residueCardinality_gt_one
  have h := setIntegral_ord_det_eq_of_functionalEquation K ψ ν σ c a hFE Φ j₀ hsupp f r hR
  have hne : (c : ℂ) * r * (spectralPoint K.canonicalTopologicalData.residueCardinality 1 *
      spectralPoint K.canonicalTopologicalData.residueCardinality
        (GodementJacquet.jpssShift n)) ^ a ≠ 0 :=
    mul_ne_zero (mul_ne_zero c.ne_zero hr) (zpow_ne_zero _ (mul_ne_zero
      (RankinSelberg.spectralPoint_ne_zero_of_pos hq0 _)
      (RankinSelberg.spectralPoint_ne_zero_of_pos hq0 _)))
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← h]
  refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => ?_
  by_cases h1 : rectangularFourierIntegral ψ ν Φ g.val = 0
  · rw [h1, zero_mul]
  · rw [hcon g hg h1, mul_zero]

end Padic

end Langlands.BushnellKutzko
