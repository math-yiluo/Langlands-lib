import Langlands.LocalFactor.WeilDeligne
import Langlands.WeilDeligne.Dual
import Langlands.WeilDeligne.SumsTensor
import Mathlib.RingTheory.Algebraic.Integral

noncomputable section

universe uK uG uV uW uT

open Polynomial

namespace Langlands.LocalFactor

namespace RationalReflection

variable {K : Type uK} [Field K]

/-- The reciprocal change of variable with a nonzero scalar. -/
def reflectedVariable (c : Kˣ) : RatFunc K := algebraMap K (RatFunc K) (c : K) / RatFunc.X

theorem variable_transcendental (c : Kˣ) : Transcendental K (reflectedVariable c) := by
  intro h
  apply RatFunc.transcendental_X (K := K)
  have ht := h.inv.smul (c : K)
  have hc : algebraMap K (RatFunc K) (c : K) ≠ 0 :=
    (map_ne_zero (algebraMap K (RatFunc K))).mpr c.ne_zero
  rw [Algebra.smul_def, reflectedVariable] at ht
  convert ht using 1
  field_simp

/-- Substitution `X ↦ c / X` as an actual algebra homomorphism. -/
def subst (c : Kˣ) : RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.liftAlgHom (aeval (reflectedVariable c))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      ((transcendental_iff_injective).mp (variable_transcendental c)))

@[simp]
theorem subst_polynomial (c : Kˣ) (p : K[X]) :
    subst c (algebraMap K[X] (RatFunc K) p) = aeval (reflectedVariable c) p := by
  have h := RatFunc.liftAlgHom_apply_div (aeval (reflectedVariable c))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      ((transcendental_iff_injective).mp (variable_transcendental c))) p 1
  simpa [subst] using h

@[simp]
theorem subst_X (c : Kˣ) : subst c RatFunc.X = reflectedVariable c := by
  rw [← RatFunc.algebraMap_X, subst_polynomial, aeval_X]

@[simp]
theorem subst_variable (c : Kˣ) : subst c (reflectedVariable c) = RatFunc.X := by
  have hc : algebraMap K (RatFunc K) (c : K) ≠ 0 :=
    (map_ne_zero (algebraMap K (RatFunc K))).mpr c.ne_zero
  rw [reflectedVariable, map_div₀, AlgHom.commutes, subst_X, reflectedVariable]
  field_simp

@[simp]
theorem subst_subst (c : Kˣ) (f : RatFunc K) : subst c (subst c f) = f := by
  induction f using RatFunc.induction_on with
  | f p q hq =>
    simp only [map_div₀, subst_polynomial, ← aeval_algHom_apply, subst_variable]
    simp only [RatFunc.aeval_X_left_eq_algebraMap]

/-- The reciprocal substitution is its own inverse. -/
def equiv (c : Kˣ) : RatFunc K ≃ₐ[K] RatFunc K :=
  { subst c with
    invFun := subst c
    left_inv := subst_subst c
    right_inv := subst_subst c }

end RationalReflection

namespace WeilDeligne

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

/-- The pair L-factor uses the actual tensor and its full monodromy. -/
def pairLFactor (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν)
    (I : Subgroup G) [I.Normal] (g : G) : RatFunc K :=
  rationalLFactor (WeilDeligneRepresentation.tensor A B) I g

theorem pairLFactor_ne_zero (A : WeilDeligneRepresentation K G ν)
    (B : WeilDeligneRepresentation K G ν) (I : Subgroup G) [I.Normal] (g : G) :
    pairLFactor A B I g ≠ 0 := rationalLFactor_ne_zero _ _ _

/-- The reflected dual factor, with reciprocal scale supplied as a unit. -/
def reflectedDualLFactor (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) (c : Kˣ) : RatFunc K :=
  RationalReflection.subst c (rationalLFactor (WeilDeligneRepresentation.dual A) I g)

theorem reflectedDualLFactor_ne_zero (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) (c : Kˣ) :
    reflectedDualLFactor A I g c ≠ 0 :=
  (map_ne_zero (RationalReflection.subst c)).mpr (rationalLFactor_ne_zero _ _ _)

/-- The rational L-ratio that occurs in a gamma factor. No epsilon system is assumed. -/
def rationalLRatio (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) (c : Kˣ) : RatFunc K :=
  reflectedDualLFactor A I g c / rationalLFactor A I g

theorem rationalLRatio_ne_zero (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) (c : Kˣ) : rationalLRatio A I g c ≠ 0 :=
  div_ne_zero (reflectedDualLFactor_ne_zero _ _ _ _) (rationalLFactor_ne_zero _ _ _)

/-- Exact reciprocal-polynomial formula for the reflected ratio. -/
theorem rationalLRatio_eq (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) (c : Kˣ) :
    rationalLRatio A I g c =
      algebraMap K[X] (RatFunc K) (eulerPolynomial A I g) /
        aeval (RationalReflection.reflectedVariable c)
          (eulerPolynomial (WeilDeligneRepresentation.dual A) I g) := by
  change RationalReflection.subst c
    ((algebraMap K[X] (RatFunc K)
      (eulerPolynomial (WeilDeligneRepresentation.dual A) I g))⁻¹) /
    (algebraMap K[X] (RatFunc K) (eulerPolynomial A I g))⁻¹ = _
  rw [map_inv₀, RationalReflection.subst_polynomial]
  exact inv_div_inv _ _

/-- Common regular domain; it excludes poles of both individual factors. -/
def LRatioRegularPoint (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) (c : Kˣ) :=
  {z : Kˣ // (eulerPolynomial A I g).eval (z : K) ≠ 0 ∧
    (eulerPolynomial (WeilDeligneRepresentation.dual A) I g).eval ((c / z : Kˣ) : K) ≠ 0}

/-- The unit-valued ratio on its common regular domain. -/
def regularLRatioValue (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) (c : Kˣ)
    (z : LRatioRegularPoint A I g c) : Kˣ :=
  regularLValue (WeilDeligneRepresentation.dual A) I g ⟨↑(c / z.val), z.property.2⟩ /
    regularLValue A I g ⟨↑z.val, z.property.1⟩

theorem regularLRatioValue_eq (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) (c : Kˣ)
    (z : LRatioRegularPoint A I g c) :
    (regularLRatioValue A I g c z : K) =
      (eulerPolynomial A I g).eval (z.val : K) /
        (eulerPolynomial (WeilDeligneRepresentation.dual A) I g).eval
          ((c / z.val : Kˣ) : K) := by
  simp only [regularLRatioValue, Units.val_div_eq_div_val, regularLValue]
  change ((eulerPolynomial (WeilDeligneRepresentation.dual A) I g).eval
      ((c : K) / (z.val : K)))⁻¹ /
    ((eulerPolynomial A I g).eval (z.val : K))⁻¹ = _
  exact inv_div_inv _ _

section Invariance

variable (I : Subgroup G) [I.Normal] (g : G) (c : Kˣ)

/-- Pair factors respect genuine pair equivalences in both arguments. -/
theorem pairLFactor_eq_of_equiv
    {A A' : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B B' : WeilDeligneRepresentation.{uK, uG, uW} K G ν}
    (e : WeilDeligneRepresentation.Equiv A A') (f : WeilDeligneRepresentation.Equiv B B') :
    pairLFactor A B I g = pairLFactor A' B' I g :=
  rationalLFactor_eq_of_equiv I (WeilDeligneRepresentation.tensorEquiv e f) g

theorem rationalLRatio_eq_of_equiv
    {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν}
    (e : WeilDeligneRepresentation.Equiv A B) :
    rationalLRatio A I g c = rationalLRatio B I g c := by
  unfold rationalLRatio reflectedDualLFactor
  rw [rationalLFactor_eq_of_equiv I e g,
    rationalLFactor_eq_of_equiv I (WeilDeligneRepresentation.dualEquiv e).symm g]

/-- Pair L-factors on actual pair-isomorphism classes. -/
def pairLFactorClass (A : WeilDeligneRepresentation.IsomorphismClasses.{uK, uG, uV} K G ν)
    (B : WeilDeligneRepresentation.IsomorphismClasses.{uK, uG, uW} K G ν) : RatFunc K :=
  rationalLFactorClass I g (WeilDeligneRepresentation.tensorClass A B)

/-- The reflected L-ratio on actual pair-isomorphism classes. -/
def rationalLRatioClass :
    WeilDeligneRepresentation.IsomorphismClasses.{uK, uG, uV} K G ν → RatFunc K :=
  Quotient.lift (fun A => rationalLRatio A I g c)
    (fun _ _ ⟨e⟩ => rationalLRatio_eq_of_equiv I g c e)

@[simp]
theorem pairLFactorClass_classOf (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν) :
    pairLFactorClass I g (WeilDeligneRepresentation.classOf A)
      (WeilDeligneRepresentation.classOf B) = pairLFactor A B I g := rfl

@[simp]
theorem rationalLRatioClass_classOf (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    rationalLRatioClass I g c (WeilDeligneRepresentation.classOf A) =
      rationalLRatio A I g c := rfl

end Invariance

theorem rationalLRatio_eq_of_coset (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] {g h : G} (hi : h * g⁻¹ ∈ I) (c : Kˣ) :
    rationalLRatio A I h c = rationalLRatio A I g c := by
  unfold rationalLRatio reflectedDualLFactor
  rw [rationalLFactor_eq_of_coset A I hi,
    rationalLFactor_eq_of_coset (WeilDeligneRepresentation.dual A) I hi]

section Spectral

variable {G : Type uG} [Group G] {ν : G →* ℂˣ}

/-- This unit is `q⁻¹`; the exponential form matches the published spectral parameter. -/
def reflectionScale (q : ℝ) (hq : 0 < q) : ℂˣ := spectralParameter q hq 1

@[simp]
theorem coe_reflectionScale (q : ℝ) (hq : 0 < q) :
    (reflectionScale q hq : ℂ) = (q : ℂ)⁻¹ := by
  rw [reflectionScale, spectralParameter_eq_cpow]
  rw [Complex.cpow_neg_one]

/-- The spectral reflection `s ↦ 1-s` is exactly `X ↦ q⁻¹/X`. -/
theorem spectralParameter_one_sub (q : ℝ) (hq : 0 < q) (s : ℂ) :
    spectralParameter q hq (1 - s) = reflectionScale q hq / spectralParameter q hq s := by
  apply Units.ext
  change Complex.exp (-(1 - s) * (Real.log q : ℂ)) =
    Complex.exp (-1 * (Real.log q : ℂ)) / Complex.exp (-s * (Real.log q : ℂ))
  rw [← Complex.exp_sub]
  congr 1
  ring

/-- The spectral common regular domain for `L(1-s,A∨)/L(s,A)`. -/
def SpectralLRatioRegularPoint (A : WeilDeligneRepresentation ℂ G ν)
    (I : Subgroup G) [I.Normal] (g : G) (q : ℝ) (hq : 0 < q) :=
  {s : ℂ // (eulerPolynomial A I g).eval (spectralParameter q hq s : ℂ) ≠ 0 ∧
    (eulerPolynomial (WeilDeligneRepresentation.dual A) I g).eval
      (spectralParameter q hq (1 - s) : ℂ) ≠ 0}

/-- Convert a regular spectral point to the rational common regular domain. -/
def SpectralLRatioRegularPoint.toRegular (A : WeilDeligneRepresentation ℂ G ν)
    (I : Subgroup G) [I.Normal] (g : G) (q : ℝ) (hq : 0 < q)
    (s : SpectralLRatioRegularPoint A I g q hq) :
    LRatioRegularPoint A I g (reflectionScale q hq) :=
  ⟨spectralParameter q hq s.val, s.property.1,
    by rw [← spectralParameter_one_sub]; exact s.property.2⟩

/-- The ratio of the two actual spectral values, away from both pole sets. -/
def spectralLRatioValue (A : WeilDeligneRepresentation ℂ G ν)
    (I : Subgroup G) [I.Normal] (g : G) (q : ℝ) (hq : 0 < q)
    (s : SpectralLRatioRegularPoint A I g q hq) : ℂˣ :=
  spectralLValue (WeilDeligneRepresentation.dual A) I g q hq ⟨1 - s.val, s.property.2⟩ /
    spectralLValue A I g q hq ⟨s.val, s.property.1⟩

theorem spectralLRatioValue_eq_regular (A : WeilDeligneRepresentation ℂ G ν)
    (I : Subgroup G) [I.Normal] (g : G) (q : ℝ) (hq : 0 < q)
    (s : SpectralLRatioRegularPoint A I g q hq) :
    spectralLRatioValue A I g q hq s =
      regularLRatioValue A I g (reflectionScale q hq)
        (SpectralLRatioRegularPoint.toRegular A I g q hq s) := by
  apply Units.ext
  simp only [spectralLRatioValue, regularLRatioValue, Units.val_div_eq_div_val, spectralLValue,
    LocalFactor.spectralFactorValue, regularLValue]
  change ((eulerPolynomial (WeilDeligneRepresentation.dual A) I g).eval
      (spectralParameter q hq (1 - s.val) : ℂ))⁻¹ / _ = _
  rw [spectralParameter_one_sub]
  rfl

/-- Pair evaluation applies the same safe domain to the actual tensor pair. -/
def pairSpectralLValue (A : WeilDeligneRepresentation ℂ G ν)
    (B : WeilDeligneRepresentation ℂ G ν) (I : Subgroup G) [I.Normal] (g : G)
    (q : ℝ) (hq : 0 < q)
    (s : SpectralRegularPoint (WeilDeligneRepresentation.tensor A B) I g q hq) : ℂˣ :=
  spectralLValue (WeilDeligneRepresentation.tensor A B) I g q hq s

end Spectral

end WeilDeligne

end Langlands.LocalFactor
