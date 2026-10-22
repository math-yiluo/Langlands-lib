import Langlands.LocalFactor.CommonClosureWeilDeligne
import Langlands.LocalFactor.WeilDelignePair
import Langlands.Weil.Representation.OperationClosureProof

/-!
# Conditional gamma and tensor-pair factors in a common closure

An explicit local-constant system supplies the full spectral epsilon value.
Gamma is evaluated only where both individual L-factors are regular.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.CommonClosureGamma

open CommonClosure CommonClosureSpectral CommonClosureWeilDeligne Weil.Local Polynomial

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The common regular domain for the original and reflected dual factors. -/
abbrev RegularPoint (E : Extension F) (A : Pair.{uF, uV} F E)
    (Φ : GeometricFrobenius F E) :=
  WeilDeligne.SpectralLRatioRegularPoint A (inertia F E) Φ.val
    (residueCardinality F E) (residueCardinality_pos F E)

/-- The actual reflected L-ratio on this domain. -/
def lRatioValue (E : Extension F) (A : Pair.{uF, uV} F E)
    (Φ : GeometricFrobenius F E) (s : RegularPoint F E A Φ) : ℂˣ :=
  WeilDeligne.spectralLRatioValue A (inertia F E) Φ.val
    (residueCardinality F E) (residueCardinality_pos F E) s

/-- Exact scalar expression, with both Euler denominators retained in the domain. -/
theorem lRatioValue_eq (E : Extension F) (A : Pair.{uF, uV} F E)
    (Φ : GeometricFrobenius F E) (s : RegularPoint F E A Φ) :
    (lRatioValue F E A Φ s : ℂ) =
      (WeilDeligne.eulerPolynomial A (inertia F E) Φ.val).eval
        (spectralParameter (residueCardinality F E) (residueCardinality_pos F E) s.val : ℂ) /
      (WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual A) (inertia F E) Φ.val).eval
        (spectralParameter (residueCardinality F E) (residueCardinality_pos F E) (1 - s.val) : ℂ) := by
  simp only [lRatioValue, WeilDeligne.spectralLRatioValue, Units.val_div_eq_div_val,
    WeilDeligne.spectralLValue, spectralFactorValue]
  exact inv_div_inv _ _

/-- Conditional measure-dependent gamma, including the actual WD correction. -/
def conditionalGammaValue (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F E) (s : RegularPoint F E A Φ) : ℂˣ :=
  conditionalEpsilonValue F e ε hε E ψ μ A hA Φ s.val * lRatioValue F E A Φ s

/-- The construction retains the full invariant-quotient determinant. -/
theorem conditionalGammaValue_formula (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F E) (s : RegularPoint F E A Φ) :
    (conditionalGammaValue F e ε hε E ψ μ A hA Φ s : ℂ) =
      (conditionalDeligneValue F e ε hε E ψ μ (underlyingClass F E A hA) s.val : ℂ) *
      LinearMap.det ((Complex.exp (-s.val * (Real.log (residueCardinality F E) : ℂ))) •
        (-WeilDeligne.quotientOperator A (inertia F E) Φ.val)) *
      ((WeilDeligne.eulerPolynomial A (inertia F E) Φ.val).eval
        (spectralParameter (residueCardinality F E) (residueCardinality_pos F E) s.val : ℂ) /
      (WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual A) (inertia F E) Φ.val).eval
        (spectralParameter (residueCardinality F E) (residueCardinality_pos F E) (1 - s.val) : ℂ)) := by
  rw [conditionalGammaValue, Units.val_mul, conditionalEpsilonValue, Units.val_mul,
    quotientValue_det, lRatioValue_eq]

private def polynomialRegularPoint (P Q : ℂ[X]) (q : ℝ) (hq : 0 < q) :=
  {s : ℂ // P.eval (spectralParameter q hq s : ℂ) ≠ 0 ∧
    Q.eval (spectralParameter q hq (1 - s) : ℂ) ≠ 0}

private def polynomialRegularPointEquiv (P Q R S : ℂ[X]) (q : ℝ) (hq : 0 < q)
    (hP : P = R) (hQ : Q = S) :
    polynomialRegularPoint P Q q hq ≃ polynomialRegularPoint R S q hq :=
  Equiv.subtypeEquivRight (fun _ => by rw [hP, hQ])

private theorem polynomialRegularPointEquiv_val (P Q R S : ℂ[X]) (q : ℝ) (hq : 0 < q)
    (hP : P = R) (hQ : Q = S) (s : polynomialRegularPoint P Q q hq) :
    (polynomialRegularPointEquiv P Q R S q hq hP hQ s).val = s.val := rfl

/-- Equivalence of pairs preserves the exact common regular domain. -/
def regularPointEquiv (E : Extension F) {A B : Pair.{uF, uV} F E}
    (f : WeilDeligneRepresentation.Equiv A B) (Φ : GeometricFrobenius F E) :
    RegularPoint F E A Φ ≃ RegularPoint F E B Φ :=
  polynomialRegularPointEquiv _ _ _ _
    (residueCardinality F E) (residueCardinality_pos F E)
    (WeilDeligne.eulerPolynomial_eq_of_equiv (inertia F E) f Φ.val)
    (WeilDeligne.eulerPolynomial_eq_of_equiv (inertia F E)
      (WeilDeligneRepresentation.dualEquiv f).symm Φ.val)

@[simp]
theorem regularPointEquiv_val (E : Extension F) {A B : Pair.{uF, uV} F E}
    (f : WeilDeligneRepresentation.Equiv A B) (Φ : GeometricFrobenius F E)
    (s : RegularPoint F E A Φ) : (regularPointEquiv F E f Φ s).val = s.val := rfl

/-- The L-ratio respects the identity-on-parameter domain equivalence. -/
theorem lRatioValue_eq_of_equiv (E : Extension F) {A B : Pair.{uF, uV} F E}
    (f : WeilDeligneRepresentation.Equiv A B) (Φ : GeometricFrobenius F E)
    (s : RegularPoint F E A Φ) :
    lRatioValue F E A Φ s = lRatioValue F E B Φ (regularPointEquiv F E f Φ s) := by
  apply Units.ext
  rw [lRatioValue_eq, lRatioValue_eq]
  simp only [regularPointEquiv_val,
    WeilDeligne.eulerPolynomial_eq_of_equiv (inertia F E) f,
    WeilDeligne.eulerPolynomial_eq_of_equiv (inertia F E)
      (WeilDeligneRepresentation.dualEquiv f).symm]

/-- Full gamma is invariant under actual pair equivalence. -/
theorem conditionalGammaValue_eq_of_equiv (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    {A B : Pair.{uF, uV} F E}
    (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous)
    (f : WeilDeligneRepresentation.Equiv A B) (Φ : GeometricFrobenius F E)
    (s : RegularPoint F E A Φ) :
    conditionalGammaValue F e ε hε E ψ μ A hA Φ s =
      conditionalGammaValue F e ε hε E ψ μ B hB Φ (regularPointEquiv F E f Φ s) := by
  unfold conditionalGammaValue
  rw [regularPointEquiv_val,
    conditionalEpsilonValue_eq_of_equiv F e ε hε E ψ μ hA hB f,
    lRatioValue_eq_of_equiv F E f]

/-- The polynomial depends only on the supplied geometric Frobenius coset. -/
theorem eulerPolynomial_eq_of_frobenius (E : Extension F) (A : Pair.{uF, uV} F E)
    (Φ Ψ : GeometricFrobenius F E) :
    WeilDeligne.eulerPolynomial A (inertia F E) Ψ.val =
      WeilDeligne.eulerPolynomial A (inertia F E) Φ.val := by
  unfold WeilDeligne.eulerPolynomial
  rw [WeilDeligne.kernelOperator_eq_of_coset A (inertia F E) (frobenius_coset F E Φ Ψ)]

/-- Changing the supplied geometric lift preserves the common regular domain. -/
def regularPointFrobeniusEquiv (E : Extension F) (A : Pair.{uF, uV} F E)
    (Φ Ψ : GeometricFrobenius F E) :
    RegularPoint F E A Φ ≃ RegularPoint F E A Ψ :=
  polynomialRegularPointEquiv _ _ _ _
    (residueCardinality F E) (residueCardinality_pos F E)
    (eulerPolynomial_eq_of_frobenius F E A Ψ Φ)
    (eulerPolynomial_eq_of_frobenius F E (WeilDeligneRepresentation.dual A) Ψ Φ)

@[simp]
theorem regularPointFrobeniusEquiv_val (E : Extension F) (A : Pair.{uF, uV} F E)
    (Φ Ψ : GeometricFrobenius F E) (s : RegularPoint F E A Φ) :
    (regularPointFrobeniusEquiv F E A Φ Ψ s).val = s.val :=
  polynomialRegularPointEquiv_val _ _ _ _
    (residueCardinality F E) (residueCardinality_pos F E)
    (eulerPolynomial_eq_of_frobenius F E A Ψ Φ)
    (eulerPolynomial_eq_of_frobenius F E (WeilDeligneRepresentation.dual A) Ψ Φ) s

/-- Lift independence of the reflected L-ratio on the transported domain. -/
theorem lRatioValue_eq_of_frobenius (E : Extension F) (A : Pair.{uF, uV} F E)
    (Φ Ψ : GeometricFrobenius F E) (s : RegularPoint F E A Φ) :
    lRatioValue F E A Ψ (regularPointFrobeniusEquiv F E A Φ Ψ s) =
      lRatioValue F E A Φ s := by
  apply Units.ext
  rw [lRatioValue_eq, lRatioValue_eq]
  simp only [regularPointFrobeniusEquiv_val,
    eulerPolynomial_eq_of_frobenius F E A Φ Ψ,
    eulerPolynomial_eq_of_frobenius F E (WeilDeligneRepresentation.dual A) Φ Ψ]

/-- Full gamma is independent of the supplied geometric lift. -/
theorem conditionalGammaValue_eq_of_frobenius (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous)
    (Φ Ψ : GeometricFrobenius F E) (s : RegularPoint F E A Φ) :
    conditionalGammaValue F e ε hε E ψ μ A hA Ψ
      (regularPointFrobeniusEquiv F E A Φ Ψ s) =
      conditionalGammaValue F e ε hε E ψ μ A hA Φ s := by
  unfold conditionalGammaValue
  rw [regularPointFrobeniusEquiv_val,
    conditionalEpsilonValue_eq_of_frobenius F e ε hε E ψ μ A hA Φ Ψ,
    lRatioValue_eq_of_frobenius]

/-- Continuity of the actual tensor follows from continuity of its two factors. -/
theorem tensor_isContinuous (E : Extension F) (A B : Pair.{uF, uV} F E)
    (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous) :
    (WeilDeligneRepresentation.tensor A B).toFiniteRepresentation.IsContinuous :=
  Weil.OperationClosure.continuous_tensor A.representation B.representation hA hB

/-- Pair epsilon uses the full tensor monodromy and its own quotient correction. -/
def conditionalPairEpsilonValue (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A B : Pair.{uF, uV} F E)
    (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F E) (s : ℂ) : ℂˣ :=
  conditionalEpsilonValue F e ε hε E ψ μ (WeilDeligneRepresentation.tensor A B)
    (tensor_isContinuous F E A B hA hB) Φ s

/-- Pair gamma is gamma of the actual tensor, on that tensor's common regular domain. -/
def conditionalPairGammaValue (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A B : Pair.{uF, uV} F E)
    (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F E)
    (s : RegularPoint F E (WeilDeligneRepresentation.tensor A B) Φ) : ℂˣ :=
  conditionalGammaValue F e ε hε E ψ μ (WeilDeligneRepresentation.tensor A B)
    (tensor_isContinuous F E A B hA hB) Φ s

/-- The pair product uses the pair epsilon, not a product of the separate epsilon values. -/
theorem conditionalPairGammaValue_eq (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A B : Pair.{uF, uV} F E)
    (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F E)
    (s : RegularPoint F E (WeilDeligneRepresentation.tensor A B) Φ) :
    conditionalPairGammaValue F e ε hε E ψ μ A B hA hB Φ s =
      conditionalPairEpsilonValue F e ε hε E ψ μ A B hA hB Φ s.val *
      lRatioValue F E (WeilDeligneRepresentation.tensor A B) Φ s := rfl

/-- Actual pair equivalences in both tensor legs preserve pair epsilon. -/
theorem conditionalPairEpsilonValue_eq_of_equiv (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    {A A' B B' : Pair.{uF, uV} F E}
    (hA : A.toFiniteRepresentation.IsContinuous) (hA' : A'.toFiniteRepresentation.IsContinuous)
    (hB : B.toFiniteRepresentation.IsContinuous) (hB' : B'.toFiniteRepresentation.IsContinuous)
    (f : WeilDeligneRepresentation.Equiv A A') (g : WeilDeligneRepresentation.Equiv B B')
    (Φ : GeometricFrobenius F E) (s : ℂ) :
    conditionalPairEpsilonValue F e ε hε E ψ μ A B hA hB Φ s =
      conditionalPairEpsilonValue F e ε hε E ψ μ A' B' hA' hB' Φ s :=
  conditionalEpsilonValue_eq_of_equiv F e ε hε E ψ μ _ _
    (WeilDeligneRepresentation.tensorEquiv f g) Φ s

/-- Pair gamma is invariant in both tensor legs on the transported regular domain. -/
theorem conditionalPairGammaValue_eq_of_equiv (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    {A A' B B' : Pair.{uF, uV} F E}
    (hA : A.toFiniteRepresentation.IsContinuous) (hA' : A'.toFiniteRepresentation.IsContinuous)
    (hB : B.toFiniteRepresentation.IsContinuous) (hB' : B'.toFiniteRepresentation.IsContinuous)
    (f : WeilDeligneRepresentation.Equiv A A') (g : WeilDeligneRepresentation.Equiv B B')
    (Φ : GeometricFrobenius F E)
    (s : RegularPoint F E (WeilDeligneRepresentation.tensor A B) Φ) :
    conditionalPairGammaValue F e ε hε E ψ μ A B hA hB Φ s =
      conditionalPairGammaValue F e ε hε E ψ μ A' B' hA' hB' Φ
        (regularPointEquiv F E (WeilDeligneRepresentation.tensorEquiv f g) Φ s) :=
  conditionalGammaValue_eq_of_equiv F e ε hε E ψ μ _ _
    (WeilDeligneRepresentation.tensorEquiv f g) Φ s

/-- At zero monodromy, the gamma correction reduces to the ordinary spectral constant. -/
theorem conditionalGammaValue_of_monodromy_zero (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous)
    (hN : A.monodromy = 0) (Φ : GeometricFrobenius F E) (s : RegularPoint F E A Φ) :
    conditionalGammaValue F e ε hε E ψ μ A hA Φ s =
      conditionalDeligneValue F e ε hε E ψ μ (underlyingClass F E A hA) s.val *
        lRatioValue F E A Φ s := by
  rw [conditionalGammaValue, conditionalEpsilonValue_of_monodromy_zero F e ε hε E ψ μ A hA hN]

end Langlands.LocalFactor.CommonClosureGamma
