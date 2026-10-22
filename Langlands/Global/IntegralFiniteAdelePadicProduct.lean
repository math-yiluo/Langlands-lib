import Langlands.Global.IntegralFiniteAdeles
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

namespace Langlands.Global

universe u

/-- The product of completed integer rings, embedded in the actual finite adeles. -/
def integralFiniteAdelesProductEquiv (K : Type u) [Field K] [NumberField K] :
    (∀ v : FinitePlace K, v.adicCompletionIntegers K) ≃+* integralFiniteAdeles K where
  toFun x := ⟨RestrictedProduct.structureMap _ _ Filter.cofinite x, fun v => (x v).property⟩
  invFun a v := ⟨a.val v, a.property v⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp] theorem integralFiniteAdelesProductEquiv_apply
    (K : Type u) [Field K] [NumberField K]
    (x : ∀ v : FinitePlace K, v.adicCompletionIntegers K) (v : FinitePlace K) :
    (integralFiniteAdelesProductEquiv K x : FiniteAdeles K) v = x v := rfl

theorem continuous_integralFiniteAdelesProductEquiv
    (K : Type u) [Field K] [NumberField K] :
    Continuous (integralFiniteAdelesProductEquiv K) := by
  apply continuous_induced_rng.mpr
  exact RestrictedProduct.isEmbedding_structureMap.continuous

theorem continuous_integralFiniteAdelesProductEquiv_symm
    (K : Type u) [Field K] [NumberField K] :
    Continuous (integralFiniteAdelesProductEquiv K).symm := by
  apply continuous_pi
  intro v
  exact continuous_induced_rng.mpr
    ((RestrictedProduct.continuous_eval v).comp continuous_subtype_val)

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- The explicit prime-index and completed-integer identifications into integral rational adeles. -/
def rationalPadicProductIntegralEquiv :
    (∀ p : Nat.Primes, PadicInt p.val) ≃+* integralFiniteAdeles ℚ :=
  ((RingEquiv.piCongrLeft (fun p : Nat.Primes => PadicInt p.val)
    (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ))).symm.trans
      (RingEquiv.piCongrRight fun v =>
        (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm.toRingEquiv)).trans
    (integralFiniteAdelesProductEquiv ℚ)

@[simp] theorem rationalPadicProductIntegralEquiv_apply
    (x : ∀ p : Nat.Primes, PadicInt p.val) (v : FinitePlace ℚ) :
    (rationalPadicProductIntegralEquiv x : FiniteAdeles ℚ) v =
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        (x (Rat.HeightOneSpectrum.primesEquiv v)) := rfl

theorem continuous_rationalPadicProductIntegralEquiv :
    Continuous rationalPadicProductIntegralEquiv := by
  apply (continuous_integralFiniteAdelesProductEquiv ℚ).comp
  apply continuous_pi
  intro v
  exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm.continuous.comp
    (continuous_apply (Rat.HeightOneSpectrum.primesEquiv v))

theorem continuous_rationalPadicProductIntegralEquiv_symm :
    Continuous rationalPadicProductIntegralEquiv.symm := by
  apply (Homeomorph.piCongrLeft (Y := fun p : Nat.Primes => PadicInt p.val)
    (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ))).continuous.comp
  exact (continuous_pi fun v =>
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).continuous.comp
      (continuous_apply v)).comp (continuous_integralFiniteAdelesProductEquiv_symm ℚ)

@[simp] theorem rationalPadicProductIntegralEquiv_intCast (z : ℤ) :
    (rationalPadicProductIntegralEquiv (fun p => (z : PadicInt p.val)) : FiniteAdeles ℚ) =
      algebraMap ℚ (FiniteAdeles ℚ) (z : ℚ) := by
  change (rationalPadicProductIntegralEquiv (z : ∀ p : Nat.Primes, PadicInt p.val) :
    FiniteAdeles ℚ) = _
  simp

end Langlands.Global
