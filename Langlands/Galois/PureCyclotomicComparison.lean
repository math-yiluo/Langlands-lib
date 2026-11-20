import Langlands.Galois.CyclotomicTwist
import Langlands.Galois.PureWeightParity

/-! # Arithmetic comparison after the integral cyclotomic twist -/

noncomputable section

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.Unramified Polynomial Filter

universe uK uL uM uV uW uE

variable {K : Type uK} [Field K] [NumberField K]
variable {L : Type uL} [Field L] [NumberField L] {M : Type uM} [Field M] [NumberField M]
variable {E : Type uE} [Field E]
variable {excludedL : Finset (FinitePlace L)} {excludedM : Finset (FinitePlace M)}
variable {R : Collection.{uK, uL, uV} K L excludedL}
variable {U : Collection.{uK, uM, uW} K M excludedM}

/-- Unit-normalized association and an integral half-weight difference give
    equal arithmetic Euler polynomials after the actual cyclotomic twist,
    with coefficients compared in a common field. -/
theorem eventually_frobeniusEulerPolynomial_map_eq_cyclotomicTwist_of_weakAssociation
    {ι : L →+* ℂ} {κ : M →+* ℂ} {r : ℕ} {s : SpectralSystem (FinitePlace K) r}
    {m n k : ℤ} (hk : m - n = 2 * k)
    (hR : IsPureCompatible excludedL R m) (hU : IsPureCompatible excludedM U n)
    (hs : IsWeaklyAssociatedToSpectrum ι excludedL R s)
    (ht : IsWeaklyAssociatedToSpectrum κ excludedM U s)
    (lam : {lam : FinitePlace L // lam ∉ excludedL})
    (mu : {mu : FinitePlace M // mu ∉ excludedM})
    (ιE : E →+* ℂ) (jR : FiniteCompletion L lam.val →+* E)
    (jU : FiniteCompletion M mu.val →+* E)
    (hι : ∀ x : L, ιE (jR (NumberField.FinitePlace.embedding lam.val x)) = ι x)
    (hκ : ∀ x : M, ιE (jU (NumberField.FinitePlace.embedding mu.val x)) = κ x) :
    ∀ᶠ w in cofinite,
      (frobeniusEulerPolynomial (R lam) w).map jR =
        (frobeniusEulerPolynomial (cyclotomicTwist mu.val k (U mu)) w).map jU := by
  obtain ⟨S, P, hP, hp⟩ := hR
  obtain ⟨T, Q, hQ, hq⟩ := hU
  have he := eventually_pureEuler_eq_comp_of_weakAssociation hs ht hP hQ hp hq lam mu
  have hRmap : ιE.comp (jR.comp (NumberField.FinitePlace.embedding lam.val)) = ι :=
    RingHom.ext hι
  have hUmap : ιE.comp (jU.comp (NumberField.FinitePlace.embedding mu.val)) = κ :=
    RingHom.ext hκ
  filter_upwards [he, S.eventually_cofinite_notMem, T.eventually_cofinite_notMem,
    eventually_residueCharacteristic_not_dvd (K := K) (residueCharacteristic lam.val)
      (residueCharacteristic_prime lam.val).ne_zero,
    eventually_residueCharacteristic_not_dvd (K := K) (residueCharacteristic mu.val)
      (residueCharacteristic_prime mu.val).ne_zero] with w hew hs' ht' hl hm
  have hL : residueCharacteristic w ≠ residueCharacteristic lam.val :=
    fun h => hl (h ▸ dvd_rfl)
  have hM : residueCharacteristic w ≠ residueCharacteristic mu.val :=
    fun h => hm (h ▸ dvd_rfl)
  have hleft := (hasEulerPolynomialAt_iff.mp (hP lam w hs' hL)).2
  have hright := (hasEulerPolynomialAt_iff.mp ((hQ mu w ht' hM).cyclotomicTwist k hM)).2
  have harith := hew hL hM
  rw [hk, radius_two_mul, Complex.ofReal_zpow, Complex.ofReal_natCast] at harith
  apply Polynomial.map_injective ιE ιE.injective
  simpa only [hleft, hright, Polynomial.map_comp, Polynomial.map_map, hRmap, hUmap,
    Polynomial.map_mul, Polynomial.map_C, map_zpow₀, map_natCast, Polynomial.map_X] using harith

end Langlands.GaloisRepresentation
