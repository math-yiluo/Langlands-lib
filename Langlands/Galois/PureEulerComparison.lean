import Langlands.Galois.FrobeniusLift
import Langlands.Galois.WeakAssociation
import Langlands.Automorphic.AssociatedPresentationSpectrum

/-! # Comparing Euler polynomials of pure weakly associated families -/

noncomputable section

namespace Langlands.GaloisRepresentation

open Polynomial Langlands.Global Langlands.Unramified Langlands.Automorphic
open Cohomology.Weights

universe uK uL uM uV uW uP uQ

private theorem reverse_map_of_injective {L M : Type*} [Semiring L] [Semiring M]
    (ι : L →+* M) (hι : Function.Injective ι) (P : L[X]) :
    (P.map ι).reverse = P.reverse.map ι := by
  rw [Polynomial.reverse, Polynomial.reverse, natDegree_map_eq_of_injective hι, reflect_map]

private theorem reverse_reverse_of_coeff_zero_ne {L : Type*} [Semiring L]
    {P : L[X]} (hP : P.coeff 0 ≠ 0) : P.reverse.reverse = P := by
  change P.reverse.reflect P.reverse.natDegree = P
  rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hP), Nat.sub_zero]
  exact reflect_reflect

/-- Purity identifies the unitary normalization with a single scalar substitution. -/
theorem unitaryEulerPolynomial_eq_pure_substitution {L : Type uL} [Field L] [NumberField L]
    (ι : L →+* ℂ) {q : ℕ} {m : ℤ} {P : L[X]} (h0 : P.coeff 0 ≠ 0)
    (hP : IsPurePolynomial q m P.reverse) :
    unitaryEulerPolynomial (P.map ι) =
      (P.map ι).comp (C (radius q m : ℂ)⁻¹ * X) := by
  have hrev : (P.map ι).reverse = P.reverse.map ι :=
    reverse_map_of_injective ι ι.injective P
  have hmonic : (P.map ι).reverse.Monic := hrev ▸ hP.1.map ι
  have hroots : HasComplexRootsOfWeight q m (P.map ι).reverse :=
    hrev ▸ hP.hasComplexRootsOfWeight ι
  have h0' : (P.map ι).coeff 0 ≠ 0 := by
    rw [coeff_map]
    exact (_root_.map_ne_zero ι).mpr h0
  rw [unitaryEulerPolynomial, unitaryEulerFromEigenvalues_eq_weight_substitution hmonic hroots,
    reverse_reverse_of_coeff_zero_ne h0']

/-- Recover the arithmetic comparison of two pure polynomials from equality of
    their unitary normalizations, with each coefficient embedding retained. -/
theorem pureEuler_eq_comp_of_unitaryEuler_eq
    {L : Type uL} [Field L] [NumberField L] {M : Type uM} [Field M] [NumberField M]
    (ι : L →+* ℂ) (κ : M →+* ℂ) {q : ℕ} (hq : 0 < q) {m n : ℤ}
    {P : L[X]} {Q : M[X]} (hP0 : P.coeff 0 ≠ 0) (hQ0 : Q.coeff 0 ≠ 0)
    (hP : IsPurePolynomial q m P.reverse) (hQ : IsPurePolynomial q n Q.reverse)
    (heq : unitaryEulerPolynomial (P.map ι) = unitaryEulerPolynomial (Q.map κ)) :
    P.map ι = (Q.map κ).comp (C (radius q (m - n) : ℂ) * X) := by
  rw [unitaryEulerPolynomial_eq_pure_substitution ι hP0 hP,
    unitaryEulerPolynomial_eq_pure_substitution κ hQ0 hQ] at heq
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hm : (radius q m : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hq' _).ne'
  have hratio : (radius q n : ℂ)⁻¹ * (radius q m : ℂ) = (radius q (m - n) : ℂ) := by
    have hreal : (q : ℝ) ^ (((m - n : ℤ) : ℝ) / 2) =
        (q : ℝ) ^ ((m : ℝ) / 2) / (q : ℝ) ^ ((n : ℝ) / 2) := by
      rw [Int.cast_sub, sub_div, Real.rpow_sub hq']
    rw [mul_comm, ← div_eq_mul_inv, ← Complex.ofReal_div]
    exact congrArg Complex.ofReal hreal.symm
  have hcomp := congrArg (fun f : ℂ[X] => f.comp (C (radius q m : ℂ) * X)) heq
  simpa only [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hm,
    hratio, map_one, one_mul, comp_X] using hcomp

section Families

variable {K : Type uK} [Field K] [NumberField K]
variable {L : Type uL} [Field L] [NumberField L]
variable {M : Type uM} [Field M] [NumberField M]
variable {excludedL : Finset (FinitePlace L)} {excludedM : Finset (FinitePlace M)}
variable {R : Collection.{uK, uL, uV} K L excludedL}
variable {U : Collection.{uK, uM, uW} K M excludedM}

/-- Two matching polynomial systems for the same collection agree at a place
    seen by a common member of the collection. -/
theorem MatchesOutside.polynomial_eq {A B : Finset (FinitePlace K)}
    {P Q : FinitePlace K → L[X]} (hP : MatchesOutside excludedL R A P)
    (hQ : MatchesOutside excludedL R B Q) (lam : {lam : FinitePlace L // lam ∉ excludedL})
    {v : FinitePlace K} (hA : v ∉ A) (hB : v ∉ B)
    (hchar : residueCharacteristic v ≠ residueCharacteristic lam.val) : P v = Q v := by
  let ι : L →+* FiniteCompletion L lam.val := NumberField.FinitePlace.embedding lam.val
  exact Polynomial.map_injective ι ι.injective
    ((hP lam v hA hchar).unique (hQ lam v hB hchar))

/-- The arithmetic polynomial has constant coefficient one wherever it
    matches an actual unramified representation. -/
theorem MatchesOutside.coeff_zero_eq_one {A : Finset (FinitePlace K)}
    {P : FinitePlace K → L[X]} (hP : MatchesOutside excludedL R A P)
    (lam : {lam : FinitePlace L // lam ∉ excludedL}) {v : FinitePlace K} (hA : v ∉ A)
    (hchar : residueCharacteristic v ≠ residueCharacteristic lam.val) : (P v).coeff 0 = 1 := by
  obtain ⟨_, g, _, hg⟩ := hP lam v hA hchar
  have h := (congrArg (fun f => f.coeff 0) hg).symm.trans
    (eulerPolynomial_coeff_zero (atFinitePlace v (R lam)) g)
  rw [coeff_map, ← map_one (NumberField.FinitePlace.embedding lam.val)] at h
  exact (NumberField.FinitePlace.embedding lam.val).injective h

/-- Any common Euler polynomial data may be used to evaluate weak association
    at the good places of a fixed member of the collection. -/
theorem IsWeaklyAssociatedToSpectrum.eventually_unitaryEuler_eq
    {ι : L →+* ℂ} {A : Finset (FinitePlace K)} {P : FinitePlace K → L[X]}
    {r : ℕ} {s : SpectralSystem (FinitePlace K) r}
    (h : IsWeaklyAssociatedToSpectrum ι excludedL R s) (hP : MatchesOutside excludedL R A P)
    (lam : {lam : FinitePlace L // lam ∉ excludedL}) :
    ∀ᶠ v in Filter.cofinite, v ∉ A →
      residueCharacteristic v ≠ residueCharacteristic lam.val → ∀ hv : v ∉ s.exceptional,
        unitaryEulerPolynomial ((P v).map ι) = s.eulerPolynomial v hv := by
  obtain ⟨B, Q, hQ, hunitary⟩ := h
  filter_upwards [B.eventually_cofinite_notMem, hunitary] with v hv hunitary
  intro hA hchar hs
  rw [hP.polynomial_eq hQ lam hA hv hchar]
  exact hunitary hs

/-- Weak association to the same numerical spectrum determines pure Euler
    polynomials up to the ratio of their radii. -/
theorem eventually_pureEuler_eq_comp_of_weakAssociation
    {ι : L →+* ℂ} {κ : M →+* ℂ} {r : ℕ} {s : SpectralSystem (FinitePlace K) r}
    {A B : Finset (FinitePlace K)} {P : FinitePlace K → L[X]} {Q : FinitePlace K → M[X]}
    {m n : ℤ}
    (hR : IsWeaklyAssociatedToSpectrum ι excludedL R s)
    (hU : IsWeaklyAssociatedToSpectrum κ excludedM U s)
    (hP : MatchesOutside excludedL R A P) (hQ : MatchesOutside excludedM U B Q)
    (hp : ∀ v ∉ A, IsPurePolynomial (residueCardinality v) m (P v).reverse)
    (hq : ∀ v ∉ B, IsPurePolynomial (residueCardinality v) n (Q v).reverse)
    (lam : {lam : FinitePlace L // lam ∉ excludedL})
    (mu : {mu : FinitePlace M // mu ∉ excludedM}) :
    ∀ᶠ v in Filter.cofinite,
      residueCharacteristic v ≠ residueCharacteristic lam.val →
      residueCharacteristic v ≠ residueCharacteristic mu.val →
      (P v).map ι = ((Q v).map κ).comp (C (radius (residueCardinality v) (m - n) : ℂ) * X) := by
  filter_upwards [hR.eventually_unitaryEuler_eq hP lam, hU.eventually_unitaryEuler_eq hQ mu,
    A.eventually_cofinite_notMem, B.eventually_cofinite_notMem,
    s.exceptional.eventually_cofinite_notMem] with v hRv hUv hAv hBv hsv
  intro hl hm
  have h0 : 0 < residueCardinality v := one_pos.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  exact pureEuler_eq_comp_of_unitaryEuler_eq ι κ h0
    (by rw [hP.coeff_zero_eq_one lam hAv hl]; exact one_ne_zero)
    (by rw [hQ.coeff_zero_eq_one mu hBv hm]; exact one_ne_zero)
    (hp v hAv) (hq v hBv) ((hRv hAv hl hsv).trans (hUv hBv hm hsv).symm)

variable [CompactSpace (AdeleQuotient K)]

/-- Weak association descends to the numerical spectrum of any supplied actual
    presentation of the weakly associated cuspidal class. -/
theorem weakAssociationToSpectrum_of_class
    {r : ℕ} {S : CuspidalOperatorRealization K r} {ι : L →+* ℂ}
    (h : S.isoClass.IsWeaklyAssociated.{uK, uL, uV, uP} ι excludedL R)
    (Q : CuspidalSpectralPresentation.{uK, uQ} S) :
    IsWeaklyAssociatedToSpectrum ι excludedL R Q.spectralSystem := by
  obtain ⟨s, hs, hR⟩ := h
  obtain ⟨P, rfl⟩ := (CuspidalOperatorRealization.IsoClass.hasSpectralSystem_iff S s).mp hs
  exact hR.of_sameEulerPolynomials (P.spectralSystem_sameEulerPolynomials Q)

end Families
end Langlands.GaloisRepresentation
