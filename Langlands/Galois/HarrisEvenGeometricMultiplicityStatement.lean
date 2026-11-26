import Langlands.Galois.Harris1998MultiplicityStatement
import Langlands.Galois.HarrisEvenGeometricStatement
import Langlands.Galois.CyclotomicTwist
import Langlands.Galois.PureWeightParity

/-!
# The geometric endpoint of Harris's Theorem 1.2 with multiplicity

The output of the geometric construction (Clozel's transfer, Kottwitz's theorem in the
middle degree, and Clozel's twist of the middle-degree cohomology by the Galois character
of an abelian correcting character), for the hypotheses of
`Harris1998Theorem12CuspidalMultiplicityStatement`. Over a totally real base field the
correcting character is an Artin character (Clozel 1991, (5.31) and printed p. 142). In
the CM case of the endpoint (Clozel 1991, §5.3, printed pp. 142–144) it need not be one:
when `P = Σ_u P_u`, with `P_u` the integers of (5.33) at the archimedean places `u`, is
odd, Clozel's character `χ` is not an Artin character and the coefficient system has
weight one. The statement: for a prime `ℓ` and an isomorphism `ℂ ≅ ℚ̄_ℓ`, a continuous `ℓ`-adic representation whose Euler polynomials
are, at almost every place, the `a`-th powers of the unramified Euler polynomials in
Clozel's arithmetic normalization. No purity, no labelled Hodge–Tate weights and no
semisimplicity are asserted. The statement is beside the published
`HarrisEvenGeometricPowerStatement`, which stays. The twist by the `(n - 1)`-th power of
the cyclotomic character and a semisimplification reduce Henniart's form to it; that
reduction is proved here, with semisimplification a named input.
-/

noncomputable section

universe uK uE uL uV uW

namespace Langlands.Automorphic

open Polynomial Langlands.Global Langlands.Unramified Langlands.GaloisRepresentation

variable {E : Type uE} [Field E] [NumberField E] [CompactSpace (AdeleQuotient E)]
variable {L : Type uL} [Field L] [TopologicalSpace L]

namespace CuspidalOperatorRealization.IsoClass

variable {r : ℕ}

/-- Clozel's arithmetic normalization with multiplicity `a`: some actual spectral
presentation of `c` has a spectrum `s` such that at all but finitely many finite places
`v`, `R` is unramified at `v` with Euler polynomial the image under `ιL` of the `a`-th
power of the published `clozelEulerPolynomial (s.eigenvalues v hv) 1 q_v`, that is
`∏ᵢ (1 - q_v^{(n-1)/2} tᵢ X)`: `L(R_v, s) = L(c_v, s - (n - 1)/2)^a`. -/
def IsClozelAssociatedAt (c : IsoClass E r) (ιL : ℂ →+* L)
    (R : Objects.{uE, uL, uV} E L) (a : ℕ) : Prop :=
  ∃ s : SpectralSystem (FinitePlace E) (r + 1),
    HasSpectralSystem.{uE, uW} c s ∧
      ∀ᶠ v in Filter.cofinite, ∀ hv : v ∉ s.exceptional,
        HasEulerPolynomialAt R v
          ((clozelEulerPolynomial (s.eigenvalues v hv) 1 (residueCardinality v) ^ a).map ιL)

end CuspidalOperatorRealization.IsoClass

end Langlands.Automorphic

namespace Langlands.GaloisRepresentation

open Polynomial Langlands.Global Langlands.Unramified Langlands.Automorphic
open NumberField (IsTotallyReal IsTotallyComplex IsCMField)

/-- The geometric endpoint of the construction of Harris's Theorem 1.2 with
multiplicity (Henniart 2001, §5.5), without labelled Hodge–Tate weights, without purity
and without semisimplicity. The hypotheses are those of
`Harris1998Theorem12CuspidalMultiplicityStatement`: a CM field `E = E₀ K₀` with
`[E₀ : ℚ]` even, an irreducible cuspidal class `c` of rank `n = r + 1 ≥ 2` with regular
highest weight, conjugate self-dual and supercuspidal at a finite place split in `K₀`.
The conclusion: for every prime `ℓ` and isomorphism `ιℓ : ℂ ≅ ℚ̄_ℓ`, there are `a ≥ 1`
and a continuous representation `R` of `Gal(Ē/E)` of dimension `a n` over `ℚ̄_ℓ` whose
Euler polynomial at almost every place is `ιℓ((∏ᵢ (1 - q_v^{(n-1)/2} tᵢ X))^a)`. -/
def HarrisEvenGeometricMultiplicityStatement : Prop :=
  ∀ (E : Type uE) [Field E] [NumberField E] [IsCMField E] [CompactSpace (AdeleQuotient E)]
    (E₀ K₀ : IntermediateField ℚ E),
    IsTotallyReal E₀ → Module.finrank ℚ K₀ = 2 → IsTotallyComplex K₀ → E₀ ⊔ K₀ = ⊤ →
    Even (Module.finrank ℚ E₀) →
    ∀ (r : ℕ), 1 ≤ r → ∀ (c : CuspidalOperatorRealization.IsoClass E r) (v : FinitePlace E),
      c.HasRegularHighestWeight → c.IsConjugateSelfDual →
      CuspidalOperatorRealization.IsoClass.HasSupercuspidalComponent.{uE, uW} c v →
      Harris.IsSplitImaginaryQuadratic (residueCharacteristic v) K₀ →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιℓ : ℂ ≃+* PadicAlgCl ℓ),
        ∃ (a : ℕ) (R : Objects.{uE, 0, uV} E (PadicAlgCl ℓ)),
          0 < a ∧ R.val.rank = a * (r + 1) ∧
          CuspidalOperatorRealization.IsoClass.IsClozelAssociatedAt.{uE, 0, uV, uW}
            c ιℓ.toRingHom R a

/-- Semisimplification of continuous Galois representations, a named input: every
continuous finite-dimensional representation `A` of the absolute Galois group of a field
`K`, with coefficients in a topological field `L`, has a continuous semisimple
representation `B` of the same dimension with the same characteristic polynomial at
every element, on which every element acting trivially on `A` acts trivially. The
direct sum of the Jordan–Hölder factors of `A` is such a `B`. The statement is not
proved here. -/
def GaloisSemisimplificationStatement : Prop :=
  ∀ (K : Type uK) [Field K] (L : Type uL) [Field L] [TopologicalSpace L] [IsTopologicalRing L]
    (A : Objects.{uK, uL, uV} K L),
    ∃ B : Objects.{uK, uL, uV} K L,
      Representation.IsSemisimpleRepresentation B.val.representation ∧
      B.val.rank = A.val.rank ∧
      (∀ g, characteristicPolynomial B g = characteristicPolynomial A g) ∧
      ∀ g, A.val.representation g = 1 → B.val.representation g = 1

/-- Henniart's normalized Euler polynomial is Clozel's with the variable scaled by
`q^{-(n-1)}`, `n = r + 1`: the eigenvalues `q^{(n-1)/2} αᵢ` become `q^{-(n-1)/2} αᵢ`. -/
theorem henniartEulerPolynomial_eq_clozel_comp {r : ℕ} (α : Eigenvalues (r + 1)) {q : ℕ}
    (hq : 0 < q) :
    henniartEulerPolynomial α q =
      (clozelEulerPolynomial α 1 q).comp (C ((q : ℂ) ^ (-(r : ℤ))) * X) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hn : ((r + 1 : ℕ) : ℝ) - 1 = r := by push_cast; ring
  have hscal : (((q : ℝ) ^ ((((r + 1 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * (q : ℂ) ^ (-(r : ℤ)) =
      (((q : ℝ) ^ (-((((r + 1 : ℕ) : ℝ) - 1) / 2)) : ℝ) : ℂ) := by
    have hz : (q : ℂ) ^ (-(r : ℤ)) = (((q : ℝ) ^ (-(r : ℝ)) : ℝ) : ℂ) := by
      rw [Real.rpow_neg hq'.le, Real.rpow_natCast, zpow_neg, zpow_natCast]
      push_cast
      ring
    rw [hz, ← Complex.ofReal_mul, ← Real.rpow_add hq', hn]
    congr 2
    ring
  rw [henniartEulerPolynomial, clozelEulerPolynomial, Eigenvalues.power_one, comp_assoc]
  congr 1
  rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, hscal]

/-- A representation with the same characteristic polynomials, trivial wherever the
first one is trivial, has the same Euler polynomial at every place where the first one
has it. -/
theorem HasEulerPolynomialAt.of_charpoly_eq {K : Type uK} [Field K] [NumberField K]
    {L : Type uL} [Field L] [TopologicalSpace L] {A B : Objects.{uK, uL, uV} K L}
    (hchar : ∀ g, characteristicPolynomial B g = characteristicPolynomial A g)
    (htriv : ∀ g, A.val.representation g = 1 → B.val.representation g = 1)
    {v : FinitePlace K} {P : L[X]} (hA : HasEulerPolynomialAt A v P) :
    HasEulerPolynomialAt B v P := by
  obtain ⟨hI, g, hg, hP⟩ := hA
  refine ⟨fun i => htriv _ (hI i), g, hg, ?_⟩
  rw [← hP, atFinitePlace, atFinitePlace, eulerPolynomial, eulerPolynomial,
    characteristicPolynomial_pullback, characteristicPolynomial_pullback, hchar]

/-- The geometric endpoint and semisimplification give Harris's Theorem 1.2 with
multiplicity in Henniart's normalization. -/
def Harris1998MultiplicityOfEvenGeometricStatement : Prop :=
  HarrisEvenGeometricMultiplicityStatement.{uE, uV, uW} →
    GaloisSemisimplificationStatement.{uE, 0, uV} →
    Harris1998Theorem12CuspidalMultiplicityStatement.{uE, uV, uW}

/-- Proof of `Harris1998MultiplicityOfEvenGeometricStatement`: twist the representation
of the endpoint by the `(n - 1)`-th power of the cyclotomic character (the published
`geometricCyclotomicPower` with exponent `-(n - 1)`), which scales the Euler variable by
`q_v^{-(n-1)}` at the places not above `ℓ`
(`HasEulerPolynomialAt.geometricCyclotomicTwist`), and take a semisimplification. -/
theorem harris1998Multiplicity_of_evenGeometric :
    Harris1998MultiplicityOfEvenGeometricStatement.{uE, uV, uW} := by
  intro hgeo hss E _ _ _ _ E₀ K₀ hE₀ h2 hK₀ hsup heven r hr c v hreg hcsd hsc hsplit ℓ _ ιℓ
  obtain ⟨a, W, ha, hrank, s, hs, hW⟩ :=
    hgeo E E₀ K₀ hE₀ h2 hK₀ hsup heven r hr c v hreg hcsd hsc hsplit ℓ ιℓ
  let φ : ℚ_[ℓ] →+* PadicAlgCl ℓ := algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)
  have hφ : Continuous φ := continuous_algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)
  let W' : Objects.{uE, 0, uV} E (PadicAlgCl ℓ) :=
    twist (geometricCyclotomicPower E ℓ φ (-(r : ℤ)))
      (continuous_geometricCyclotomicPower E ℓ φ hφ (-(r : ℤ))) W
  obtain ⟨B, hBss, hBrank, hBchar, hBtriv⟩ := hss E (PadicAlgCl ℓ) W'
  refine ⟨a, B, ha, hBrank.trans hrank, hBss, s, hs, ?_⟩
  have hℓ : ∀ᶠ w : FinitePlace E in Filter.cofinite, residueCharacteristic w ≠ ℓ := by
    filter_upwards [eventually_residueCharacteristic_not_dvd (K := E) ℓ
      (Fact.out : ℓ.Prime).ne_zero] with w hw heq
    exact hw (heq ▸ dvd_refl _)
  filter_upwards [hW, hℓ] with w hw hwℓ hws
  have hq : 0 < residueCardinality w :=
    Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors
      ⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩)
  have htw := (hw hws).geometricCyclotomicTwist ℓ φ hφ (-(r : ℤ)) hwℓ
  refine HasEulerPolynomialAt.of_charpoly_eq hBchar hBtriv ?_
  convert htw using 1
  rw [henniartEulerPolynomial_eq_clozel_comp _ hq, ← pow_comp, Polynomial.map_comp,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, map_zpow₀, map_natCast]

end Langlands.GaloisRepresentation
