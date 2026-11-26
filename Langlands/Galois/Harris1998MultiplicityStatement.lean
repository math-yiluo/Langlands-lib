import Langlands.Galois.Harris1998ExistenceStatement
import Langlands.Automorphic.RegularHighestWeight
import Langlands.Automorphic.SupercuspidalComponent
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RepresentationTheory.Semisimple

/-!
# Harris (1998), Theorem 1.2, with multiplicity: Henniart's form

The theorem of Clozel and Kottwitz in the form of Henniart, *Sur la conjecture de
Langlands locale pour `GL_n`*, J. Théor. Nombres Bordeaux 13 (2001), §5.5,
printed p. 179: fix a prime `ℓ` and an isomorphism `ℂ ≅ ℚ̄_ℓ`. For a cuspidal `Π` of
`GL_n` over a CM field `E = E₀ K₀` that is conjugate self-dual, regular algebraic and
discrete series at a finite place split in `K₀`, there are `a ≥ 1` and a semisimple
`ℓ`-adic representation `Σ` of dimension `a n` with
`L(Σ_v, s) = L(Π_v, s + (n - 1)/2)^a` at almost every finite place.

The statement adds three hypotheses to Henniart's, those that the variant of the
construction of Harris (1998), Proposition 4.8, taking this theorem as input supplies:
`[E₀ : ℚ]` even (Henniart's fields contain the real quadratic field of his §5.1), a
supercuspidal component at a split place, and regular highest weight. The last one
is not supplied by the printed proposition, whose archimedean types are more general
(Harris's Remark, printed p. 202); the variant obtains it by choosing the infinity type
of the inducing Hecke character with exponents at distance at least `2`. It is an
unproved statement definition.
-/

noncomputable section

universe uE uL uV uW

namespace Langlands.GaloisRepresentation

open Polynomial Langlands.Global Langlands.Unramified

/-- Henniart's normalization of the unramified Euler polynomial: for Satake
parameters `α` of `GL_n` at a place with residue field of cardinality `q`, the
polynomial `∏ᵢ (1 - q^{-(n-1)/2} αᵢ X)`, whose inverse at `X = q^{-s}` is
`L(π_v, s + (n - 1)/2)`. Geometric Frobenius has the eigenvalues `q^{-(n-1)/2} αᵢ`. -/
def henniartEulerPolynomial {n : ℕ} (α : Eigenvalues n) (q : ℕ) : ℂ[X] :=
  α.eulerPolynomial.comp (C (((q : ℝ) ^ (-(((n : ℝ) - 1) / 2)) : ℝ) : ℂ) * X)

end Langlands.GaloisRepresentation

namespace Langlands.Automorphic

open Polynomial Langlands.Global Langlands.Unramified Langlands.GaloisRepresentation

variable {E : Type uE} [Field E] [NumberField E] [CompactSpace (AdeleQuotient E)]
variable {L : Type uL} [Field L] [TopologicalSpace L]

namespace CuspidalOperatorRealization.IsoClass

variable {r : ℕ}

/-- Henniart 2001, §5.5, for an irreducible cuspidal class `c` of rank `r + 1` and a
continuous representation `R` of `Gal(Ē/E)` with coefficients in a topological field
`L`, compared through a ring homomorphism `ιL : ℂ →+* L`: some actual spectral
presentation of `c` has a spectrum `s` such that at all but finitely many finite places
`v`, `R` is unramified at `v` and its Euler polynomial `det(1 - Frob_v X)` is the image
under `ιL` of the `a`-th power of Henniart's normalized Euler polynomial of `s`; that
is, `L(R_v, s) = L(c_v, s + (n - 1)/2)^a`. The universe `uW` is that of the local factor
carriers of the presentation. -/
def IsHenniartAssociatedAt (c : IsoClass E r) (ιL : ℂ →+* L)
    (R : Objects.{uE, uL, uV} E L) (a : ℕ) : Prop :=
  ∃ s : SpectralSystem (FinitePlace E) (r + 1),
    HasSpectralSystem.{uE, uW} c s ∧
      ∀ᶠ v in Filter.cofinite, ∀ hv : v ∉ s.exceptional,
        HasEulerPolynomialAt R v
          ((henniartEulerPolynomial (s.eigenvalues v hv) (residueCardinality v) ^ a).map ιL)

end CuspidalOperatorRealization.IsoClass

end Langlands.Automorphic

namespace Langlands.GaloisRepresentation

open Polynomial Langlands.Global Langlands.Unramified Langlands.Automorphic
open NumberField (IsTotallyReal IsTotallyComplex IsCMField)

/-- Harris (1998), Theorem 1.2, in the form with multiplicity of Henniart (2001), §5.5,
under three added hypotheses: even real degree, a supercuspidal component and regular
highest weight, those used by the variant of the construction of Harris's
Proposition 4.8 that takes this theorem as input.

Hypotheses: `E` is a CM field with intermediate fields `E₀` totally real of even
degree over `ℚ` and `K₀` imaginary quadratic such that `E = E₀ K₀`; `c` is an
irreducible cuspidal class of `GL_n(𝔸_E)` with `n = r + 1 ≥ 2`; `c` has regular
highest weight at infinity (the weights at each complex embedding are at distance at
least `2` from one another); `c` is conjugate self-dual for the CM conjugation; and `c`
has a supercuspidal local component at a finite place `v` whose residue characteristic
splits in `K₀`.

Conclusion: for every prime `ℓ` and every isomorphism `ιℓ : ℂ ≅ ℚ̄_ℓ`
(`PadicAlgCl ℓ`), there are an integer `a ≥ 1` and a continuous semisimple
representation `R` of `Gal(Ē/E)` on a `ℚ̄_ℓ`-vector space of dimension `a n` such that
at almost every finite place `v`, `R` is unramified with Euler polynomial
`ιℓ((∏ᵢ (1 - q_v^{-(n-1)/2} tᵢ X))^a)`, `tᵢ` the Satake parameters of `c` at `v`:
`L(R_v, s) = L(c_v, s + (n - 1)/2)^a` through `ιℓ`. -/
def Harris1998Theorem12CuspidalMultiplicityStatement : Prop :=
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
          Representation.IsSemisimpleRepresentation R.val.representation ∧
          CuspidalOperatorRealization.IsoClass.IsHenniartAssociatedAt.{uE, 0, uV, uW}
            c ιℓ.toRingHom R a

end Langlands.GaloisRepresentation
