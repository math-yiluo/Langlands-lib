import Langlands.Galois.FamilySum
import Langlands.Galois.UnitaryNormalization
import Langlands.Automorphic.CuspidalSpectralPresentation

/-!
# Weak association of compatible Galois families with cuspidal spectra

Harris (1998), Definition 1.1, with the unitary normalization of p.184 and
Harris (1999), (5.6): a compatible family of genuine `λ`-adic representations
is weakly associated to an automorphic representation when, outside a finite
set of places, the unitary normalization of the common Frobenius Euler
polynomial equals the normalized Euler polynomial of the automorphic
representation.

Only almost-everywhere unramified matching is defined here. Nothing is said
about ramified places, and no existence of an associated family is asserted.
-/

noncomputable section

universe uE uL uV uW uJ uK

namespace Langlands.GaloisRepresentation

open Polynomial Langlands.Global Langlands.Unramified

variable {E : Type uE} [Field E] [NumberField E]
variable {L : Type uL} [Field L] [NumberField L]

/-- The unitary normalization (at the complex embedding `ι`) of the supplied
coefficient-field Euler polynomials agrees with the Euler polynomials of the
spectral system at all but finitely many places. -/
def UnitaryMatchesSpectrum (ι : L →+* ℂ) (P : FinitePlace E → L[X]) {n : ℕ}
    (s : SpectralSystem (FinitePlace E) n) : Prop :=
  ∀ᶠ v in Filter.cofinite, ∀ hv : v ∉ s.exceptional,
    unitaryEulerPolynomial ((P v).map ι) = s.eulerPolynomial v hv

/-- Harris (1998), Definition 1.1, for a numerical spectrum: the collection is
compatible with common Euler polynomials `P_v` outside a finite set `S`, and
the unitary normalization of `P_v` at `ι` is the Euler polynomial of `s` at
all but finitely many places. -/
def IsWeaklyAssociatedToSpectrum (ι : L →+* ℂ) (excluded : Finset (FinitePlace L))
    (R : Collection.{uE, uL, uV} E L excluded) {n : ℕ}
    (s : SpectralSystem (FinitePlace E) n) : Prop :=
  ∃ (S : Finset (FinitePlace E)) (P : FinitePlace E → L[X]),
    MatchesOutside excluded R S P ∧ UnitaryMatchesSpectrum ι P s

/-- The direct sum `⊕ₖ Rₖ` of a finite family of collections, all with the same
excluded coefficient places, is weakly associated to the spectrum `s`: the
summands are compatible with common Euler polynomials `Pₖ` outside one finite
set, and the unitary normalization of the product `∏ₖ Pₖ`, which is the Euler
polynomial of the direct sum, matches `s` at almost all places. -/
def IsSumWeaklyAssociatedToSpectrum (ι : L →+* ℂ) (excluded : Finset (FinitePlace L))
    {K : Type uK} [Fintype K] (R : K → Collection.{uE, uL, uV} E L excluded) {n : ℕ}
    (s : SpectralSystem (FinitePlace E) n) : Prop :=
  ∃ (S : Finset (FinitePlace E)) (P : K → FinitePlace E → L[X]),
    (∀ k, MatchesOutside excluded (R k) S (P k)) ∧
      UnitaryMatchesSpectrum ι (fun v => ∏ k, P k v) s

omit [NumberField E] [NumberField L] in
theorem UnitaryMatchesSpectrum.of_sameEulerPolynomials {ι : L →+* ℂ}
    {P : FinitePlace E → L[X]} {n m : ℕ} {s : SpectralSystem (FinitePlace E) n}
    {t : SpectralSystem (FinitePlace E) m} (hs : UnitaryMatchesSpectrum ι P s)
    (hst : s.SameEulerPolynomials t) : UnitaryMatchesSpectrum ι P t := by
  filter_upwards [hs, hst, s.exceptional.eventually_cofinite_notMem] with v hv hvst hvs
  intro hvt
  rw [hv hvs, hvst hvs hvt]

/-- Weak association depends only on the Euler polynomials of the spectrum
outside a finite set. -/
theorem IsWeaklyAssociatedToSpectrum.of_sameEulerPolynomials {ι : L →+* ℂ}
    {excluded : Finset (FinitePlace L)} {R : Collection.{uE, uL, uV} E L excluded}
    {n m : ℕ} {s : SpectralSystem (FinitePlace E) n} {t : SpectralSystem (FinitePlace E) m}
    (hs : IsWeaklyAssociatedToSpectrum ι excluded R s) (hst : s.SameEulerPolynomials t) :
    IsWeaklyAssociatedToSpectrum ι excluded R t := by
  obtain ⟨S, P, hP, hm⟩ := hs
  exact ⟨S, P, hP, hm.of_sameEulerPolynomials hst⟩

/-- Weak association implies compatibility of the collection. -/
theorem IsWeaklyAssociatedToSpectrum.isCompatible {ι : L →+* ℂ}
    {excluded : Finset (FinitePlace L)} {R : Collection.{uE, uL, uV} E L excluded}
    {n : ℕ} {s : SpectralSystem (FinitePlace E) n}
    (hs : IsWeaklyAssociatedToSpectrum ι excluded R s) : IsCompatible excluded R := by
  obtain ⟨S, P, hP, -⟩ := hs
  exact ⟨S, P, hP⟩

/-- A single collection is weakly associated exactly when the one-summand
family is. -/
theorem isSumWeaklyAssociatedToSpectrum_unique_iff (ι : L →+* ℂ)
    (excluded : Finset (FinitePlace L)) {K : Type uK} [Unique K]
    (R : K → Collection.{uE, uL, uV} E L excluded) {n : ℕ}
    (s : SpectralSystem (FinitePlace E) n) :
    IsSumWeaklyAssociatedToSpectrum ι excluded R s ↔
      IsWeaklyAssociatedToSpectrum ι excluded (R default) s := by
  constructor
  · rintro ⟨S, P, hP, hm⟩
    refine ⟨S, P default, hP default, ?_⟩
    simpa only [Fintype.prod_unique] using hm
  · rintro ⟨S, P, hP, hm⟩
    refine ⟨S, fun _ => P, fun k => ?_, ?_⟩
    · rw [Unique.eq_default k]
      exact hP
    · simpa only [Fintype.prod_unique] using hm

/-- The Euler polynomial of a collection at a place where it matches a common
polynomial is nonzero, so the common polynomial itself is nonzero. -/
theorem MatchesOutside.ne_zero {excluded : Finset (FinitePlace L)}
    {R : Collection.{uE, uL, uV} E L excluded} {S : Finset (FinitePlace E)}
    {P : FinitePlace E → L[X]} (hP : MatchesOutside excluded R S P)
    (lam : {lam : FinitePlace L // lam ∉ excluded}) {v : FinitePlace E} (hv : v ∉ S)
    (hchar : residueCharacteristic v ≠ residueCharacteristic lam.val) : P v ≠ 0 := by
  intro h0
  obtain ⟨-, g, -, hg⟩ := hP lam v hv hchar
  have hc := eulerPolynomial_coeff_zero (atFinitePlace v (R lam)) g
  rw [hg, h0, Polynomial.map_zero, Polynomial.coeff_zero] at hc
  exact zero_ne_one hc

end Langlands.GaloisRepresentation

namespace Langlands.Automorphic

open Langlands.Global Langlands.Unramified Langlands.GaloisRepresentation

variable {E : Type uE} [Field E] [NumberField E] [CompactSpace (AdeleQuotient E)]
variable {L : Type uL} [Field L] [NumberField L]

namespace CuspidalOperatorRealization.IsoClass

variable {r : ℕ}

/-- Harris (1998), Definition 1.1, for an irreducible cuspidal class `c` of
rank `r + 1`: some actual spectral presentation of `c` has a spectrum to which
the collection is weakly associated. The universe `uW` is that of the local
factor carriers of the presentation, as in `HasSpectralSystem`. -/
def IsWeaklyAssociated (c : IsoClass E r) (ι : L →+* ℂ)
    (excluded : Finset (FinitePlace L)) (R : Collection.{uE, uL, uV} E L excluded) : Prop :=
  ∃ s : SpectralSystem (FinitePlace E) (r + 1),
    HasSpectralSystem.{uE, uW} c s ∧ IsWeaklyAssociatedToSpectrum ι excluded R s

/-- The direct sum `⊕ₖ Rₖ` of a finite family of collections is weakly
associated to the cuspidal class `c` (Harris 1998, Definition 1.1, with the
family a sum of collections as on p.183). -/
def IsSumWeaklyAssociated (c : IsoClass E r) (ι : L →+* ℂ)
    (excluded : Finset (FinitePlace L)) {K : Type uK} [Fintype K]
    (R : K → Collection.{uE, uL, uV} E L excluded) : Prop :=
  ∃ s : SpectralSystem (FinitePlace E) (r + 1),
    HasSpectralSystem.{uE, uW} c s ∧ IsSumWeaklyAssociatedToSpectrum ι excluded R s

end CuspidalOperatorRealization.IsoClass

namespace PositiveRankCuspidalClass

/-- Harris (1998), Definition 1.1, for an automorphic representation given by
its cuspidal spectrum: a finite family `c` of cuspidal classes of `GL_{nⱼ}`.
The direct sum `⊕ₖ Rₖ` of a finite family of collections is weakly associated
to it when each `cⱼ` has an actual spectral presentation with spectrum `sⱼ` and
the direct sum is weakly associated to the concatenated spectrum, whose Euler
polynomials are the products of those of the `sⱼ`. -/
def IsSpectrumWeaklyAssociated {J : Type uJ} [Fintype J]
    (c : J → PositiveRankCuspidalClass E) (ι : L →+* ℂ)
    (excluded : Finset (FinitePlace L)) {K : Type uK} [Fintype K]
    (R : K → Collection.{uE, uL, uV} E L excluded) : Prop :=
  ∃ s : ∀ j, SpectralSystem (FinitePlace E) (c j).rank,
    (∀ j, HasSpectralSystem.{uE, uW} (c j) (s j)) ∧
      IsSumWeaklyAssociatedToSpectrum ι excluded R (SpectralSystem.finiteSum s)

end PositiveRankCuspidalClass

end Langlands.Automorphic
