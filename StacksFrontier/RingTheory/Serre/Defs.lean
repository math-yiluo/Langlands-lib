module

import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.LinearAlgebra.Matrix.CommSemiring

public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Depth.Nakayama
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The Serre conditions

A Noetherian ring `R` satisfies `(Rₖ)` when every prime of height at most `k` has regular
localization, and `(Sₖ)` when at every prime `𝔭` the depth of `R_𝔭` — or, for a finite module
`M`, the depth of `M_𝔭` — is at least `min(k, dim)`. Both conditions are defined here, following
Definition 031P, on top of the depth of a module along an ideal.

Two lemmas about small `k` follow. At `k = 1` the condition on a finite module `M` over a
Noetherian ring says exactly that `M` has no *embedded* associated prime, that is, that every
associated prime of `M` is minimal among the associated primes of `M`: an embedded associated
prime `𝔭 ⊋ 𝔮 ∈ Ass(M)` puts `𝔭R_𝔭` in `Ass(M_𝔭)` and `𝔮` in `Supp(M_𝔭)`, so `depth(M_𝔭) = 0`
while `dim Supp(M_𝔭) ≥ 1`; conversely at a prime where `(S₁)` fails `𝔭` is associated to `M`, and
so is a minimal prime of `Supp(M)` strictly inside it, exhibiting `𝔭` as embedded (Lemma 031Q).

At `k = 2` the condition is what Serre's criterion gives a Noetherian normal domain `R` with
fraction field `K`, and Lemma 031T is what it says about the *divisorial* quotients of `R` — the
quotients by the ideals `R ∩ xR` cut out by an element `x` of `K`. Their associated primes are
minimal among themselves and of height one, and `R` is the intersection, inside `K`, of its
localizations at the height-one primes.

## Main definitions

* `HasPropertyRk`: property `(Rₖ)`, regularity in codimension at most `k`.
* `PropertySkRing`, `PropertySkModule`: property `(Sₖ)` for a ring and for a finite module.
* `fibreRing`: the fibre ring `S ⊗_R κ(𝔭)` of an `R`-algebra `S` at a prime `𝔭` of `R`.

## Main results

* `Module.forall_minimal_mem_associatedPrimes_iff_min_one_supportDim_le_depth`: a finite module
  over a Noetherian ring has no embedded associated prime if and only if it satisfies `(S₁)`.
* `associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot`: for a Noetherian
  normal domain `R` with fraction field `K`, (1) every associated prime of `R/aR` with `a ≠ 0` is
  minimal among them and of height `1`, (2) `R` is the intersection of the subalgebras `R_𝔭 ⊆ K`
  over the height-one primes `𝔭`, and (3) the same as (1) for `R/(R ∩ xR)` with `0 ≠ x ∈ K`.

## Implementation notes

Property `(Rₖ)` uses no finiteness of the ring, so `HasPropertyRk` is stated over an arbitrary
commutative ring. The two `(Sₖ)` predicates keep the Noetherian hypothesis of Definition 031P.
Their conventions are Noetherian-local ones: `moduleDepth` is `0` on the zero module where the
source writes `∞`, and `unbotD 0` reads the source's `dim(∅) = -∞` as `0`, so the spelling agrees
with Definition 031P for a finite module over a Noetherian local ring. `fibreRing` is
`Ideal.Fiber` with the two tensor factors interchanged.

In `Module.forall_minimal_mem_associatedPrimes_iff_min_one_supportDim_le_depth`, property `(S₁)`
is spelled out as the inequality `min{1, dim Supp(M_𝔭)} ≤ depth_{𝔭R_𝔭}(M_𝔭)` rather than as
`PropertySkModule R M 1`: the predicates above are phrased with `moduleDepth` and
`moduleSupportDim`, which are stated for a local ring and truncate the dimension of the empty
support to `0`, while the lemma is phrased with `Module.depth` and `Module.supportDim`, whose
conventions `depth(0) = ⊤` and `dim(∅) = ⊥` are the source's `∞` and `-∞`. The inequality is
therefore read in `WithBot ℕ∞`, and the primes off the support impose no condition, so the
statement may quantify over all of `PrimeSpectrum R`, as Definition 0AAH does. Having no
embedded associated prime is spelled with `Minimal`, and the localizations are the canonical
models `Localization.AtPrime 𝔭` and `LocalizedModule 𝔭.primeCompl M`.

In `associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot` a normal domain is
`IsDomain` plus `IsIntegrallyClosed`, and heights are `Ideal.height`, taken in `R` and not in a
localization. Item (2) is the equality `⨅ 𝔭, R_𝔭 = ⊥` in the lattice of `R`-subalgebras of `K`,
each `R_𝔭` being `Localization.subalgebra.ofField` and `⊥` the image of `algebraMap R K`, as in
`IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot` and
`PrimeSpectrum.iInf_localization_eq_bot`. When `R` is a field the intersection is empty, and
`⊤ = ⊥` holds because `algebraMap R K` is then surjective. The ideal `R ∩ xR` is the pullback
`(Submodule.span R {x}).comap (Algebra.linearMap R K)` of the `R`-submodule `xR` of `K`; for
`x = algebraMap R K a` it equals `Ideal.span {a}`, so item (1) is the case `x ∈ R` of item (3),
though not definitionally.

## References

* [StacksProject 031P](https://stacks.math.columbia.edu/tag/031P)
* [StacksProject 031Q](https://stacks.math.columbia.edu/tag/031Q)
* [StacksProject 031T](https://stacks.math.columbia.edu/tag/031T)
-/

@[expose] public section

/-! ### `(S₁)` and embedded associated primes -/

namespace Module

section

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

end

end Module

/-! ### Divisorial quotients of a Noetherian normal domain -/

/-- **The stabiliser of a nonzero ideal is the ring itself.** In a Noetherian integrally closed
domain `R` with fraction field `K`, an element `x` of `K` with `x𝔭 ⊆ 𝔭` for some nonzero ideal
`𝔭` of `R` already lies in `R`. -/
private theorem mem_bot_of_mul_ideal_le {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {p : Ideal R} (hp : p ≠ ⊥) {x : K}
    (hx : ∀ r ∈ p, ∃ s ∈ p, x * algebraMap R K r = algebraMap R K s) :
    x ∈ (⊥ : Subalgebra R K) := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff p).mp hp
  have hxi : IsIntegral R x := by
    refine isIntegral_of_smul_mem_submodule (Submodule.map (Algebra.linearMap R K) p)
      ((Submodule.ne_bot_iff _).mpr ⟨algebraMap R K v, ⟨v, hv, rfl⟩, by simpa using hv0⟩)
      ((IsNoetherian.noetherian p).map _) x ?_
    rintro y ⟨r, hr, rfl⟩
    obtain ⟨s, hs, hrs⟩ := hx r hr
    exact ⟨s, hs, by simpa [Algebra.smul_def] using hrs.symm⟩
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxi
  exact Algebra.mem_bot.mpr ⟨w, hw⟩

/-- **Normality in elementary form.** If `𝔭` is a nonzero ideal of a Noetherian normal domain,
`a ≠ 0`, and `b𝔭 ⊆ a𝔭`, then `a ∣ b`. -/
private theorem dvd_of_mul_ideal_le {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] {p : Ideal R} (hp : p ≠ ⊥) {a b : R} (ha : a ≠ 0)
    (h : ∀ r ∈ p, ∃ s ∈ p, r * b = a * s) : a ∣ b := by
  have hane : algebraMap R (FractionRing R) a ≠ 0 := by simp [ha]
  have key : ∀ r ∈ p, ∃ s ∈ p, algebraMap R (FractionRing R) b / algebraMap R (FractionRing R) a
      * algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) s := by
    intro r hr
    obtain ⟨s, hs, hrs⟩ := h r hr
    have hrs' : algebraMap R (FractionRing R) r * algebraMap R (FractionRing R) b
        = algebraMap R (FractionRing R) a * algebraMap R (FractionRing R) s := by
      rw [← map_mul, ← map_mul, hrs]
    exact ⟨s, hs, by field_simp; linear_combination hrs'⟩
  obtain ⟨w, hw⟩ := Algebra.mem_bot.mp (mem_bot_of_mul_ideal_le hp key)
  refine ⟨w, IsFractionRing.injective R (FractionRing R) ?_⟩
  rw [map_mul, hw]
  field_simp

/-- The height of a prime is the height of the maximal ideal of the localization at it. -/
private theorem height_maximalIdeal_localization {R : Type*} [CommRing R] (p : Ideal R)
    [p.IsPrime] : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).height = p.height := by
  rw [← IsLocalization.height_under p.primeCompl
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)), Localization.AtPrime.under_maximalIdeal]

/-- **Krull's principal ideal theorem, localized.** A prime `𝔭` of a Noetherian ring which becomes
principal after inverting the complement of `𝔭` has height at most `1`: it suffices that some
`y ∈ 𝔭` divide every `r ∈ 𝔭` up to a factor `d ∉ 𝔭`. -/
private theorem height_le_one_of_forall_mul_eq {R : Type*} [CommRing R] [IsNoetherianRing R]
    {p : Ideal R} [p.IsPrime] {y : R} (hy : y ∈ p)
    (h : ∀ r ∈ p, ∃ d ∉ p, ∃ e : R, r * d = y * e) : p.height ≤ 1 := by
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime p)
      = Ideal.span {algebraMap R (Localization.AtPrime p) y} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    refine le_antisymm ?_ (Ideal.span_le.mpr (by simpa using Ideal.mem_map_of_mem _ hy))
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    obtain ⟨d, hd, e, hre⟩ := h r hr
    obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.AtPrime p) (⟨d, hd⟩ : p.primeCompl)
    simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
    refine ⟨algebraMap R (Localization.AtPrime p) e * (↑u⁻¹ : Localization.AtPrime p), ?_⟩
    rw [← mul_assoc]
    refine (Units.eq_mul_inv_iff_mul_eq u).mpr ?_
    rw [hu, ← map_mul, ← map_mul]
    exact congrArg _ hre
  have : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).IsPrincipal := ⟨_, hmax⟩
  rw [← height_maximalIdeal_localization p]
  exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing
    (IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl)

/-- In `R ⧸ aR`, the colon ideal `(0 : b)` consists of the `r : R` with `a ∣ r * b`. -/
private theorem mem_colon_singleton_quotient_iff {R : Type*} [CommRing R] {a b : R} {r : R} :
    r ∈ (⊥ : Submodule R (R ⧸ Ideal.span {a})).colon {Ideal.Quotient.mk (Ideal.span {a}) b} ↔
      a ∣ r * b := by
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot,
    show r • Ideal.Quotient.mk (Ideal.span {a}) b = Ideal.Quotient.mk (Ideal.span {a}) (r * b)
      from rfl,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- An associated prime of `R ⧸ aR` is a colon ideal `(aR : b)` with `b ∉ aR`: it consists of the
`r : R` with `a ∣ r * b`. -/
private theorem exists_forall_mem_iff_dvd_mul {R : Type*} [CommRing R] [IsNoetherianRing R]
    {a : R} {p : Ideal R} (hp : p ∈ associatedPrimes R (R ⧸ Ideal.span {a})) :
    ∃ b : R, ¬ a ∣ b ∧ ∀ r : R, r ∈ p ↔ a ∣ r * b := by
  obtain ⟨-, x0, hx0⟩ := isAssociatedPrime_iff.mp hp
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x0
  have hmem : ∀ r : R, r ∈ p ↔ a ∣ r * b := fun r => by
    rw [hx0, mem_colon_singleton_quotient_iff]
  exact ⟨b, fun hab => hp.isPrime.ne_top ((Ideal.eq_top_iff_one p).mpr
    ((hmem 1).mpr (by simpa using hab))), hmem⟩

/-- In a Noetherian normal domain `R`, every associated prime of `R/aR` with `a ≠ 0` has
height `1`. -/
private theorem height_eq_one_of_mem_associatedPrimes {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] {a : R} (ha : a ≠ 0) {p : Ideal R}
    (hp : p ∈ associatedPrimes R (R ⧸ Ideal.span {a})) : p.height = 1 := by
  have hpp : p.IsPrime := hp.isPrime
  obtain ⟨b, hab, hmem⟩ := exists_forall_mem_iff_dvd_mul hp
  have hap : a ∈ p := (hmem a).mpr (dvd_mul_right a b)
  have hpne : p ≠ ⊥ := fun h => ha (by simpa [h] using hap)
  refine le_antisymm ?_ ?_
  · obtain ⟨y, hy, d, hd, hyd⟩ : ∃ y ∈ p, ∃ d ∉ p, y * b = a * d := by
      by_contra hcon
      refine hab (dvd_of_mul_ideal_le hpne ha fun r hr => ?_)
      obtain ⟨e, he⟩ := (hmem r).mp hr
      exact ⟨e, not_not.mp fun hen => hcon ⟨r, hr, e, hen, he⟩, he⟩
    refine height_le_one_of_forall_mul_eq hy fun r hr => ⟨d, hd, ?_⟩
    obtain ⟨e, he⟩ := (hmem r).mp hr
    exact ⟨e, mul_left_cancel₀ ha (by linear_combination y * he - r * hyd)⟩
  · rwa [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]

/-- A set of primes all of whose members have height `1` has no strict inclusions: every member is
minimal in it, and of course of height `1`. -/
private theorem minimal_and_height_eq_one {R : Type*} [CommRing R] {S : Set (Ideal R)}
    (hS : ∀ q ∈ S, q.IsPrime ∧ q.height = 1) {p : Ideal R} (hp : p ∈ S) :
    Minimal (· ∈ S) p ∧ p.height = 1 := by
  obtain ⟨hpp, hph⟩ := hS p hp
  refine ⟨⟨hp, fun q hq hqp => (hqp.eq_or_lt.resolve_right fun hlt => ?_).ge⟩, hph⟩
  obtain ⟨hqp', hqh⟩ := hS q hq
  have hle := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hqh, hph, one_add_one_eq_two] at hle
  exact absurd hle (by decide)

/-- The ideal `R ∩ xR` cut out by `x = n / d` in the fraction field, `d ≠ 0`: an element `r` of
`R` lies in it exactly when `n ∣ r * d`. -/
private theorem mem_comap_span_singleton_div {R : Type*} [CommRing R] (K : Type*)
    [Field K] [Algebra R K] [IsFractionRing R K] {n d : R} (hd : d ≠ 0) (r : R) :
    r ∈ ((Submodule.span R {algebraMap R K n / algebraMap R K d}).comap
      (Algebra.linearMap R K) : Ideal R) ↔ n ∣ r * d := by
  have hdne : algebraMap R K d ≠ 0 := by simp [hd]
  simp only [Submodule.mem_comap, Algebra.linearMap_apply, Submodule.mem_span_singleton,
    Algebra.smul_def]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, IsFractionRing.injective R K ?_⟩
    field_simp at hc
    rw [map_mul, map_mul]
    linear_combination -hc
  · rintro ⟨c, hc⟩
    have hc' : algebraMap R K r * algebraMap R K d = algebraMap R K n * algebraMap R K c := by
      rw [← map_mul, ← map_mul, hc]
    exact ⟨c, by field_simp; linear_combination -hc'⟩

/-- An element of the fraction field whose denominators can be chosen outside every prime of
height `1` lies in `R`. -/
private theorem mem_bot_of_forall_height_eq_one {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] {z : K}
    (hz : ∀ q : Ideal R, q.IsPrime → q.height = 1 →
      ∃ m s : R, s ∉ q ∧ z * algebraMap R K s = algebraMap R K m) :
    z ∈ (⊥ : Subalgebra R K) := by
  by_contra hnot
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) z
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdne : algebraMap R K d ≠ 0 := by simp [hd0]
  have hmk : Ideal.Quotient.mk (Ideal.span {d}) n ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    rintro ⟨c, rfl⟩
    exact hnot (Algebra.mem_bot.mpr ⟨c, by rw [map_mul]; field_simp⟩)
  obtain ⟨P, hP, hPle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hmk
  obtain ⟨m, s, hs, hzs⟩ := hz P hP.isPrime (height_eq_one_of_mem_associatedPrimes hd0 hP)
  refine hs (hPle ?_)
  rw [mem_colon_singleton_quotient_iff]
  refine ⟨m, IsFractionRing.injective R K ?_⟩
  rw [map_mul, map_mul]
  field_simp at hzs
  linear_combination hzs

/-- Let `R` be a Noetherian normal domain with fraction field `K`. Then
(1) for every nonzero `a : R` each associated prime of `R/aR` is minimal among the associated
primes of `R/aR` — that is, `R/aR` has no embedded primes — and has height `1`;
(2) `R` is the intersection, inside `K`, of the subalgebras `R_𝔭` over the primes `𝔭` of height
`1`; and (3) the same as (1) for the ideal `R ∩ xR` attached to a nonzero `x : K`. -/
@[stacks 031T "A normal domain is `IsDomain` plus `IsIntegrallyClosed`, as in Definition 0309; \
  having no embedded primes is spelled with `Minimal`, as in tags 02M6 and 031Q; item (2) is the \
  equality `⨅ 𝔭, R_𝔭 = ⊥` of `R`-subalgebras of `K`, as in \
  `IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot`; and `R ∩ xR` is the pullback of \
  `xR ⊆ K` along `Algebra.linearMap R K`. See the module docstring."]
public theorem associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    (∀ a : R, a ≠ 0 → ∀ p ∈ associatedPrimes R (R ⧸ Ideal.span {a}),
        Minimal (· ∈ associatedPrimes R (R ⧸ Ideal.span {a})) p ∧ p.height = 1) ∧
      ((⨅ p : PrimeSpectrum R, ⨅ _ : p.asIdeal.height = 1,
          Localization.subalgebra.ofField K _ p.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥) ∧
      (∀ x : K, x ≠ 0 →
        ∀ p ∈ associatedPrimes R
            (R ⧸ ((Submodule.span R {x}).comap (Algebra.linearMap R K) : Ideal R)),
          Minimal (· ∈ associatedPrimes R
              (R ⧸ ((Submodule.span R {x}).comap (Algebra.linearMap R K) : Ideal R))) p ∧
            p.height = 1) := by
  refine ⟨fun a ha p hp => minimal_and_height_eq_one (fun q hq =>
      ⟨hq.isPrime, height_eq_one_of_mem_associatedPrimes ha hq⟩) hp, ?_, ?_⟩
  · refine bot_unique fun z hz => mem_bot_of_forall_height_eq_one K fun P hPp hPh => ?_
    obtain ⟨m, s, hs, hzs⟩ := Algebra.mem_iInf.mp (Algebra.mem_iInf.mp hz ⟨P, hPp⟩) hPh
    have hsne : algebraMap R K s ≠ 0 := by
      simp [show s ≠ 0 from fun h => hs (h ▸ P.zero_mem)]
    exact ⟨m, s, hs, by rw [hzs]; field_simp⟩
  · intro x hx p hp
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hn0 : n ≠ 0 := by rintro rfl; simp at hx
    have hker : LinearMap.ker ((Submodule.mkQ (Ideal.span {n})).comp (LinearMap.mulRight R d))
        = ((Submodule.span R {algebraMap R K n / algebraMap R K d}).comap
          (Algebra.linearMap R K) : Ideal R) := by
      ext r
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.mulRight_apply, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
        mem_comap_span_singleton_div K hd0 r]
    have hinj : Function.Injective (((Submodule.span R {algebraMap R K n / algebraMap R K d}).comap
        (Algebra.linearMap R K) : Ideal R).liftQ _ hker.ge) :=
      LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ hker.le)
    exact minimal_and_height_eq_one (fun q hq => ⟨hq.isPrime,
      height_eq_one_of_mem_associatedPrimes hn0
        (associatedPrimes.subset_of_injective hinj hq)⟩) hp

end
