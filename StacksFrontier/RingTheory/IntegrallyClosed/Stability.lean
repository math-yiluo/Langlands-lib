module

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
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ext.Baer
public import Mathlib.RingTheory.LocalProperties.InjectiveDimension
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import StacksFrontier.Data.ENat.WithBotNatCast
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.RegularLocalRing.GlobalDimension
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

@[expose] public section

/-!
# A regular ring is normal

A commutative ring `R` is regular (Mathlib's `IsRegularRing`: Noetherian, with every
localization at a prime a regular local ring); it is normal if every such localization is an
integrally closed integral domain. The classical fact is that regular implies normal: by Serre's
criterion (Stacks 031S) it suffices to check `(R_1)`, which is part of regularity, and `(S_2)`,
which holds because a regular local ring is Cohen–Macaulay (Stacks 00NQ).

The predicate `IsNormalRing` is provided once and for all in
`StacksFrontier.RingTheory.IntegrallyClosed.Defs`; it is reused here.
-/

end

@[expose] public section

/-! Stacks 00GZ, that a principal ideal domain is normal — integrally closed in its field of
fractions — is a Mathlib instance chain: a PID is a unique factorization domain by
`PrincipalIdealRing.to_uniqueFactorizationMonoid`, and a unique factorization domain is
integrally closed by `UniqueFactorizationMonoid.instIsIntegrallyClosed`. -/

end

/-!
# The integral closure inside a normal domain is a normal domain

Let `R → S` be a map of commutative rings and suppose `S` is a normal domain. Let
`R̄ ⊆ S` be the integral closure of `R` in `S`. Then `R̄` is a normal domain: with the
ring structure inherited from `S` as a subring it is a domain, and it is integrally
closed in its fraction field `Frac(R̄)`. This is Stacks Tag 034L.

Recall the notions involved. An element `s` of `S` is *integral* over `R` when it
satisfies a monic polynomial equation with coefficients in the image of `R`; the
*integral closure* of `R` in `S` is the set of all such elements, a subring of `S`
(Stacks Tag 00GO), which in Mathlib is `integralClosure R S : Subalgebra R S`, with
integrality of an element written `IsIntegral R s`. A ring `A` is a *domain* when
`0 ≠ 1` and it has no nonzero zero-divisors (`IsDomain A`), and a *normal domain*
when it is moreover integrally closed in its field of fractions `Frac(A)` (Stacks
Tag 0309). The latter is the class `IsNormalDomain A`, whose two fields
are `IsDomain A` and `IsIntegrallyClosed A`, the second saying exactly that every
element of `Frac(A)` integral over `A` lies in the image of `A`.

## Main results

* `integralClosure_isNormalDomain`: the integral closure of `R` in a normal domain
  `S` is a normal domain.

## Implementation notes

That `R̄` is a domain is automatic: `S` is a domain and Mathlib infers `IsDomain` for
a subalgebra of a domain. For integral closedness, an element `x` of `Frac(R̄)`
integral over `R̄` is transported along the injection `Frac(R̄) → Frac(S)` induced by
`R̄ ⊆ S`; transitivity of integrality makes its image integral over `R`, hence over
`S`, so normality of `S` produces an `s ∈ S` representing it. That `s` is then
integral over `R`, so it lies in `R̄`, and it is the required preimage of `x`.
-/

@[expose] public section

end

@[expose] public section

end

@[expose] public section

/-!
# A finite product of normal rings is normal

A commutative ring `R` is *normal* (`IsNormalRing`, Stacks Tag `00GV`) when, for every
prime ideal `p` of `R`, the localization `Localization.AtPrime p` is an integrally closed
integral domain. Here `IsIntegrallyClosed R` (Mathlib) is, reducibly,
`IsIntegrallyClosedIn R (FractionRing R)`: `R` is integrally closed in its total ring of
fractions.

Given a finite index type `ι` and a family of commutative rings `R : ι → Type*`, the product
ring is the dependent function type `∀ i, R i` with the componentwise (`Pi.commRing`) ring
structure. We claim: if each `R i` is normal, then the product `∀ i, R i` is normal.

A localization of the product at a prime `p` is canonically ring-isomorphic to a
localization of one of the factors at a prime, so each localization of the product is an
integrally closed domain precisely because each `R i` is normal.
-/

/-- Supporting lemma: bijectivity of `Localization.localRingHom` along a surjective ring hom
whose kernel is killed in the localization at `I`. -/
private theorem isNormalRing_pi.localRingHom_bijective
    {S P : Type*} [CommRing S] [CommRing P] (f : S →+* P)
    (hf : Function.Surjective f) (J : Ideal P) [J.IsPrime] (I : Ideal S) [I.IsPrime]
    (hcomap : I = Ideal.comap f J)
    (hker : ∀ k, f k = 0 → ∃ w ∉ I, w * k = 0) :
    Function.Bijective (Localization.localRingHom I J f hcomap) := by
  have hpre : ∀ s, f s ∈ J.primeCompl → s ∈ I.primeCompl := fun s hs hc =>
    hs (by simpa [hcomap] using hc)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective I.primeCompl z
    rw [Localization.localRingHom_mk'] at hz
    rw [IsLocalization.mk'_eq_zero_iff] at hz ⊢
    obtain ⟨⟨m, hm⟩, hmeq⟩ := hz
    obtain ⟨s, rfl⟩ := hf m
    obtain ⟨w, hw, hweq⟩ := hker (s * a) (by simpa using hmeq)
    exact ⟨⟨w * s, I.primeCompl.mul_mem hw (hpre s hm)⟩, (mul_assoc w s a).trans hweq⟩
  · intro z
    obtain ⟨⟨b, t'⟩, rfl⟩ := IsLocalization.mk'_surjective J.primeCompl z
    obtain ⟨a, rfl⟩ := hf b
    obtain ⟨t, ht⟩ := hf t'.val
    refine ⟨IsLocalization.mk' (Localization.AtPrime I) a ⟨t, hpre t (ht ▸ t'.property)⟩, ?_⟩
    simp [ht]

/-- Supporting lemma: a localization of the product at a prime is ring-isomorphic to a
localization of one of the factors at a prime. -/
private theorem isNormalRing_pi.exists_factor_localization
    {ι : Type*} [Finite ι] (R : ι → Type*) [∀ i, CommRing (R i)]
    (p : Ideal (∀ i, R i)) [p.IsPrime] :
    ∃ (i₀ : ι) (q : Ideal (R i₀)) (_ : q.IsPrime),
      Nonempty (Localization.AtPrime p ≃+* Localization.AtPrime q) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hsum : (1 : ∀ i, R i) = ∑ i, Pi.single i 1 := by
    ext j
    simp [Finset.sum_apply]
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, Pi.single i₀ (1 : R i₀) ∉ p := by
    by_contra! hcon
    exact ‹p.IsPrime›.ne_top
      ((Ideal.eq_top_iff_one _).2 (hsum ▸ Ideal.sum_mem _ fun i _ => hcon i))
  set f : (∀ i, R i) →+* R i₀ := Pi.evalRingHom R i₀ with hf_def
  have hfsurj : Function.Surjective f := Function.surjective_eval i₀
  have hker : ∀ k, f k = 0 → ∃ w ∉ p, w * k = 0 := by
    intro k hk
    refine ⟨Pi.single i₀ (1 : R i₀), hi₀, ?_⟩
    ext j
    by_cases hj : j = i₀
    · subst hj
      simpa [hf_def] using hk
    · simp [hj]
  have hkerle : RingHom.ker f ≤ p := fun x hx => by
    obtain ⟨w, hw, h0⟩ := hker x (RingHom.mem_ker.mp hx)
    exact (‹p.IsPrime›.mem_or_mem (h0 ▸ p.zero_mem : w * x ∈ p)).resolve_left hw
  have hJprime : (Ideal.map f p).IsPrime := Ideal.map_isPrime_of_surjective hfsurj hkerle
  have hcomap : p = Ideal.comap f (Ideal.map f p) := by
    rw [Ideal.comap_map_of_surjective f hfsurj, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hkerle]
  exact ⟨i₀, _, hJprime, ⟨RingEquiv.ofBijective _
    (isNormalRing_pi.localRingHom_bijective f hfsurj _ p hcomap hker)⟩⟩

/-- A finite product of normal rings is normal.
(Stacks Lemma 10.37.16, tag `0CYA`.) -/
@[stacks 0CYA]
theorem isNormalRing_pi
    {ι : Type*} [Finite ι] {R : ι → Type*} [∀ i, CommRing (R i)]
    (h : ∀ i, IsNormalRing (R i)) :
    IsNormalRing (∀ i, R i) := by
  refine isNormalRing_iff.2 fun p hp => ?_
  obtain ⟨i₀, q, hq, ⟨e⟩⟩ := isNormalRing_pi.exists_factor_localization R p
  obtain ⟨_, _⟩ := isNormalRing_iff.1 (h i₀) q
  have hdom : IsDomain (Localization.AtPrime p) := e.injective.isDomain e.toRingHom
  exact ⟨hdom, IsIntegrallyClosed.of_equiv e.symm⟩

end
