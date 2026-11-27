import Langlands.AlgebraicGeometry.FactorialAffineExtension
import Langlands.AlgebraicGeometry.SmoothDvrAffineOpenGeometry
import Langlands.AlgebraicGeometry.FibreDenseOpenPullback
import Langlands.CommutativeAlgebra.RegularLocalFactorialProof

/-! # Fibre-dense opens at small primes in smooth DVR schemes -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Topology

namespace Langlands.AlgebraicGeometry.SmoothDvrCodimensionOneOpen

open FactorialAffineExtension

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

local notation "S" => Spec (CommRingCat.of R)

/-- The complement of the closed point of the spectrum of a DVR. -/
def genericOpen : (S).Opens :=
  ⟨{IsLocalRing.closedPoint R}ᶜ, (IsLocalRing.isClosed_singleton_closedPoint R).isOpen_compl⟩

@[simp]
theorem mem_genericOpen (s : S) : s ∈ genericOpen R ↔ s ≠ IsLocalRing.closedPoint R := Iff.rfl

/-- The generic open is dense in the spectrum of a DVR. -/
theorem dense_genericOpen : Dense (genericOpen R : Set S) := by
  apply (genericOpen R).isOpen.dense
  refine ⟨(⊥ : PrimeSpectrum R), ?_⟩
  intro he
  exact IsDiscreteValuationRing.not_a_field R (congrArg PrimeSpectrum.asIdeal he.symm)

/-- Smoothness over a DVR gives a domain stalk. -/
theorem isDomain_stalk {X : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  have := Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing R f x
  exact IsRegularLocalRing.isDomainFLT _

/-- Smoothness over a DVR gives a factorial stalk. -/
theorem factorial_stalk {X : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  Langlands.CommutativeAlgebra.regularLocalFactorial _
    (Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing R f x)

private theorem eq_bot_or_eq_of_le_principal_prime {A : Type*} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] (p q : PrimeSpectrum A) (hqp : q ≤ p)
    (hp : IsGenericOrPrimeElement p) : q = ⊥ ∨ q = p := by
  rcases hp with hp | ⟨r, hr, hp⟩
  · left
    exact le_antisymm (show q.asIdeal ≤ ⊥ by rwa [← hp]) bot_le
  by_cases hq : q.asIdeal = ⊥
  · exact Or.inl (PrimeSpectrum.ext hq)
  · right
    obtain ⟨t, ht, hprime⟩ := q.isPrime.exists_mem_prime_of_ne_bot hq
    have hrt : r ∣ t := Ideal.mem_span_singleton.mp (hp ▸ hqp ht)
    obtain ⟨v, hv⟩ := (hr.associated_of_dvd hprime hrt).symm
    have hqr : r ∈ q.asIdeal := by
      rw [← hv]
      exact Ideal.mul_mem_right _ _ ht
    apply le_antisymm hqp
    change p.asIdeal ≤ q.asIdeal
    rwa [hp, Ideal.span_singleton_le_iff_mem]

/-- A fibre-dense open that contains the generic fibre contains the images of the generic
and principal prime points of each stalk spectrum. -/
theorem smallPrime_mem {X : Scheme.{u}} (f : X ⟶ S) [Smooth f] (U : X.Opens)
    (hU : FibreGenerizationDense f (U : Set X)) (hη : f ⁻¹ᵁ genericOpen R ≤ U)
    (x : X) (p : PrimeSpectrum (X.presheaf.stalk x))
    (hp : IsGenericOrPrimeElement p) : X.fromSpecStalk x p ∈ U := by
  let A := X.presheaf.stalk x
  let : IsDomain A := isDomain_stalk R f x
  let : UniqueFactorizationMonoid A := factorial_stalk R f x
  let j := X.fromSpecStalk x
  have hmin (z : X) (hz : z ⤳ j (⊥ : PrimeSpectrum A)) : z = j (⊥ : PrimeSpectrum A) := by
    have hr : z ∈ Set.range j := by
      rw [Scheme.range_fromSpecStalk]
      exact hz.trans ((IsLocalRing.specializes_closedPoint (⊥ : PrimeSpectrum A)).map j.continuous |>.trans
        (specializes_of_eq Scheme.fromSpecStalk_closedPoint))
    obtain ⟨q, rfl⟩ := hr
    have hle := (PrimeSpectrum.le_iff_specializes _ _).mpr (j.isEmbedding.specializes_iff.mp hz)
    rw [le_bot_iff.mp hle]
  by_cases h : f (j p) ∈ genericOpen R
  · exact hη h
  have hbot : f (j (⊥ : PrimeSpectrum A)) = (⊥ : PrimeSpectrum R) := by
    obtain ⟨z, hz, hfz⟩ := Flat.generalizingMap f (a := j (⊥ : PrimeSpectrum A))
      ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le : (⊥ : PrimeSpectrum R) ⤳ f (j (⊥ : PrimeSpectrum A)))
    rwa [hmin z hz] at hfz
  obtain ⟨z, hzU, hfz, hz⟩ := hU (j p)
  have hr : z ∈ Set.range j := by
    rw [Scheme.range_fromSpecStalk]
    exact hz.trans ((IsLocalRing.specializes_closedPoint p).map j.continuous |>.trans
      (specializes_of_eq Scheme.fromSpecStalk_closedPoint))
  obtain ⟨q, rfl⟩ := hr
  have hqp := (PrimeSpectrum.le_iff_specializes _ _).mpr (j.isEmbedding.specializes_iff.mp hz)
  rcases eq_bot_or_eq_of_le_principal_prime p q hqp hp with rfl | rfl
  · apply (h ?_).elim
    rw [← hfz, hbot]
    change (⊥ : PrimeSpectrum R) ≠ IsLocalRing.closedPoint R
    intro he
    exact IsDiscreteValuationRing.not_a_field R (congrArg PrimeSpectrum.asIdeal he.symm)
  · exact hzU

end Langlands.AlgebraicGeometry.SmoothDvrCodimensionOneOpen
