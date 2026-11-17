import Langlands.Geometry.Analytic.AnalytificationCenter
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormStatement

/-! # Affine center surjectivity from faithful norms on finite-type domains -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification.CenterSurjectivity

/-- Every prime quotient has a faithful multiplicative seminorm extending the
norm of the ground field. This is an explicit input to the center reduction. -/
def PrimeQuotientNormData (K : Type u) [NontriviallyNormedField K]
    (A : Type v) [CommRing A] [Algebra K A] : Prop :=
  ∀ p : PrimeSpectrum A, ∃ n : MulRingSeminorm (A ⧸ p.asIdeal),
    ExtendsNorm K n ∧ ∀ a : A ⧸ p.asIdeal, n a = 0 → a = 0

variable (K : Type u) [NontriviallyNormedField K]
  {A : Type v} [CommRing A] [Algebra K A]

/-- Pulling a faithful multiplicative seminorm back from a prime quotient gives
an extending seminorm whose zero set is exactly the given prime ideal. -/
theorem exists_seminorm_with_kernel (p : PrimeSpectrum A)
    (n : MulRingSeminorm (A ⧸ p.asIdeal))
    (hn : ExtendsNorm K n)
    (hfaithful : ∀ a : A ⧸ p.asIdeal, n a = 0 → a = 0) :
    ∃ ν : MulRingSeminorm A, ExtendsNorm K ν ∧
      ∀ a : A, ν a = 0 ↔ a ∈ p.asIdeal := by
  let ν : MulRingSeminorm A :=
    { toFun := fun a => n (Ideal.Quotient.mk p.asIdeal a)
      map_zero' := by simp
      map_one' := by simp
      map_mul' := fun a b => by simp only [map_mul]
      add_le' := fun a b => by
        rw [map_add]
        exact map_add_le_add n _ _
      neg' := fun a => by simp only [map_neg, map_neg_eq_map] }
  refine ⟨ν, ?_, ?_⟩
  · intro c
    change n (Ideal.Quotient.mk p.asIdeal (algebraMap K A c)) = ‖c‖
    rw [Ideal.Quotient.mk_algebraMap]
    exact hn c
  · intro a
    change n (Ideal.Quotient.mk p.asIdeal a) = 0 ↔ a ∈ p.asIdeal
    constructor
    · intro h
      exact Ideal.Quotient.eq_zero_iff_mem.mp (hfaithful _ h)
    · intro h
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

variable [IsUltrametricDist K] [CompleteSpace K] (P : FinitePolynomialPresentation K A)

/-- The seminorm range property and a faithful extending seminorm on every
prime quotient imply surjectivity of the affine center map. -/
theorem center_surjective_of_quotient_norms
    (hrange : Set.range (pointSeminorm K P) =
      {ν : MulRingSeminorm A | ExtendsNorm K ν})
    (hnorm : PrimeQuotientNormData K A) :
    Function.Surjective (center K P) := by
  intro p
  obtain ⟨n, hn, hfaithful⟩ := hnorm p
  obtain ⟨ν, hν, hzero⟩ := exists_seminorm_with_kernel K p n hn hfaithful
  have hmem : ν ∈ Set.range (pointSeminorm K P) := by
    rw [hrange]
    exact hν
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, PrimeSpectrum.ext ?_⟩
  ext a
  rw [center_asIdeal, mem_kernel, hx]
  exact hzero a

/-- A faithful extending seminorm for every finite-type domain supplies the
quotient seminorms needed for affine center surjectivity, in independent universes. -/
theorem center_surjective_of_finiteType_norms
    (hrange : Set.range (pointSeminorm K P) =
      {ν : MulRingSeminorm A | ExtendsNorm K ν})
    (hnorm : ∀ (D : Type v) [CommRing D] [IsDomain D] [Algebra K D]
      [Algebra.FiniteType K D], ∃ n : MulRingSeminorm D,
        ExtendsNorm K n ∧ ∀ a : D, n a = 0 → a = 0) :
    Function.Surjective (center K P) := by
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  apply center_surjective_of_quotient_norms K P hrange
  intro p
  let : p.asIdeal.IsPrime := p.isPrime
  exact hnorm (A ⧸ p.asIdeal)

end Langlands.Analytic.AffineAnalytification.CenterSurjectivity
