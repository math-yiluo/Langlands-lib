import Langlands.Geometry.Analytic.StrictTestDomain.RationalPullbackDefinitions
import Mathlib.Data.Finset.Max

/-! # Standard rational covers from finite tuples -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {P Q : PresentedStrictAffinoidAlgebra K} {n : ℕ}

/-- The standard rational datum with denominator `f j` and all entries of `f`
as numerators. Its no-common-zero condition follows from that of the tuple. -/
def standardRational (f : Fin n → P)
    (h : ∀ x : BanachSpectrum P, ∃ k, x (f k) ≠ 0) (j : Fin n) :
    RationalData K P where
  arity := n
  denominator := f j
  numerator := f
  no_common_zero x := Or.inr (h x)

variable (f : Fin n → P)
  (h : ∀ x : BanachSpectrum P, ∃ k, x (f k) ≠ 0)

@[simp]
theorem standardRational_arity (j : Fin n) :
    (standardRational f h j).arity = n := rfl

@[simp]
theorem standardRational_denominator (j : Fin n) :
    (standardRational f h j).denominator = f j := rfl

@[simp]
theorem standardRational_numerator (j k : Fin n) :
    (standardRational f h j).numerator k = f k := rfl

/-- Membership in a standard rational locus is exactly maximality of the
chosen denominator among the evaluated entries of the tuple. -/
@[simp]
theorem mem_standardRational_locus (j : Fin n) (x : BanachSpectrum P) :
    x ∈ (standardRational f h j).locus ↔ ∀ k, x (f k) ≤ x (f j) :=
  Iff.rfl

/-- The standard rational loci cover the whole Banach spectrum.
The tuple's nonvanishing hypothesis supplies an index at each point, including
when the tuple is allowed to be empty. -/
theorem standardRational_covers (x : BanachSpectrum P) :
    ∃ j, x ∈ (standardRational f h j).locus := by
  classical
  obtain ⟨i, _⟩ := h x
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun k => x (f k)) ⟨i, Finset.mem_univ i⟩
  exact ⟨j, fun k => hj k (Finset.mem_univ k)⟩

include h in
/-- A bounded algebra map preserves the tuple's absence of common spectrum
zeros, by evaluation at the actual pulled-back spectrum point. -/
theorem tuple_no_common_zero_pullback (φ : BoundedAlgHom K P Q) :
    ∀ x : BanachSpectrum Q, ∃ k, x (φ (f k)) ≠ 0 :=
  fun x => h (BanachSpectrum.comap φ.toBoundedRingHom x)

/-- The standard datum for the mapped tuple is the existing pullback datum. -/
@[simp]
theorem standardRational_pullback (φ : BoundedAlgHom K P Q) (j : Fin n) :
    (standardRational f h j).pullback φ =
      standardRational (fun k => φ (f k)) (tuple_no_common_zero_pullback f h φ) j :=
  rfl

/-- The standard loci for the mapped tuple are the inverse images of the
original standard loci under the actual spectrum map. -/
theorem standardRational_locus_pullback (φ : BoundedAlgHom K P Q) (j : Fin n) :
    (standardRational (fun k => φ (f k)) (tuple_no_common_zero_pullback f h φ) j).locus =
      (BanachSpectrum.comap φ.toBoundedRingHom) ⁻¹' (standardRational f h j).locus :=
  rfl

end Langlands.Analytic.StrictTestDomain
