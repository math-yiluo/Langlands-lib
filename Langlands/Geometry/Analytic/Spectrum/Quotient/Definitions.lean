import Langlands.Geometry.Analytic.Spectrum.Definitions
import Mathlib.Analysis.Normed.Group.Quotient

/-! # Ideal zero loci and the bounded quotient projection -/

noncomputable section

universe u

namespace Langlands.Analytic.BanachSpectrum

variable {A : Type u} [NormedCommRing A]

/-- The zero locus of an actual ideal. -/
def zeroLocus (I : Ideal A) : Set (BanachSpectrum A) :=
  {x | I ≤ x.kernel}

variable (I : Ideal A) [IsClosed (I : Set A)]

/-- The quotient projection is contractive for the actual quotient norm. -/
def quotientHom : BoundedRingHom A (A ⧸ I) where
  toRingHom := Ideal.Quotient.mk I
  bounded := ⟨1, zero_lt_one, fun a => by
    simpa only [one_mul] using Ideal.Quotient.norm_mk_le I a⟩

@[simp]
theorem quotientHom_apply (a : A) :
    quotientHom I a = Ideal.Quotient.mk I a := rfl

end Langlands.Analytic.BanachSpectrum
