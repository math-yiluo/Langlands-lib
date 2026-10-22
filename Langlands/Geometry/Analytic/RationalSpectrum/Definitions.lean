import Langlands.Geometry.Analytic.RationalPresentation.Definitions

/-! # Algebraic fractions inside a rational quotient -/

universe u v w

namespace Langlands.Analytic

section Fractions

variable (K : Type u) {A : Type v} {B : Type w}
  [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- The actual subalgebra of elements whose product with some power of
`φ s` lies in the image of `φ`. No localization or inverse is assumed. -/
def fractionSubalgebra (φ : A →ₐ[K] B) (s : A) : Subalgebra K B where
  carrier := {b | ∃ r : ℕ, ∃ a : A, φ s ^ r * b = φ a}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨0, 1, by simp⟩
  add_mem' := by
    rintro a b ⟨r, a', ha⟩ ⟨t, b', hb⟩
    refine ⟨r + t, s ^ t * a' + s ^ r * b', ?_⟩
    calc
      φ s ^ (r + t) * (a + b) =
          φ s ^ t * (φ s ^ r * a) + φ s ^ r * (φ s ^ t * b) := by
        rw [pow_add]
        ring
      _ = φ s ^ t * φ a' + φ s ^ r * φ b' := by rw [ha, hb]
      _ = _ := by simp only [map_add, map_mul, map_pow]
  mul_mem' := by
    rintro a b ⟨r, a', ha⟩ ⟨t, b', hb⟩
    refine ⟨r + t, a' * b', ?_⟩
    calc
      φ s ^ (r + t) * (a * b) = (φ s ^ r * a) * (φ s ^ t * b) := by
        rw [pow_add]
        ring
      _ = φ a' * φ b' := by rw [ha, hb]
      _ = _ := (φ.map_mul _ _).symm
  algebraMap_mem' c := ⟨0, algebraMap K A c, by simp⟩

theorem mem_fractionSubalgebra (φ : A →ₐ[K] B) (s a : A) :
    φ a ∈ fractionSubalgebra K φ s :=
  ⟨0, a, by simp⟩

end Fractions

end Langlands.Analytic
