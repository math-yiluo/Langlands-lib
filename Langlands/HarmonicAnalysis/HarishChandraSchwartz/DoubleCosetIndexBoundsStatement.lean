import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DoubleCosetMeasure

/-! # Algebraic bounds for conjugate-intersection indices -/

universe u v

namespace Langlands.HarishChandraSchwartz

/-- The finite conjugate-intersection index is submultiplicative, is bounded
on powers by the corresponding index power, and cannot increase under a group
homomorphism applied to both the subgroup and the element. -/
def DoubleCosetIndexBoundsStatement : Prop :=
  ∀ (G : Type u) [Group G] (K : Subgroup G),
    (∀ g h : G, doubleCosetIndex K g ≠ 0 → doubleCosetIndex K h ≠ 0 →
      doubleCosetIndex K (g * h) ≠ 0 ∧
        doubleCosetIndex K (g * h) ≤ doubleCosetIndex K g * doubleCosetIndex K h) ∧
    (∀ g : G, doubleCosetIndex K g ≠ 0 → ∀ n : ℕ,
      doubleCosetIndex K (g ^ n) ≠ 0 ∧
        doubleCosetIndex K (g ^ n) ≤ doubleCosetIndex K g ^ n) ∧
    (∀ (H : Type v) [Group H] (f : G →* H) (g : G),
      doubleCosetIndex K g ≠ 0 →
        doubleCosetIndex (K.map f) (f g) ≠ 0 ∧
          doubleCosetIndex (K.map f) (f g) ≤ doubleCosetIndex K g)

end Langlands.HarishChandraSchwartz
