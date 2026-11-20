import Langlands.Geometry.Analytic.DrinfeldReduction

/-! # The reduction map of Drinfeld's upper half space is surjective -/

universe u v

namespace Langlands.Analytic.DrinfeldUpperHalfSpace

/-- Over a non-Archimedean local field `F`, every homothety class of norms on `F^{d+1}` is the
reduction `Res(z)` of a point `z` of Drinfeld's upper half space `Ω ⊂ 𝔸^d_K`
(Rémy–Thuillier–Werner, §2.1.3: the map `j` is a section of `τ`). -/
def ReductionSurjectiveStatement : Prop :=
  ∀ (F : Type v) [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F]
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [NormedAlgebra F K] (d : ℕ) [NeZero d],
    Function.Surjective (reduction (F := F) K (d := d))

end Langlands.Analytic.DrinfeldUpperHalfSpace
