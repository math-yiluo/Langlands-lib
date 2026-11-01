import Langlands.Geometry.Analytic.GeneralizedAffinoid.Definitions

/-! # A common complete field realizing compatible affinoid points -/

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

/-- Compatible points of two actual presented affinoid algebras admit norm
realizations by bounded algebra maps to one complete ultrametric field in the
coefficient field's universe, with equal composites from the common base. -/
def PointAmalgamationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A B C : PresentedAffinoidAlgebra K)
    (i : BoundedAlgHom K A B) (j : BoundedAlgHom K A C)
    (x : BanachSpectrum B) (y : BanachSpectrum C),
    BanachSpectrum.comap i.toBoundedRingHom x =
      BanachSpectrum.comap j.toBoundedRingHom y →
    ∃ (L : Type u) (_ : NormedField L) (_ : IsUltrametricDist L)
      (_ : CompleteSpace L) (_ : NormedAlgebra K L)
      (f : BoundedAlgHom K B L) (g : BoundedAlgHom K C L),
      f.comp i = g.comp j ∧
        (∀ b : B, ‖f b‖ = x b) ∧
        (∀ c : C, ‖g c‖ = y c)

end Langlands.Analytic.PresentedAffinoidAlgebra
