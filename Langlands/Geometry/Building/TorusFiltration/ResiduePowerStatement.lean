import Langlands.Geometry.Building.TorusFiltration.Points

/-! # Residue-characteristic powers in the minimal congruent torus filtration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

/-- For `0 < r ≤ s ≤ min (2 * r) (r + 1)`, the `p`th power of every point of
depth `r` in the minimal congruent filtration of a torus over the maximal
unramified field has depth `s`, where `p` is the residue characteristic. This is
the rational-point estimate behind the exponent-`p` quotients `T(K)_r / T(K)_s`
in KP Proposition B.10.17 on this range of depths. -/
def MinimalCongruentResiduePowerStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left] (hT : IsTorus T.toGrp) (r s : ℝ≥0),
    0 < r → r ≤ s → s ≤ 2 * r → s ≤ r + 1 →
      ∀ g ∈ minimalCongruentPoints F T hT r,
        g ^ ringChar (IsLocalRing.ResidueField (fixedFieldIntegers F)) ∈
          minimalCongruentPoints F T hT s

end Langlands.Geometry.Building
