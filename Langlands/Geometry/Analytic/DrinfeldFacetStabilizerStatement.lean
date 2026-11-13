import Langlands.Geometry.Analytic.DrinfeldBuildingCovering

/-! # Statement: the elements of a facet stabilizer with `|det| = 1` form a compact open set -/

universe v

namespace Langlands.Analytic.DrinfeldUpperHalfSpace

/-- For a facet `f` of the building of norm classes on `F^{d+1}` (the vertex set of a chain of
lattices), the elements `γ` of its stabilizer `S(f)` in `GL_{d+1}(F)` with `|det γ| = 1` form a
compact open subset of `GL_{d+1}(F)`. This is the analogue, for the matrix factor
`GL_{d+1}(F)` of Harris's group `G_J`, of the reason Harris gives for the compactness of `S(ê)`
(Harris 1999, §2, printed pp.303–304). -/
def FacetStabilizerCompactOpenStatement : Prop :=
  ∀ (F : Type v) [NontriviallyNormedField F] [ProperSpace F] (d : ℕ)
    (S : Set (NormClass F (Fin (d + 1) → F))), NormClass.IsFacet S →
      IsCompact {γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F |
          γ ∈ facetStabilizer S ∧ ‖((Matrix.GeneralLinearGroup.det γ : Fˣ) : F)‖ = 1} ∧
        IsOpen {γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F |
          γ ∈ facetStabilizer S ∧ ‖((Matrix.GeneralLinearGroup.det γ : Fˣ) : F)‖ = 1}

end Langlands.Analytic.DrinfeldUpperHalfSpace
