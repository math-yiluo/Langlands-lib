import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Data.Fintype.EquivFin

/-! # Finite ordered affine covers of quasi-compact schemes -/

noncomputable section

universe u

open TopologicalSpace

namespace AlgebraicGeometry.Scheme.OrderedAffineCover

/-- A quasi-compact scheme admits a finite ordered affine open cover. -/
def ofCompactSpace (X : Scheme.{u}) [CompactSpace X] : X.OrderedAffineCover :=
  Classical.choice (by
    classical
    obtain ⟨Us, hUs, hfinite, hcover⟩ :=
      X.isBasis_affineOpens.exists_finite_of_isCompact
        (U := ⊤) (show IsCompact (⊤ : X.Opens).carrier from isCompact_univ)
    let : Fintype Us := hfinite.fintype
    let : LinearOrder Us :=
      LinearOrder.lift' (Fintype.equivFin Us) (Fintype.equivFin Us).injective
    exact ⟨{
      ι := Us
      U := Subtype.val
      isAffineOpen := fun i => hUs i.property
      iSup_eq_top := by
        simpa only [sSup_eq_iSup'] using hcover.symm
    }⟩)

end AlgebraicGeometry.Scheme.OrderedAffineCover
