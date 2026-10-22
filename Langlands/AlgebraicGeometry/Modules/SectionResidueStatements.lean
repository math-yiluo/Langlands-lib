import Langlands.AlgebraicGeometry.Modules.SectionResidue
import Langlands.AlgebraicGeometry.Picard.LineBundle

/-! # Comparison targets for residue-field nonvanishing of line-bundle sections -/

universe u

open AlgebraicGeometry

namespace Langlands.SchemeModule

open Langlands.AlgebraicGeometry.Picard

/-- For a line bundle, nonzero residue-field value is equivalent to being a stalk frame. -/
def LineBundleResidueStalkCriterion : Prop :=
  ∀ (X : Scheme.{u}) (L : LineBundle X) (s : GlobalSections L.obj) (x : X),
    NonvanishingAt L.obj s x ↔ IsStalkFrame L.obj s x

/-- The whole residue-field nonvanishing locus is the local trivialization open. -/
def LineBundleResidueOpenComparison : Prop :=
  ∀ (X : Scheme.{u}) (L : LineBundle X) (s : GlobalSections L.obj),
    nonvanishingLocus L.obj s = (trivializationOpen L.obj s : Set X)

/-- The stalk and open-locus comparisons for actual residue-field values. -/
def LineBundleSectionResidueComparison : Prop :=
  LineBundleResidueStalkCriterion.{u} ∧ LineBundleResidueOpenComparison.{u}

end Langlands.SchemeModule
