import Langlands.AlgebraicGeometry.Picard.EquivariantLineBundle
import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationInvariantOpen
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Invariant generating sections along a cartesian étale relation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule

/-- Let `p : U ⟶ S` be a flat surjective morphism of affine schemes, `E` an actual étale
equivalence relation and `f : E.U ⟶ U` quasi-compact and quasi-separated, with
`E.R` the fibre product of `E.U` and `U` over `S` through `E.t` and `E.s ≫ f`.
If a global section of the chart bundle of an actual equivariant line bundle
generates it at a point, then some global section generates it at that point and
has an invariant generation locus. -/
def EquivariantInvariantSectionStatement : Prop :=
  ∀ (S U : Scheme.{u}), IsAffine S → IsAffine U →
    ∀ (p : U ⟶ S), Flat p → Surjective p →
      ∀ (E : EtaleEquivalenceRelation.{u}) (f : E.U ⟶ U),
        QuasiCompact f → QuasiSeparated f →
          IsPullback E.t (E.s ≫ f) (f ≫ p) p →
            ∀ (B : EquivariantLineBundle E) (σ : GlobalSections B.bundle.obj) (x : E.U),
              x ∈ trivializationOpen B.bundle.obj σ →
                ∃ m : GlobalSections B.bundle.obj,
                  x ∈ trivializationOpen B.bundle.obj m ∧
                    E.IsInvariantOpen (trivializationOpen B.bundle.obj m)

end Langlands.AlgebraicGeometry.Picard
