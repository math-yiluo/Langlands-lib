import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Henselian

/-!
# Algebraic boundedness and analytic compactness: statement targets

KP Fact 2.2.3 with the corrected Henselian hypothesis, followed by its
unrestricted nonarchimedean-local-field specialization. Both use the named
canonical evaluation topology on actual rational points.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]

/-- Corrected KP Fact 2.2.3. The field topology is the nontrivial rank-one
valuation topology; Henselianity and local compactness are explicit premises.
The conclusion concerns closed subsets of actual finite-type affine points. -/
def AffineBoundedCompactnessProperty
    [ValuativeRel.IsNontrivial F] [ValuativeRel.IsRankLeOne F]
    [IsValuativeTopology F] : Prop :=
  HenselianLocalRing (ValuativeRel.valuation F).integer →
    LocallyCompactSpace F →
      ∀ (X : Over (Spec (CommRingCat.of F))) [IsAffine X.left]
        [LocallyOfFiniteType X.hom],
        letI : TopologicalSpace (RationalPoint F X) := rationalPointTopology F X
        ∀ B : Set (RationalPoint F X),
          IsClosed B → (IsAlgebraicallyBounded F X B ↔ IsCompact B)

/-- The full nonarchimedean-local-field specialization of the comparison.
There is no extra Henselianity or characteristic premise. -/
def LocalFieldAffineBoundedCompactnessProperty
    [IsNonarchimedeanLocalField F] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of F))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom],
    letI : TopologicalSpace (RationalPoint F X) := rationalPointTopology F X
    ∀ B : Set (RationalPoint F X),
      IsClosed B → (IsAlgebraicallyBounded F X B ↔ IsCompact B)

end Langlands.AlgebraicGeometry.PointTopology
