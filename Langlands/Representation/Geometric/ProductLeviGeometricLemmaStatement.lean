import Langlands.Representation.Geometric.GeometricLemmaStatement
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.CompactCoefficient.GroupTransport

/-! BZ77's normalized geometric lemma inside a standard product Levi of GL. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- Minimal representatives for the pair of flattened Levis of two refinements
of `B` that lie in the Weyl group of the coarse Levi `B.Levi`. -/
abbrev BlockMinimalRepresentatives (Q S : BlockRefinement B) :=
  {w : MinimalRepresentatives (B.flatten Q) (B.flatten S) // w.val ∈ blockWeyl B}

/-- The actual composition inside `B.Levi`: normalized induction from the
refined subgroup of `Q`, then the normalized upper Jacquet functor to the
refined subgroup of `S`, both read on flattened Levis through the constructed
continuous identifications. -/
def innerJacquetInductionFunctor (Q S : BlockRefinement B) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ ((B.flatten Q).Levi F.Carrier) ⥤
      Rep.{max uF uV} ℂ ((B.flatten S).Levi F.Carrier) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B Q).symm ⋙
    T.normalizedRefinedInductionFunctor B Q ⋙
    T.normalizedRefinedJacquetFunctor B S ⋙
    SmoothRep.pullbackFunctor (flattenedLeviEquivContinuous F.Carrier B S) ⋙
    SmoothRep.toRep

/-- BZ77 2.12 for the group `B.Levi`, with the parabolic subgroups of
`B.Levi` attached to `Q` and `S`. The pieces are the `GL_n` geometric-lemma
pieces for the flattened shapes, indexed by the minimal representatives in the
coarse Weyl group. Refinements, equalities, enumeration, filtration and
natural graded isomorphisms are all conclusions. -/
def ProductLeviGeometricLemmaTheorem (Q S : BlockRefinement B) : Prop :=
  letI := T.topology
  ∃ (S' : BlockMinimalRepresentatives B Q S → BlockRefinement (B.flatten Q))
    (R' : BlockMinimalRepresentatives B Q S → BlockRefinement (B.flatten S)),
    ∃ (hS : ∀ w, IsIntersectionRefinement (F := F.Carrier)
        (B.flatten Q) (B.flatten S) w.val.val (S' w))
      (hR : ∀ w, IsIntersectionRefinement (F := F.Carrier)
        (B.flatten S) (B.flatten Q) w.val.val⁻¹ (R' w)),
      ∃ (m : ℕ) (e : Fin m ≃ BlockMinimalRepresentatives B Q S),
        IsGluedFrom (innerJacquetInductionFunctor.{uF, uV} T B Q S)
          (fun i => geometricPieceFunctor T (B.flatten Q) (B.flatten S) (e i).val.val
            (S' (e i)) (R' (e i)) (hS (e i)).2.1 (hR (e i)).2.1)

/-- The product-Levi normalized geometric lemma for every coarse shape and every
pair of refinements in positive-rank GL over every actual finite p-adic
extension. -/
def PadicProductLeviGeometricLemmaTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n → ∀ (B : BlockShape n)
      (Q S : BlockRefinement B),
      ProductLeviGeometricLemmaTheorem.{uF, uV} T B Q S

end Langlands.Geometric
