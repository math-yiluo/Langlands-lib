import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.SubrepresentationLattice
import Mathlib.MeasureTheory.Group.Measure

/-! # The isotypic decomposition along an irreducible compact representation (Renard IV.1.4)

For an irreducible representation `τ` with compactly supported coefficients of a unimodular
t.d. group countable at infinity, every smooth representation `V` is `V(τ) ⊕ V(τ)^⊥`, where
`V(τ)` is a direct sum of copies of `τ` and no irreducible subquotient of `V(τ)^⊥` is
isomorphic to `τ`; the complement `V(τ)^⊥` is the only invariant complement of `V(τ)`.
-/

noncomputable section

universe u v

open CategoryTheory MeasureTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.1.4, Theorem, with IV.1.5, Proposition (iii) and Remark 1: let `G` be a
Hausdorff, locally compact, totally disconnected group, countable at infinity, admitting a
Haar measure that is also right invariant (`G` is unimodular), and `τ` an irreducible smooth
representation with compactly supported smooth coefficients. For every smooth representation
`V`, let `V(τ)` be the sum of the images of all intertwiners `τ → V`. Then

* `V(τ)` is the direct sum of the images of a family of injective intertwiners `τ → V`;
* `V(τ)` has exactly one invariant complement;
* no irreducible subquotient of an invariant complement of `V(τ)` is isomorphic to `τ`. -/
def CompactIsotypicComplementStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [μ.IsMulRightInvariant] (τ : SmoothRep.{0, u, v} ℂ G),
    τ.IsIrreducible → HasCompactSmoothDualCoefficients τ.representation →
    ∀ V : SmoothRep.{0, u, v} ℂ G,
      let isotypic : Subrepresentation V.representation :=
        ⨆ f : τ.representation.IntertwiningMap V.representation, f.range
      (∃ s : Set (τ.representation.IntertwiningMap V.representation),
        (∀ f ∈ s, Function.Injective f) ∧
          iSupIndep (fun f : s =>
            (f : τ.representation.IntertwiningMap V.representation).range) ∧
          ⨆ f : s, (f : τ.representation.IntertwiningMap V.representation).range =
            isotypic) ∧
        (∃! S : Subrepresentation V.representation, IsCompl isotypic S) ∧
        ∀ S : Subrepresentation V.representation, IsCompl isotypic S →
          ∀ B : SmoothRep.{0, u, v} ℂ G,
            SmoothRep.IsSubquotient B (SmoothRep.subrepresentation V S) → IsEmpty (B ≅ τ)

end Langlands.Renard.CompactRepresentation
