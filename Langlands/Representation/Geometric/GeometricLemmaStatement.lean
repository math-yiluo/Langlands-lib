import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Geometric.IntersectionTransport
import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Filtration.Definitions

/-! BZ77's normalized geometric lemma on actual smooth GL representations. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CategoryTheory

universe uF uV

section EqualityTransport

variable {G : Type uF} [Group G] [TopologicalSpace G]

/-- Relabel smooth representations along equality of their actual subgroups.
After equality elimination this is the identity functor. -/
def subgroupEqualityFunctor (H K : Subgroup G) (h : H = K) :
    SmoothRep.{0, uF, uV} ℂ H ⥤ SmoothRep.{0, uF, uV} ℂ K := by
  subst K
  exact 𝟭 _

end EqualityTransport

/-- All three actual intersection groups agree with a standard refinement. -/
def IsIntersectionRefinement {F : Type uF} [CommRing F] {n : ℕ}
    (B C : BlockShape n) (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) : Prop :=
  sourceParabolic F B C w = refinedParabolic F B S ∧
  sourceLevi F B C w = refinedLevi F B S ∧
  sourceUnipotent F B C w = refinedUnipotent F B S

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)

/-- The actual graded functor: normalized inner Jacquet, inverse-conjugation
transport, then normalized inner induction. The equalities only relabel the
same concrete subgroup; their existence is part of the theorem below. -/
def geometricPieceFunctor (w : Equiv.Perm (Fin n))
    (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) ⥤
      Rep.{max uF uV} ℂ (C.Levi F.Carrier) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact T.normalizedRefinedJacquetFunctor B S ⋙
    subgroupEqualityFunctor _ _ hS.symm ⋙
    intersectionTransportFunctor F.Carrier B C w ⋙
    subgroupEqualityFunctor _ _ hR ⋙
    T.normalizedRefinedInductionFunctor C R ⋙ SmoothRep.toRep

/-- The actual composition whose natural filtration is asserted. -/
def jacquetInductionFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) ⥤
      Rep.{max uF uV} ℂ (C.Levi F.Carrier) := by
  letI := T.topology
  exact T.normalizedParabolicInductionFunctor B ⋙
    T.normalizedJacquetFunctor C ⋙ SmoothRep.toRep

/-- BZ77 2.12 together with its concrete standard-intersection identifications.
Refinements, equalities, enumeration, filtration and natural graded
isomorphisms are all conclusions, never theorem-valued parameters. -/
def GeometricLemmaTheorem : Prop :=
  letI := T.topology
  ∃ (S : MinimalRepresentatives B C → BlockRefinement B)
    (R : MinimalRepresentatives B C → BlockRefinement C),
    ∃ (hS : ∀ w, IsIntersectionRefinement (F := F.Carrier) B C w.val (S w))
      (hR : ∀ w, IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ (R w)),
      ∃ (m : ℕ) (e : Fin m ≃ MinimalRepresentatives B C),
        IsGluedFrom (jacquetInductionFunctor.{uF, uV} T B C)
          (fun i => geometricPieceFunctor T B C (e i).val
            (S (e i)) (R (e i)) (hS (e i)).2.1 (hR (e i)).2.1)

/-- The normalized geometric lemma for every pair of standard Levis in
positive-rank GL over every actual finite p-adic extension. -/
def PadicGeometricLemmaTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n → ∀ B C : BlockShape n,
      GeometricLemmaTheorem.{uF, uV} T B C

end Langlands.Geometric
