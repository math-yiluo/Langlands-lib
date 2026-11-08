import Langlands.Representation.Category.Basic
import Langlands.Representation.Category.RestrictionSubquotients
import Langlands.Representation.Unitary.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-! # Smooth representations of compact t.d. groups and an admissibility criterion
(Renard IV.1.1 and IV.1.2)

For a compact totally disconnected group `K`: irreducible smooth representations are
finite-dimensional; a finite-dimensional smooth representation is trivial on an open normal
subgroup; every smooth representation is semisimple and unitarizable. For a t.d. group `G`, a
smooth representation is admissible exactly when every irreducible smooth representation of
every compact open subgroup occurs in it with finite multiplicity.
-/

universe u v

open CategoryTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.1.1, Theorem: let `K` be a compact totally disconnected Hausdorff topological
group and `π` a smooth complex representation of `K`.

* (i) If `π` is irreducible, it is finite-dimensional.
* (ii) If `π` is finite-dimensional, some open normal subgroup of `K` acts trivially.
* (iii) `π` is semisimple (as a module over the group algebra).
* (iv) `π` is unitarizable: it admits a `K`-invariant positive definite Hermitian form. -/
def CompactGroupSmoothRepresentationStatement : Prop :=
  ∀ (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [T2Space K] [TotallyDisconnectedSpace K] (π : SmoothRep.{0, u, v} ℂ K),
    (π.IsIrreducible → FiniteDimensional ℂ π) ∧
    (FiniteDimensional ℂ π →
      ∃ N : OpenSubgroup K, (N : Subgroup K).Normal ∧
        ∀ n ∈ N, ∀ x : π, π.representation n x = x) ∧
    IsSemisimpleModule (MonoidAlgebra ℂ K) π.representation.asModule ∧
    IsUnitarizable π.representation

/-- Renard IV.1.2, Proposition: let `G` be a locally compact totally disconnected Hausdorff
topological group and `π` a smooth complex representation of `G`. Then `π` is admissible if
and only if, for every compact open subgroup `K` of `G` and every irreducible smooth
representation `σ` of `K`, the multiplicity `dim Hom_K(σ, π|_K)` is finite. -/
def AdmissibleFiniteMultiplicityStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (π : SmoothRep.{0, u, v} ℂ G),
    π.IsAdmissible ↔
      ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
        ∀ σ : SmoothRep.{0, u, v} ℂ (K : Subgroup G), σ.IsIrreducible →
          FiniteDimensional ℂ (σ.representation.IntertwiningMap
            (SmoothRep.restrictSubgroup (K : Subgroup G) π).representation)

/-- The two statements above. -/
def CompactGroupSmoothStatements.{u', v'} : Prop :=
  CompactGroupSmoothRepresentationStatement.{u', v'} ∧
    AdmissibleFiniteMultiplicityStatement.{u', v'}

end Langlands.Renard.CompactRepresentation
