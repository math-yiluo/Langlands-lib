import Langlands.Representation.Category.Basic
import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.Hecke.ActionProjection

/-! # Compact representations (Renard IV.1.3)

Renard calls a smooth representation `(π, V)` of a t.d. group compact when, for every `v ∈ V`
and every compact open subgroup `K`, the function `f_{K,v} : g ↦ π(e_K) π(g⁻¹) v` has compact
support. This module states that this is equivalent to compact support of all smooth matrix
coefficients, that compact representations of finite type are admissible, and that the
existence of a nonzero compact representation forces a compact centre for groups countable
at infinity.
-/

noncomputable section

universe u v

open CategoryTheory MeasureTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.1.3, Theorem, with Renard's definition of compact representations: for a smooth
representation `π` of a t.d. group `G` with a Haar measure `μ`, the functions
`f_{K,x}(g) = π(e_K) π(g⁻¹) x` (`π(e_K)` the published projection onto the `K`-fixed vectors)
have compact support for every compact open `K` and every `x` if and only if every smooth
matrix coefficient of `π` has compact support. -/
def CompactRepresentationCoefficientCriterionStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (π : SmoothRep.{0, u, v} ℂ G),
    (∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : π),
        HasCompactSupport (fun g : G =>
          Hecke.fixedProjection μ π.representation π.isSmooth K hK
            (π.representation g⁻¹ x))) ↔
      HasCompactSmoothDualCoefficients π.representation

/-- Renard IV.1.3, Proposition: a smooth representation of a t.d. group whose smooth matrix
coefficients have compact support and which is finitely generated over the group algebra is
admissible. -/
def CompactFiniteTypeAdmissibleStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (π : SmoothRep.{0, u, v} ℂ G),
    HasCompactSmoothDualCoefficients π.representation →
      Module.Finite (MonoidAlgebra ℂ G) π.representation.asModule → π.IsAdmissible

/-- Renard IV.1.3, Lemma: if a t.d. group `G` countable at infinity has a nonzero smooth
representation whose smooth matrix coefficients have compact support, then the centre of `G`
is compact. -/
def CompactRepresentationCompactCenterStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    (π : SmoothRep.{0, u, v} ℂ G),
    Nontrivial π → HasCompactSmoothDualCoefficients π.representation →
      IsCompact (Subgroup.center G : Set G)

/-- The three statements above. -/
def CompactRepresentationCriterionStatements.{u', v'} : Prop :=
  CompactRepresentationCoefficientCriterionStatement.{u', v'} ∧
    CompactFiniteTypeAdmissibleStatement.{u', v'} ∧
    CompactRepresentationCompactCenterStatement.{u', v'}

end Langlands.Renard.CompactRepresentation
