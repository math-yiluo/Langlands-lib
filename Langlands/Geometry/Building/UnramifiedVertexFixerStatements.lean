import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness
import Mathlib.GroupTheory.Index

/-! # Vertex fixers and finite vertex approximation over the unramified field -/

noncomputable section

universe u

open AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.MaximalUnramified

private instance unramifiedVertexFixerAffine
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom] : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- KP Theorem 4.2.15(1), restricted to the actual maximal unramified field:
the norm-one fixer of any vertex is maximal among algebraically bounded
subgroups of the original rational-point group. -/
def VertexOneStabilizerMaximalBoundedStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : BuildingData F G) (y : C.ReducedBuilding),
    C.IsVertex y →
    letI := ValuativeRel.ofValuation (fixedFieldValued F).v
    Maximal (fun B : Subgroup (rationalPoints G) =>
      IsAlgebraicallyBounded (inertiaFixedField F) G.X
        (B : Set (rationalPoints G))) (C.oneStabilizer y)

/-- The geometric finite-index approximation used in KP 8.3.1--8.3.2.
A nonempty bounded subset of a translated apartment has a norm-one pointwise
fixer containing, normally and with finite index, an intersection of finitely
many nonempty vertex fixers. No integral model is assumed or constructed. -/
def FiniteVertexFixerApproximationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : BuildingData F G) (g : rationalPoints G) (Ωa : Set C.Apartment),
    Ωa.Nonempty →
    (∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ωa)) →
    ∃ Y : Finset C.ReducedBuilding,
      Y.Nonempty ∧ (∀ y ∈ Y, C.IsVertex y) ∧
      let U : Subgroup (rationalPoints G) := ⨅ y ∈ Y, C.oneStabilizer y
      let H := characterValuationKernel (valuation F) G ⊓
        C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa)
      U ≤ H ∧ (U.subgroupOf H).Normal ∧ (U.subgroupOf H).FiniteIndex

/-- The two model-free building inputs to the full-model construction over the
actual maximal unramified integers. Both assertions remain unproved here. -/
def VertexFixerApproximationStatement : Prop :=
  VertexOneStabilizerMaximalBoundedStatement.{u} ∧
    FiniteVertexFixerApproximationStatement.{u}

end Langlands.Geometry.Building.MaximalUnramified
