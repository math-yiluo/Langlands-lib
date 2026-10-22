import Langlands.Representation.CompactCoefficient.Isotypic
import Mathlib.LinearAlgebra.Projection

/-!
# Conditional equivariant projections

Complementary invariant subspaces give an equivariant projection. Its
naturality specializes to the intrinsic compact-coefficient isotypic and
annihilator subspaces, with independent source and target carrier universes.
Complementarity is an explicit hypothesis throughout.
-/

noncomputable section

namespace Langlands

section Linear

variable {R V W : Type*} [Ring R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

/-- A linear map preserving both summands commutes with the corresponding
projections, also when the source and target carriers have different universes. -/
theorem projection_natural_of_mapsTo
    {S Q : Submodule R V} {S' Q' : Submodule R W}
    (h : IsCompl S Q) (h' : IsCompl S' Q') (f : V →ₗ[R] W)
    (hS : Set.MapsTo f S S') (hQ : Set.MapsTo f Q Q') (v : V) :
    f (S.projection Q h v) = S'.projection Q' h' (f v) := by
  obtain ⟨s, q, rfl, _⟩ := S.existsUnique_add_of_isCompl h v
  simp only [map_add, Submodule.projection_apply_left, Submodule.projection_apply_right,
    add_zero]
  rw [Submodule.projection_apply_of_mem_left h' (hS s.property),
    Submodule.projection_apply_of_mem_right h' (hQ q.property), add_zero]

end Linear

section Equivariant

open Representation

variable {R G V W : Type*} [CommRing R] [Monoid G]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {ρ : Representation R G V} {σ : Representation R G W}

/-- Projection onto an invariant subspace along a supplied invariant complement. -/
def equivariantProjection (S Q : Subrepresentation ρ)
    (h : IsCompl S.toSubmodule Q.toSubmodule) : ρ.IntertwiningMap ρ where
  toLinearMap := S.toSubmodule.projection Q.toSubmodule h
  isIntertwining' g := by
    ext v
    exact (projection_natural_of_mapsTo h h (ρ g)
      (fun _ hv => S.apply_mem_toSubmodule g hv)
      (fun _ hv => Q.apply_mem_toSubmodule g hv) v).symm

@[simp]
theorem equivariantProjection_range (S Q : Subrepresentation ρ)
    (h : IsCompl S.toSubmodule Q.toSubmodule) :
    (equivariantProjection S Q h).range = S := by
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.range_projection h

@[simp]
theorem equivariantProjection_ker (S Q : Subrepresentation ρ)
    (h : IsCompl S.toSubmodule Q.toSubmodule) :
    (equivariantProjection S Q h).ker = Q := by
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.ker_projection h

theorem equivariantProjection_idempotent (S Q : Subrepresentation ρ)
    (h : IsCompl S.toSubmodule Q.toSubmodule) :
    IsIdempotentElem (equivariantProjection S Q h).toLinearMap :=
  Submodule.isIdempotentElem_projection h

/-- The projection is natural for every intertwiner preserving both summands. -/
theorem equivariantProjection_natural
    {S Q : Subrepresentation ρ} {S' Q' : Subrepresentation σ}
    (h : IsCompl S.toSubmodule Q.toSubmodule)
    (h' : IsCompl S'.toSubmodule Q'.toSubmodule)
    (f : ρ.IntertwiningMap σ)
    (hS : Set.MapsTo f (S : Set V) (S' : Set W))
    (hQ : Set.MapsTo f (Q : Set V) (Q' : Set W)) (v : V) :
    f (equivariantProjection S Q h v) =
      equivariantProjection S' Q' h' (f v) :=
  projection_natural_of_mapsTo h h' f.toLinearMap hS hQ v

/-- An equivariant idempotent with the prescribed range and kernel is this
projection. This uses Mathlib's uniqueness theorem for linear idempotents. -/
theorem equivariantProjection_unique (S Q : Subrepresentation ρ)
    (h : IsCompl S.toSubmodule Q.toSubmodule) (P : ρ.IntertwiningMap ρ)
    (hP : IsIdempotentElem P.toLinearMap) (hS : P.range = S) (hQ : P.ker = Q) :
    P = equivariantProjection S Q h := by
  apply IntertwiningMap.ext
  apply (LinearMap.IsIdempotentElem.ext_iff hP
    (equivariantProjection_idempotent S Q h)).2
  constructor
  · change P.range.toSubmodule = (equivariantProjection S Q h).range.toSubmodule
    rw [hS, equivariantProjection_range]
  · change P.ker.toSubmodule = (equivariantProjection S Q h).ker.toSubmodule
    rw [hQ, equivariantProjection_ker]

end Equivariant

namespace CompactCoefficientClass

universe uG uV uW uX

variable {G : Type uG} [Group G] [TopologicalSpace G]
  (c : CompactCoefficientClass.{uG, uV} G)
  {A : SmoothRep.{0, uG, uW} ℂ G} {B : SmoothRep.{0, uG, uX} ℂ G}

/-- The intrinsic isotypic projection, conditional on the isotypic and
annihilator subspaces being complementary. -/
def isotypicProjectorOfIsCompl
    (h : IsCompl (isotypicSubrepresentation c A).toSubmodule
      (annihilatorSubrepresentation c A).toSubmodule) :
    A.representation.IntertwiningMap A.representation :=
  equivariantProjection (isotypicSubrepresentation c A) (annihilatorSubrepresentation c A) h

@[simp]
theorem isotypicProjectorOfIsCompl_range
    (h : IsCompl (isotypicSubrepresentation c A).toSubmodule
      (annihilatorSubrepresentation c A).toSubmodule) :
    (isotypicProjectorOfIsCompl c h).range = isotypicSubrepresentation c A :=
  equivariantProjection_range _ _ h

@[simp]
theorem isotypicProjectorOfIsCompl_ker
    (h : IsCompl (isotypicSubrepresentation c A).toSubmodule
      (annihilatorSubrepresentation c A).toSubmodule) :
    (isotypicProjectorOfIsCompl c h).ker = annihilatorSubrepresentation c A :=
  equivariantProjection_ker _ _ h

theorem isotypicProjectorOfIsCompl_idempotent
    (h : IsCompl (isotypicSubrepresentation c A).toSubmodule
      (annihilatorSubrepresentation c A).toSubmodule) :
    IsIdempotentElem (isotypicProjectorOfIsCompl c h).toLinearMap :=
  equivariantProjection_idempotent _ _ h

/-- Cross-universe naturality follows from the published intrinsic MapsTo laws. -/
theorem isotypicProjectorOfIsCompl_natural
    (hA : IsCompl (isotypicSubrepresentation c A).toSubmodule
      (annihilatorSubrepresentation c A).toSubmodule)
    (hB : IsCompl (isotypicSubrepresentation c B).toSubmodule
      (annihilatorSubrepresentation c B).toSubmodule)
    (f : A.representation.IntertwiningMap B.representation) (v : A) :
    f (isotypicProjectorOfIsCompl c hA v) =
      isotypicProjectorOfIsCompl c hB (f v) :=
  equivariantProjection_natural hA hB f
    (mapsTo_isotypicSubrepresentation c f) (mapsTo_annihilatorSubrepresentation c f) v

/-- Arbitrarily supplied idempotents with the intrinsic ranges and kernels
are automatically natural, even across independent ambient universes. -/
theorem isotypicProjectors_natural
    (P : A.representation.IntertwiningMap A.representation)
    (Q : B.representation.IntertwiningMap B.representation)
    (hP : IsIdempotentElem P.toLinearMap) (hQ : IsIdempotentElem Q.toLinearMap)
    (hPr : P.range = isotypicSubrepresentation c A)
    (hPk : P.ker = annihilatorSubrepresentation c A)
    (hQr : Q.range = isotypicSubrepresentation c B)
    (hQk : Q.ker = annihilatorSubrepresentation c B)
    (f : A.representation.IntertwiningMap B.representation) (v : A) :
    f (P v) = Q (f v) := by
  have hA : IsCompl (isotypicSubrepresentation c A).toSubmodule
      (annihilatorSubrepresentation c A).toSubmodule := by
    rw [← hPr, ← hPk]
    exact LinearMap.IsIdempotentElem.isCompl hP
  have hB : IsCompl (isotypicSubrepresentation c B).toSubmodule
      (annihilatorSubrepresentation c B).toSubmodule := by
    rw [← hQr, ← hQk]
    exact LinearMap.IsIdempotentElem.isCompl hQ
  rw [equivariantProjection_unique _ _ hA P hP hPr hPk,
    equivariantProjection_unique _ _ hB Q hQ hQr hQk]
  exact isotypicProjectorOfIsCompl_natural c hA hB f v

end CompactCoefficientClass

end Langlands
