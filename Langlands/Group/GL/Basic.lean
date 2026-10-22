import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# General linear groups and their basic continuous maps

The group is Mathlib's group of units of the matrix ring, without an additional
group wrapper. See the paired Markdown for the hypotheses and source conventions.
-/

namespace Langlands

universe u v w

/-- The general linear group on the standard `n` coordinates. -/
abbrev GeneralLinear (n : ℕ) (R : Type u) [CommRing R] :=
  Matrix.GeneralLinearGroup (Fin n) R

namespace GeneralLinear

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The usual determinant with values in the units of the coefficient ring. -/
abbrev determinant : GeneralLinear n R →* Rˣ :=
  Matrix.GeneralLinearGroup.det

/-- The usual scalar matrix homomorphism. -/
abbrev scalar : Rˣ →* GeneralLinear n R :=
  Matrix.GeneralLinearGroup.scalar (Fin n)

/-- Scalar matrices, with their centrality certificate. -/
def scalarToCenter : Rˣ →* Subgroup.center (GeneralLinear n R) :=
  scalar.codRestrict _ fun a =>
    Subgroup.mem_center_iff.mpr fun g =>
      (Matrix.GeneralLinearGroup.scalar_commute a g).symm

/-- For positive rank, the scalar homomorphism is an embedding. -/
def scalarEmbedding (hn : 0 < n) : Rˣ ↪ GeneralLinear n R where
  toFun := scalar
  inj' := by
    intro a b h
    apply Units.ext
    have hd := congrArg (fun g : GeneralLinear n R => g ⟨0, hn⟩ ⟨0, hn⟩) h
    simpa [scalar, Matrix.scalar_apply] using hd

section Topology

variable [TopologicalSpace R]

/-- Evaluation of a matrix entry as a continuous map. -/
def entry (i j : Fin n) : C(GeneralLinear n R, R) where
  toFun g := g i j
  continuous_toFun :=
    (continuous_apply j).comp
      (Matrix.GeneralLinearGroup.continuous_apply _ continuous_id i)

/-- The scalar homomorphism with its continuity certificate. -/
def scalarContinuous : ContinuousMonoidHom Rˣ (GeneralLinear n R) where
  toMonoidHom := scalar
  continuous_toFun := by
    apply Continuous.units_map
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_if_const _ (fun _ => continuous_id) (fun _ => continuous_const)

variable [IsTopologicalRing R]

/-- The determinant as a continuous homomorphism to the unit group. -/
def determinantContinuous : ContinuousMonoidHom (GeneralLinear n R) Rˣ where
  toMonoidHom := determinant
  continuous_toFun := Matrix.GeneralLinearGroup.continuous_det

/-- Change of coefficients induced by a continuous ring homomorphism. -/
def mapContinuous {S : Type v} [CommRing S] [TopologicalSpace S]
    (f : R →+* S) (hf : Continuous f) :
    ContinuousMonoidHom (GeneralLinear n R) (GeneralLinear n S) where
  toMonoidHom := Matrix.GeneralLinearGroup.map f
  continuous_toFun := hf.generalLinearGroup_map

end Topology

section Reindex

variable {ι : Type v} {κ : Type w} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Simultaneously relabel rows and columns of an invertible matrix. -/
def reindex (e : ι ≃ κ) :
    Matrix.GeneralLinearGroup ι R ≃* Matrix.GeneralLinearGroup κ R :=
  Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv

variable [TopologicalSpace R]

/-- Reindexing is an isomorphism of topological groups. -/
def reindexContinuous (e : ι ≃ κ) :
    Matrix.GeneralLinearGroup ι R ≃ₜ* Matrix.GeneralLinearGroup κ R :=
  Units.mapContinuousMulEquiv
    { toMulEquiv := (Matrix.reindexRingEquiv R e).toMulEquiv
      continuous_toFun := continuous_pi fun i =>
        continuous_pi fun j =>
          (continuous_apply (e.symm j)).comp (continuous_apply (e.symm i))
      continuous_invFun := continuous_pi fun i =>
        continuous_pi fun j =>
          (continuous_apply (e j)).comp (continuous_apply (e i)) }

end Reindex

end GeneralLinear
end Langlands
