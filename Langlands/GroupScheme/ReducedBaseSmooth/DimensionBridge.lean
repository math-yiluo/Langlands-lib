import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof
import Langlands.AlgebraicGeometry.SmoothPureDimensionProof

/-! # Locally constant fibre dimension gives a locally constant relative dimension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.ReducedBaseSmooth

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- A nonempty scheme smooth of relative dimension `n` over a field has topological Krull
dimension `n`. -/
theorem topologicalKrullDim_eq_of_smoothOfRelativeDimension (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    [Nonempty X] : topologicalKrullDim X = (n : WithBot ℕ∞) := by
  rw [topologicalKrullDim_eq_iSup_at]
  simp only [fieldSmooth_topologicalKrullDimAt k X f n]
  exact iSup_const

/-- If every residue fibre of `f` is smooth and connected and the topological dimension of the
fibres is locally constant, then every point of the base has an open neighbourhood over which
all residue fibres are smooth of one relative dimension `n`. -/
theorem exists_open_smoothOfRelativeDimension_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    (hsm : ∀ s : S, Smooth (f.fiberToSpecResidueField s))
    (hconn : ∀ s : S, ConnectedSpace (f.fiber s))
    (hlc : IsLocallyConstant (fun s : S => topologicalKrullDim (f.fiber s))) (s : S) :
    ∃ (U : S.Opens) (n : ℕ), s ∈ U ∧
      ∀ t ∈ U, SmoothOfRelativeDimension n (f.fiberToSpecResidueField t) := by
  have hdim : ∀ t : S, ∃ n : ℕ, SmoothOfRelativeDimension n (f.fiberToSpecResidueField t) ∧
      topologicalKrullDim (f.fiber t) = (n : WithBot ℕ∞) := by
    intro t
    obtain ⟨n, hn⟩ := smoothConnectedRelativeDimension _ _ (f.fiberToSpecResidueField t)
      (hsm t) (hconn t)
    have : Nonempty (f.fiber t) := (hconn t).toNonempty
    exact ⟨n, hn, topologicalKrullDim_eq_of_smoothOfRelativeDimension (S.residueField t) _
      (f.fiberToSpecResidueField t) n⟩
  obtain ⟨n, hn, hns⟩ := hdim s
  refine ⟨⟨_, hlc.isOpen_fiber (topologicalKrullDim (f.fiber s))⟩, n, rfl, ?_⟩
  intro t ht
  obtain ⟨m, hm, hmt⟩ := hdim t
  have hcast : (m : WithBot ℕ∞) = n := by
    rw [← hmt, ← hns]
    exact ht
  have hmn : m = n := by exact_mod_cast hcast
  exact hmn ▸ hm

end Langlands.GroupScheme.ReducedBaseSmooth
