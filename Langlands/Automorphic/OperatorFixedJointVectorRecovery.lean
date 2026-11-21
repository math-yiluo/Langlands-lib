import Langlands.Automorphic.OperatorJointVectorRecovery
import Langlands.Representation.Archimedean.SmoothFixedSubspace

/-! # Recovery at a fixed finite level -/

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff

namespace Langlands.Automorphic.OperatorUnitaryFormCore

open Langlands.Archimedean Langlands.Archimedean.SmoothInvariantSubspace

universe uG uK uV uX uA uGarch

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {K : Type uK} [Group K] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {X : Type uX} {ρ : Representation ℂ G V} {κ : Representation ℂ K V}
  {D : X → Module.End ℂ V}

/-- An open-level fixed, compact-finite vector recovers to the original
carrier at the same fixed level. -/
theorem exists_fixed_toHilbert_of_compactFinite (b : OperatorUnitaryFormCore ρ κ D)
    (hrec : b.JointVectorRecovery) (J : OpenSubgroup G) (x : b.HilbertCompletion)
    (hxJ : x ∈ Langlands.fixedVectors b.completedFiniteRepresentation J.toSubgroup)
    (hxK : Langlands.FiniteVectors.IsFiniteVector b.completedCompactRepresentation x) :
    ∃ v : Langlands.fixedVectors ρ J.toSubgroup, b.toHilbert (v : V) = x := by
  obtain ⟨v, hv⟩ := (hrec x).mp ⟨⟨J, hxJ⟩, hxK⟩
  have hvJ : v ∈ Langlands.fixedVectors ρ J.toSubgroup := by
    intro d
    exact b.toHilbert_injective
      ((b.completedFiniteRepresentation_toHilbert d.val v).symm.trans
        ((congrArg (b.completedFiniteRepresentation d.val) hv).trans
          ((hxJ d).trans hv.symm)))
  exact ⟨⟨v, hvJ⟩, hv⟩

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {Garch : Type uGarch} [Group Garch] [TopologicalSpace Garch] [ChartedSpace A Garch]
  [LieGroup 𝓘(ℝ, A) ∞ Garch] (b : OperatorUnitaryFormCore ρ κ D)
  (σ : G →* (b.HilbertCompletion →L[ℂ] b.HilbertCompletion)) (J : OpenSubgroup G)
  (π : Garch →* (b.HilbertCompletion →L[ℂ] b.HilbertCompletion))

local notation "I" => 𝓘(ℝ, A)

/-- The genuine fixed smooth vectors with original fixed preimages. -/
def fixedSmoothImage : Set (ambientFixedSmoothSubspace σ J.toSubgroup π I) :=
  {w | ∃ v : Langlands.fixedVectors ρ J.toSubgroup,
    b.toHilbert v.val = (DerivativeSmoothVectors.toSmooth I π w.val).val}

/-- A dense set of compact-finite smooth vectors at the fixed level gives
derivative density of the original fixed smooth image. -/
theorem dense_fixedSmoothImage_of_dense_compactFinite
    (hrec : b.JointVectorRecovery)
    (hfinite : ∀ d x, σ d x = b.completedFiniteRepresentation d x)
    (hd : Dense {w : ambientFixedSmoothSubspace σ J.toSubgroup π I |
      FiniteVectors.IsFiniteVector b.completedCompactRepresentation
        (DerivativeSmoothVectors.toSmooth I π w.val).val}) :
    Dense (fixedSmoothImage (A := A) b σ J π) := by
  refine hd.mono ?_
  intro w hw
  let x := (DerivativeSmoothVectors.toSmooth I π w.val).val
  have hfixed : x ∈ fixedSubspace σ J.toSubgroup :=
    (mem_ambientSmoothSubspace π (fixedSubspace σ J.toSubgroup) I w.val).mp w.property
  have hxJ : x ∈ Langlands.fixedVectors b.completedFiniteRepresentation J.toSubgroup :=
    fun d => (hfinite d x).symm.trans ((mem_fixedSubspace_iff σ J.toSubgroup x).mp hfixed d)
  exact exists_fixed_toHilbert_of_compactFinite b hrec J x hxJ hw

end Langlands.Automorphic.OperatorUnitaryFormCore
