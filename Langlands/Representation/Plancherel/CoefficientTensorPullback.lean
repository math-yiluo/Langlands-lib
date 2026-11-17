import Langlands.Representation.Plancherel.CoefficientTensors
import Langlands.Representation.CompactCoefficient.GroupTransport

/-! # Coefficient tensors under a topological group equivalence

For a continuous group isomorphism `e : H ≃ₜ* G` and a smooth representation `A` of `G`,
the pullback `SmoothRep.pullback e A` has the same vectors and the same smooth functionals.
Hence its coefficient tensors are those of `A`, and coefficients are precomposed with `e`.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.Plancherel

universe uG uH uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The smooth functionals of a pullback along a topological group equivalence are the
smooth functionals of the original representation. -/
theorem smoothVectors_dual_comp_continuousMulEquiv {V : Type uV} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (e : H ≃ₜ* G) :
    smoothVectors (Representation.dual (ρ.comp e.toMonoidHom)) = smoothVectors ρ.dual :=
  Submodule.ext fun ℓ => isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ

/-- The identity of algebraic functionals, as an equivalence of smooth duals. -/
def smoothDualPullbackEquiv (e : H ≃ₜ* G) (A : SmoothRep.{0, uG, uV} ℂ G) :
    SmoothDual A.representation ≃ₗ[ℂ] SmoothDual (SmoothRep.pullback e A).representation :=
  LinearEquiv.ofEq _ _ (smoothVectors_dual_comp_continuousMulEquiv A.representation e).symm

set_option linter.unusedSectionVars false in
@[simp]
theorem smoothDualPullbackEquiv_val (e : H ≃ₜ* G) (A : SmoothRep.{0, uG, uV} ℂ G)
    (ℓ : SmoothDual A.representation) :
    (smoothDualPullbackEquiv e A ℓ).val = ℓ.val :=
  rfl

/-- Coefficient tensors of the pullback: the same vector and the same algebraic
functional in each pure tensor. -/
def coefficientTensorPullbackEquiv (e : H ≃ₜ* G) (A : SmoothRep.{0, uG, uV} ℂ G) :
    CoefficientTensor A ≃ₗ[ℂ] CoefficientTensor (SmoothRep.pullback e A) :=
  TensorProduct.congr (LinearEquiv.refl ℂ A) (smoothDualPullbackEquiv e A)

set_option linter.unusedSectionVars false in
@[simp]
theorem coefficientTensorPullbackEquiv_tmul (e : H ≃ₜ* G) (A : SmoothRep.{0, uG, uV} ℂ G)
    (v : A) (ℓ : SmoothDual A.representation) :
    coefficientTensorPullbackEquiv e A (v ⊗ₜ[ℂ] ℓ) =
      (v : SmoothRep.pullback e A) ⊗ₜ[ℂ] smoothDualPullbackEquiv e A ℓ :=
  rfl

/-- Coefficients of transported tensors are the original coefficients precomposed with
the group equivalence. -/
theorem coefficientTensorMap_coefficientTensorPullbackEquiv (e : H ≃ₜ* G)
    (A : SmoothRep.{0, uG, uV} ℂ G) (t : CoefficientTensor A) (h : H) :
    coefficientTensorMap (SmoothRep.pullback e A) (coefficientTensorPullbackEquiv e A t) h =
      coefficientTensorMap A t (e h) := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ => rfl
  | add t u ht hu =>
    simp only [map_add, LocallyConstant.add_apply, ht, hu]

/-- The same identity as functions on `H`. -/
theorem coe_coefficientTensorMap_coefficientTensorPullbackEquiv (e : H ≃ₜ* G)
    (A : SmoothRep.{0, uG, uV} ℂ G) (t : CoefficientTensor A) :
    (coefficientTensorMap (SmoothRep.pullback e A) (coefficientTensorPullbackEquiv e A t) :
        H → ℂ) = (coefficientTensorMap A t : G → ℂ) ∘ e := by
  funext h
  exact coefficientTensorMap_coefficientTensorPullbackEquiv e A t h

/-- The external `H × H` action on transported tensors is the external `G × G` action at
the image pair. -/
theorem coefficientTensorAction_coefficientTensorPullbackEquiv (e : H ≃ₜ* G)
    (A : SmoothRep.{0, uG, uV} ℂ G) (x : H × H) (t : CoefficientTensor A) :
    coefficientTensorAction (SmoothRep.pullback e A) x (coefficientTensorPullbackEquiv e A t) =
      coefficientTensorPullbackEquiv e A (coefficientTensorAction A (e x.1, e x.2) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    change (A.representation (e x.1) v : SmoothRep.pullback e A) ⊗ₜ[ℂ]
        smoothContragredient (SmoothRep.pullback e A).representation x.2
          (smoothDualPullbackEquiv e A ℓ) =
      (A.representation (e x.1) v : SmoothRep.pullback e A) ⊗ₜ[ℂ]
        smoothDualPullbackEquiv e A (smoothContragredient A.representation (e x.2) ℓ)
    congr 1
    apply Subtype.ext
    change (Representation.dual (A.representation.comp e.toMonoidHom)) x.2 ℓ.val =
      A.representation.dual (e x.2) ℓ.val
    rw [dual_comp_monoidHom]
    rfl
  | add t u ht hu => rw [map_add, map_add, map_add, map_add, ht, hu]

end Langlands.Plancherel
