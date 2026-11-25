import Langlands.Analysis.Meromorphic.ScalarIdentity
import Langlands.Analysis.Meromorphic.IdentityTheorem
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Products and determinants of scalar meromorphic functions -/

noncomputable section

open Set
open scoped Manifold

set_option autoImplicit false

namespace Langlands.Global.EisensteinGenericInjectivity

open Langlands.Analysis.Meromorphic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E}

/-- A finite product of scalar meromorphic functions with a common open dense holomorphy domain
is meromorphic there. -/
theorem isMeromorphicOn_prod {ι : Type*} (s : Finset ι) {a : ι → E → ℂ}
    (hU : IsOpen U) (hdU : Dense U) (ha : ∀ i ∈ s, IsMeromorphicOn 𝓘(ℂ, E) (a i) U) :
    IsMeromorphicOn 𝓘(ℂ, E) (∏ i ∈ s, a i) U := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact (isMeromorphicOn_const (E := E) 1).restrict_domain hU hdU (subset_univ U)
  | @insert i t hi ih =>
    have hai := ha i (Finset.mem_insert_self i t)
    have hat := ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi]
    simpa only [inter_self] using hai.mul hat

/-- The determinant of a matrix of scalar meromorphic functions with a common open dense
holomorphy domain is meromorphic there. -/
theorem isMeromorphicOn_det {m : ℕ} (f : Fin m → Fin m → E → ℂ) (hU : IsOpen U) (hdU : Dense U)
    (hf : ∀ i k, IsMeromorphicOn 𝓘(ℂ, E) (f i k) U) :
    IsMeromorphicOn 𝓘(ℂ, E) (fun s => (Matrix.of fun i k => f i k s).det) U := by
  have h := IsMeromorphicOn.sum (Finset.univ : Finset (Equiv.Perm (Fin m))) hU hdU
    (a := fun σ s => (∏ i, f (σ i) i s) * (Equiv.Perm.sign σ : ℂ))
    (fun σ _ => by
      have hp := isMeromorphicOn_prod (Finset.univ : Finset (Fin m)) hU hdU
        (a := fun i => f (σ i) i) (fun i _ => hf _ _)
      convert hp.mul_const (Equiv.Perm.sign σ : ℂ) using 1
      funext s
      simp only [Finset.prod_apply])
  convert h using 1
  funext s
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun σ _ => mul_comm _ _

end Langlands.Global.EisensteinGenericInjectivity
