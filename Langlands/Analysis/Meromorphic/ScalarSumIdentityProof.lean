import Langlands.Analysis.Meromorphic.ScalarSumIdentityStatement
import Langlands.Analysis.Meromorphic.ScalarIdentity

/-! # Scalar meromorphic identity with a finite sum in changed coordinates -/

universe u v

set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open Set

/-- The identity principle for a finite sum of scalar meromorphic products,
including the sum with no summands. -/
theorem scalarMeromorphicSumIdentity : ScalarMeromorphicSumIdentityStatement.{u, v} := by
  intro X _ _ Y _ _ e f U V W k coeff g hf hcoeff hg n c O hO hne hseed
  let : FiniteDimensional ℂ X := hf.1
  cases k with
  | zero =>
    have hz := isMeromorphicInCoordinatesOn_const (X := X) 0
    have heq := hf.eqOn_of_eqOn_open hz c hO hne (fun x hx => by
      simpa using hseed x hx.1)
    intro x hx _
    simpa using heq (mem_inter hx.1 (mem_univ x))
  | succ k =>
    let D := V ∩ e ⁻¹' W
    let b (i : Fin (k + 1)) : X → ℂ := coeff i * (g i ∘ e)
    have hb (i : Fin (k + 1)) : IsMeromorphicInCoordinatesOn (b i) D :=
      (hcoeff i).mul ((hg i).comp_linearEquiv e)
    have hD (m : ℕ) (d : (Fin m → ℂ) ≃ₗ[ℂ] X) :
        IsOpen (d ⁻¹' D) ∧ Dense (d ⁻¹' D) :=
      ⟨((hb 0).2 m d).1, ((hb 0).2 m d).2.1⟩
    have hs := IsMeromorphicInCoordinatesOn.sum Finset.univ hD (fun i _ => hb i)
    have heq := hf.eqOn_of_eqOn_open hs c hO hne (fun x hx => by
      simpa only [Function.comp_apply, Finset.sum_apply, b, Pi.mul_apply] using hseed x hx.1)
    intro x hx hxW
    simpa only [Finset.sum_apply, b, Pi.mul_apply, Function.comp_apply] using
      heq (mem_inter hx.1 (mem_inter hx.2 hxW))

end Langlands.Analysis.Meromorphic
