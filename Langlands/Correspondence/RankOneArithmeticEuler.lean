import Langlands.Correspondence.CharacterSumEuler
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! # Actual arithmetic Euler factors of rank-one characters -/

noncomputable section

universe uK uG

open Polynomial
open scoped TensorProduct

namespace Langlands.FiniteRepresentation

variable {K : Type uK} [Field K] {G : Type uG} [Group G]

/-- Multiplication identifies the tensor of scalar representations with the product character. -/
def scalarCharacterTensorEquiv (χ η : G →* Kˣ) :
    Equiv (tensor (of (Langlands.characterRepresentation χ))
      (of (Langlands.characterRepresentation η)))
      (of (Langlands.characterRepresentation (χ * η))) where
  toLinearEquiv := TensorProduct.lid K K
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    change ((χ g : K) * x) * ((η g : K) * y) =
      ((χ g : K) * (η g : K)) * (x * y)
    ring

end Langlands.FiniteRepresentation

namespace Langlands.WeilDeligneRepresentation

variable {K : Type uK} [Field K] {G : Type uG} [Group G]

/-- The tensor of zero-monodromy scalar pairs is the pair for the product character. -/
def scalarCharacterTensorEquiv (ν χ η : G →* Kˣ) :
    Equiv (tensor (zeroMonodromy ν (FiniteRepresentation.of
      (Langlands.characterRepresentation χ)))
      (zeroMonodromy ν (FiniteRepresentation.of (Langlands.characterRepresentation η))))
      (zeroMonodromy ν (FiniteRepresentation.of (Langlands.characterRepresentation (χ * η)))) where
  representationEquiv := FiniteRepresentation.scalarCharacterTensorEquiv χ η
  comm_monodromy := by
    change (TensorProduct.lid K K).toLinearMap ∘ₗ
      (TensorProduct.map (0 : Module.End K K) (1 : Module.End K K) +
        TensorProduct.map (1 : Module.End K K) (0 : Module.End K K)) =
        (0 : Module.End K K) ∘ₗ (TensorProduct.lid K K).toLinearMap
    simp

end Langlands.WeilDeligneRepresentation

namespace Langlands.LocalFactor.WeilDeligne

variable {K : Type uK} [Field K] {G : Type uG} [Group G]

/-- A nontrivial scalar action of inertia makes the fixed monodromy kernel zero. -/
theorem scalarCharacter_inertiaKernel_eq_zero (ν χ : G →* Kˣ)
    (I : Subgroup G) [I.Normal] (hχ : ∃ w ∈ I, χ w ≠ 1)
    (v : (WeilDeligneRepresentation.zeroMonodromy ν
      (FiniteRepresentation.of (Langlands.characterRepresentation χ))).inertiaKernelRepresentation I) :
    v = 0 := by
  obtain ⟨w, hw, hvalue⟩ := hχ
  have hv := congrArg Subtype.val (v.property ⟨w, hw⟩)
  let x : K := v.val.val
  change (χ w : K) * x = x at hv
  have hzero : ((χ w : K) - 1) * x = 0 := by
    rw [sub_mul, one_mul, hv, sub_self]
  have hne : (χ w : K) - 1 ≠ 0 := sub_ne_zero.mpr fun h => hvalue (Units.ext h)
  apply Subtype.ext
  apply Subtype.ext
  exact (mul_eq_zero.mp hzero).resolve_left hne

/-- A ramified scalar pair has Euler polynomial one. -/
theorem eulerPolynomial_scalarCharacter_of_ramified (ν χ : G →* Kˣ)
    (I : Subgroup G) [I.Normal] (hχ : ∃ w ∈ I, χ w ≠ 1) (g : G) :
    eulerPolynomial (WeilDeligneRepresentation.zeroMonodromy ν
      (FiniteRepresentation.of (Langlands.characterRepresentation χ))) I g = 1 := by
  let A := WeilDeligneRepresentation.zeroMonodromy ν
    (FiniteRepresentation.of (Langlands.characterRepresentation χ))
  let : Subsingleton (A.inertiaKernelRepresentation I) :=
    ⟨fun v w => (scalarCharacter_inertiaKernel_eq_zero ν χ I hχ v).trans
      (scalarCharacter_inertiaKernel_eq_zero ν χ I hχ w).symm⟩
  rw [eulerPolynomial, LocalFactor.eulerPolynomial_eq_det _
    (Module.Basis.empty (A.inertiaKernelRepresentation I) :
      Module.Basis (Fin 0) K (A.inertiaKernelRepresentation I))]
  simp

/-- An inertia-trivial scalar pair has the usual degree-one Euler polynomial. -/
theorem eulerPolynomial_scalarCharacter_of_unramified (ν χ : G →* Kˣ)
    (I : Subgroup G) [I.Normal] (hχ : ∀ w ∈ I, χ w = 1) (g : G) :
    eulerPolynomial (WeilDeligneRepresentation.zeroMonodromy ν
      (FiniteRepresentation.of (Langlands.characterRepresentation χ))) I g =
        1 - C (χ g : K) * X := by
  rw [eulerPolynomial_eq_of_monodromy_eq_zero I _ rfl (by
    intro i
    apply LinearMap.ext
    intro v
    let x : K := v
    change (χ (i : G) : K) * x = x
    rw [hχ i i.property]
    exact one_mul x)]
  have h := LocalFactor.eulerPolynomial_eq_prod_of_repr (Module.Basis.singleton Unit K)
    ((Langlands.characterRepresentation χ) g) (fun _ => (χ g : K)) (by
      intro v i
      simp only [Module.Basis.singleton_repr]
      rfl)
  change LocalFactor.eulerPolynomial ((Langlands.characterRepresentation χ) g) = _
  simpa using h

end Langlands.LocalFactor.WeilDeligne
