import Langlands.LocalFactor.Euler.Definitions
import Langlands.WeilDeligne.Kernels
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The inertia-fixed kernel inclusion and maximal Euler degree

The inclusion retains both actual subtype conditions. Its dimension properties
give an algebraic criterion for zero monodromy and trivial inertia.
-/

noncomputable section

universe uK uG uV

namespace Langlands.LocalFactor

variable {K : Type uK} [Field K]
variable {V : Type uV} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- An invertible operator has an Euler polynomial of full degree. -/
theorem eulerPolynomial_natDegree_of_isUnit (f : Module.End K V) (hf : IsUnit f) :
    (eulerPolynomial f).natDegree = Module.finrank K V := by
  have hc : f.charpoly.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, LinearMap.eval_charpoly]
    simpa only [map_zero, zero_sub] using (LinearMap.isUnit_det (-f) hf.neg).ne_zero
  rw [eulerPolynomial, Polynomial.reverse_natDegree,
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hc), Nat.sub_zero,
    LinearMap.charpoly_natDegree]

variable {G : Type uG} [Group G]

/-- In particular every group element acts with a full-degree Euler polynomial. -/
theorem eulerPolynomial_natDegree_representation
    (A : FiniteRepresentation.{uK, uG, uV} K G) (g : G) :
    (eulerPolynomial (A.representation g)).natDegree = A.rank :=
  eulerPolynomial_natDegree_of_isUnit _ ((Group.isUnit g).map A.representation)

end Langlands.LocalFactor

namespace Langlands.WeilDeligneRepresentation

variable {K : Type uK} [Field K] {G : Type uG} [Group G] {ν : G →* Kˣ}
variable (I : Subgroup G) [I.Normal]
variable (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)

/-- The actual inclusion of the inertia-fixed monodromy kernel into the carrier. -/
def inertiaKernelInclusion : inertiaKernelRepresentation I A →ₗ[K] A :=
  A.monodromy.ker.subtype.comp
    (FiniteRepresentation.invariantSubspace A.kernelRepresentation I).subtype

theorem inertiaKernelInclusion_injective :
    Function.Injective (inertiaKernelInclusion I A) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem inertiaKernel_rank_le : (inertiaKernelRepresentation I A).rank ≤ A.rank :=
  LinearMap.finrank_le_finrank_of_injective (inertiaKernelInclusion_injective I A)

/-- Full dimension forces both defining constraints to vanish. -/
theorem inertiaKernel_rank_eq_iff :
    (inertiaKernelRepresentation I A).rank = A.rank ↔
      A.monodromy = 0 ∧ ∀ i : I, A.representation i = 1 := by
  constructor
  · intro hdim
    have hs : Function.Surjective (inertiaKernelInclusion I A) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
        (inertiaKernelInclusion_injective I A)
    constructor
    · ext v
      obtain ⟨x, hx⟩ := hs v
      change A.monodromy v = 0
      rw [← hx]
      exact x.val.property
    · intro i
      ext v
      obtain ⟨x, hx⟩ := hs v
      change A.representation i v = v
      rw [← hx]
      exact congrArg Subtype.val (x.property i)
  · rintro ⟨hN, hI⟩
    have hs : Function.Surjective (inertiaKernelInclusion I A) := by
      intro v
      let w : A.monodromy.ker := ⟨v, by simp [hN]⟩
      have hw : w ∈ FiniteRepresentation.invariantSubspace A.kernelRepresentation I := by
        intro i
        apply Subtype.ext
        change A.representation i v = v
        rw [hI i]
        rfl
      exact ⟨⟨w, hw⟩, rfl⟩
    exact le_antisymm (inertiaKernel_rank_le I A)
      (LinearMap.finrank_le_finrank_of_surjective hs)

end Langlands.WeilDeligneRepresentation

namespace Langlands.LocalFactor

open WeilDeligneRepresentation

variable {K : Type uK} [Field K] {G : Type uG} [Group G] {ν : G →* Kˣ}
variable (I : Subgroup G) [I.Normal]
variable (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) (Φ : G)

/-- The WD Euler polynomial has degree equal to the invariant-kernel dimension. -/
theorem wdEulerPolynomial_natDegree :
    (eulerPolynomial ((inertiaKernelRepresentation I A).representation Φ)).natDegree =
      (inertiaKernelRepresentation I A).rank :=
  eulerPolynomial_natDegree_representation _ _

/-- Maximal Euler degree characterizes trivial inertia and zero monodromy. -/
theorem wdEulerPolynomial_natDegree_eq_rank_iff :
    (eulerPolynomial ((inertiaKernelRepresentation I A).representation Φ)).natDegree =
        A.rank ↔
      A.monodromy = 0 ∧ ∀ i : I, A.representation i = 1 := by
  rw [wdEulerPolynomial_natDegree, inertiaKernel_rank_eq_iff]

end Langlands.LocalFactor
