import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Residue base change for a local unramified algebra -/

universe u v w

open scoped TensorProduct

noncomputable section

namespace Langlands.CommutativeAlgebra.HenselianFiniteEtaleResidueComparison

variable {R : Type u} {L : Type v}
  [CommRing R] [IsLocalRing R] [CommRing L] [IsLocalRing L]
  [Algebra R L] [IsLocalHom (algebraMap R L)]
  [Algebra.EssFiniteType R L] [Algebra.FormallyUnramified R L]

/-- For an essentially finite type formally unramified local map, reduction of
the target modulo the maximal ideal of the base is the target residue field. -/
noncomputable def residueBaseChangeEquiv :
    L ⊗[R] IsLocalRing.ResidueField R ≃ₐ[L] IsLocalRing.ResidueField L :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot L
    (IsLocalRing.maximalIdeal R)).symm.trans
      (Ideal.quotientEquivAlgOfEq L
        (Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := L)))

/-- A surjection from the local target to a field identifies that field with
the target residue field, as an algebra over the target. -/
noncomputable def residueCoverEquiv
    {K : Type w} [Field K] [Algebra L K]
    (hπ : Function.Surjective (algebraMap L K)) :
    IsLocalRing.ResidueField L ≃ₐ[L] K :=
  (Ideal.quotientEquivAlgOfEq L
    (IsLocalRing.ker_eq_maximalIdeal (algebraMap L K) hπ).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId L K) hπ)

/-- Identify the closed-fibre base change of a local unramified algebra with
any field quotient supplied by a surjective algebra map. -/
noncomputable def tensorResidueCoverEquiv
    {K : Type w} [Field K] [Algebra L K]
    (hπ : Function.Surjective (algebraMap L K)) :
    L ⊗[R] IsLocalRing.ResidueField R ≃ₐ[L] K :=
  (residueBaseChangeEquiv (R := R) (L := L)).trans (residueCoverEquiv hπ)

end Langlands.CommutativeAlgebra.HenselianFiniteEtaleResidueComparison
