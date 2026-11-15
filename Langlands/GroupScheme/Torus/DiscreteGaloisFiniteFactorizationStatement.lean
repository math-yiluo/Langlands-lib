import Langlands.Representation.Smooth.Definitions
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Finiteness.Defs

/-! # Finite Galois factorization of finitely generated discrete modules -/

universe u v

namespace Langlands.GroupScheme

/-- A smooth integral absolute-Galois representation on a finitely generated
module is the inflation of an actual finite-Galois representation on the same
module through the canonical restriction homomorphism. -/
def DiscreteGaloisFiniteFactorizationStatement : Prop :=
  ∀ (k : Type u) [Field k] (M : Type v) [AddCommGroup M] [Module ℤ M]
    [Module.Finite ℤ M]
    (ρ : Representation ℤ (SeparableClosure k ≃ₐ[k] SeparableClosure k) M),
    IsSmooth ρ →
      ∃ (L : IntermediateField k (SeparableClosure k))
        (_hfin : FiniteDimensional k L) (hgal : IsGalois k L),
        letI := hgal
        ∃ ρL : Representation ℤ (L ≃ₐ[k] L) M,
          ρL.comp (AlgEquiv.restrictNormalHom L) = ρ

end Langlands.GroupScheme
