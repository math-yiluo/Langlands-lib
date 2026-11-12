import Langlands.LocalFactor.Ramification.Galois
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RepresentationTheory.Induced

/-!
# The Artin conductor of an induced finite-Galois representation

These proposition definitions state the induction formula for the published
rational Artin sums of actual finite p-adic Galois extensions. Induction is
Mathlib's `Representation.ind` along the actual restriction-of-scalars map
from the subgroup fixing an intermediate field.
-/

namespace Langlands.Ramification.Padic

open Module

universe uK uK' uL uV

section Components

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
  (K' : Type uK') [Field K'] [Algebra (Padic p) K'] [Algebra K K']
  [Algebra K' F.Carrier] [IsScalarTower (Padic p) K' F.Carrier]
  [IsScalarTower K K' F.Carrier]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The conductor of `Ind_H^G ψ` is `dim ψ` times the conductor of `Ind_H^G 1`
plus the residue degree of `K'/K` times the conductor of `ψ` over `K'`.
The residue degree is the quotient of the two inertia indices. -/
def FiniteGaloisInducedConductorStatement : Prop :=
  haveI : FiniteDimensional K F.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
  ∀ [IsGalois K F.Carrier]
    (ψ : Representation ℂ (F.Carrier ≃ₐ[K'] F.Carrier) V),
    let φ := AlgEquiv.restrictScalarsHom (S := K') (A := F.Carrier) K
    artinConductor T K (Representation.ind φ ψ) =
      (finrank ℂ V : ℚ) * artinConductor T K
          (Representation.ind φ (Representation.trivial ℂ (F.Carrier ≃ₐ[K'] F.Carrier) ℂ)) +
        ((inertia T K).index / (inertia T K').index : ℚ) * artinConductor T K' ψ

end Components

/-- The complete induction family, with arbitrary prime, compatible p-adic field
data, two intermediate fields in a scalar tower, and an independently universed
representation space. -/
def FiniteGaloisConductorInductionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uL} p) (T : F.TopologicalData)
    (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    (K' : Type uK') [Field K'] [Algebra (Padic p) K'] [Algebra K K']
    [Algebra K' F.Carrier] [IsScalarTower (Padic p) K' F.Carrier]
    [IsScalarTower K K' F.Carrier]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    FiniteGaloisInducedConductorStatement T K K' (V := V)

end Langlands.Ramification.Padic
