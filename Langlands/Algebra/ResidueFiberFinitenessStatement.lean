import Langlands.Algebra.EssFinitePresentation
import Langlands.Algebra.LocalTowerResidueFiberRings
import Mathlib.Algebra.Module.FinitePresentation

/-! # Finiteness of the actual residue-fibre arrow and module -/

universe u v w z

open scoped TensorProduct
open IsLocalRing

namespace Langlands.Algebra

/-- Derived finiteness transport to the residue fibres of a local tower `R → S → T` with a
compatible module `M` (internal support for the second use of Stacks 00R6 in the proof of
00R7). Put `κ = ResidueField R`, `F = S ⊗[R] κ`, `G = T ⊗[R] κ` and `N = κ ⊗[R] M`. If
`T` is essentially of finite presentation over `S` and `M` is finitely presented over `T`,
then `G` is essentially of finite presentation over `F` through the actual arrow
`ResidueFiberTensor.upperMap R S κ T`, and `N` is finitely presented over `G` for the
transported action `(t ⊗ a) • (b ⊗ m) = (a * b) ⊗ (t • m)` of
`ResidueFiberTensor.rawModule R T κ M`. This defines the statement only. -/
def ResidueFiberFinitenessStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (T : Type w) (M : Type z)
    [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)]
    [AddCommGroup M] [Module R M] [Module S M] [Module T M]
    [IsScalarTower R S M] [IsScalarTower S T M] [IsScalarTower R T M],
    EssFinitePresentation S T → Module.FinitePresentation T M →
      letI := ResidueFiberTensor.upperAlgebra R S (ResidueField R) T
      letI := ResidueFiberTensor.rawModule R T (ResidueField R) M
      EssFinitePresentation (LocalAlgebraSystem.TargetFiberRing R S)
          (LocalAlgebraSystem.TargetFiberRing R T) ∧
        Module.FinitePresentation (LocalAlgebraSystem.TargetFiberRing R T)
          (LocalModuleSystem.TargetResidueFiber R M)

end Langlands.Algebra
