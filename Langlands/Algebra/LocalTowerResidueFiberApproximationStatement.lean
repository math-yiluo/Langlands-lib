import Langlands.Algebra.LocalTowerResidueFiberSystem

/-! # Approximation of the actual synchronized residue-fibre system

The proposition that the published residue-fibre package `E.fiberModuleSystem`, over the
packaged fibre-ring diagram `D.fiberSystem`, is an approximation system whenever the synchronized
local tower `E` is one. This is a statement only.
-/

universe uI uA uB uC uN uR uS uT uM

namespace Langlands.Algebra

open scoped ResidueFiberTensor LocalModuleSystem LocalModuleTowerSystem

/-- Approximation preservation for the actual residue-fibre system of a synchronized local tower
(internal support for the proof of Stacks 00R7). Let `D : LocalAlgebraTowerSystem ι R S T` and
`E : LocalModuleTowerSystem D M`, where `M` carries compatible `R`-, `S`- and `T`-actions. If
`E.IsApproximation`, then, after installing the proved locality
`LocalAlgebraTowerSystem.composite_local R S T` of `R → T`, the published package
`E.fiberModuleSystem` of residue modules `κ_i ⊗[R_i] M_i` over the fibre-ring arrows
`S_i ⊗[R_i] κ_i → T_i ⊗[R_i] κ_i`, with targets `κ ⊗[R] M` over `S ⊗[R] κ → T ⊗[R] κ`,
satisfies the six clauses of `LocalModuleSystem.IsApproximation`. This defines the statement
only. -/
def LocalTowerResidueFiberApproximationStatement : Prop :=
  ∀ (ι : Type uI) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : Type uR) (S : Type uS) (T : Type uT) [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)]
    (M : Type uM) [AddCommGroup M] [Module R M] [Module S M] [Module T M]
    [IsScalarTower R S M] [IsScalarTower S T M] [IsScalarTower R T M]
    (D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T)
    (E : LocalModuleTowerSystem.{uI, uA, uB, uC, uN} D M),
    E.IsApproximation →
      letI := LocalAlgebraTowerSystem.composite_local R S T
      E.fiberModuleSystem.IsApproximation

end Langlands.Algebra
