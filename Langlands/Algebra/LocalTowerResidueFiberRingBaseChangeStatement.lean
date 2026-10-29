import Langlands.Algebra.LocalTowerResidueFiberBaseChangeStatement

/-! # Prime-localization preservation for the actual upper residue-fibre transition

The ring implication of `LocalTowerResidueFiberBaseChangeStatement`, isolated: if the upper
transition `T_i ⊗[S_i] S_j → T_j` is a localization at a prime, so is the actual fibre
transition `G_i ⊗[F_i] F_j → G_j`. This is a statement only.
-/

open scoped TensorProduct

universe uI uA uB uC uR uS uT

namespace Langlands.Algebra

open scoped ResidueFiberTensor

/-- Prime-localization preservation for the actual upper residue-fibre transition of a
synchronized local tower (internal support for the proof of Stacks 00R7). For
`F_i = D.rs.FiberRing i` and `G_i = D.UpperFiberRing i`: if the upper transition
`T_i ⊗[S_i] S_j → T_j` is a localization at a prime, so is the actual fibre transition
`D.upperFiberBaseChangeMap h : G_i ⊗[F_i] F_j → G_j`. This is exactly the ring conjunct of
`LocalTowerResidueFiberBaseChangeStatement` and defines the statement only. -/
def LocalTowerResidueFiberRingBaseChangeStatement : Prop :=
  ∀ (ι : Type uI) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : Type uR) (S : Type uS) (T : Type uT)
    [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)]
    (D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T)
    (i j : ι) (h : i ≤ j), D.st.IsPrimeLocalization h →
      letI := (D.rs.fiberRingMap h).toAlgebra
      letI := (D.upperFiberBaseChangeMap h).toAlgebra
      ∃ (p : Ideal (D.UpperFiberRing i ⊗[D.rs.FiberRing i] D.rs.FiberRing j))
        (hp : p.IsPrime),
        letI := hp
        IsLocalization.AtPrime (D.UpperFiberRing j) p

end Langlands.Algebra
