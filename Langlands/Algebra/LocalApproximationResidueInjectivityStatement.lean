import Langlands.Algebra.LocalApproximationResidueFiber

/-! # Eventual residue-fibre injectivity for local approximation systems -/

open scoped Langlands.Algebra.LocalModuleSystem

universe uI uA uB uN uR uS uM

namespace Langlands.Algebra

/-- The eventual injectivity assertion inside the proof of Stacks 046Y, together
with its raw-residue-fibre corollary, for every system satisfying the six 00QX
approximation properties. Both maps use the same eventual bound. -/
def LocalApproximationResidueInjectivityStatement : Prop :=
  ∀ (ι : Type uI) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : Type uR) (S : Type uS) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    (D : LocalAlgebraSystem.{uI, uA, uB, uR, uS} ι R S)
    (M : Type uM) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M]
    (E : LocalModuleSystem.{uI, uA, uB, uN, uR, uS, uM} D M),
    E.IsApproximation →
      ∃ i : ι, ∀ j : ι, i ≤ j →
        Function.Injective (E.residueFiberΨ j) ∧
        Function.Injective (E.residueFiberι j)

end Langlands.Algebra
