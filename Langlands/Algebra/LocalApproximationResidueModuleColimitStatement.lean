import Langlands.Algebra.LocalApproximationResidueFiber

/-! # Preservation of the actual residue-module colimit -/

open IsLocalRing
open scoped Langlands.Algebra.LocalModuleSystem

universe uI uA uB uN uR uS uM

namespace Langlands.Algebra

/-- The residue-module conjunct of `LocalApproximationResidueColimitStatement`, over the same
common inputs. If a module system `E` over a directed local algebra system `D` satisfies
`E.IsColimit`, then the canonical lift from the actual direct limit of the residue modules
`κᵢ ⊗[Rᵢ] Mᵢ` to `κ ⊗[R] M` is bijective. The transitions, cocone and lift are the published
actual maps. This defines the statement only. -/
def LocalApproximationResidueModuleColimitStatement : Prop :=
  ∀ (ι : Type uI) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : Type uR) (S : Type uS) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    (D : LocalAlgebraSystem.{uI, uA, uB, uR, uS} ι R S)
    (M : Type uM) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (E : LocalModuleSystem.{uI, uA, uB, uN, uR, uS, uM} D M),
    E.IsColimit →
      letI := Classical.decEq ι
      let residueFiberLift :
          AddCommGroup.DirectLimit E.ResidueFiber
              (fun _ _ h ↦ (E.residueFiberMap h).toAddMonoidHom) →+
            LocalModuleSystem.TargetResidueFiber R M :=
        AddCommGroup.DirectLimit.lift E.ResidueFiber
          (fun _ _ h ↦ (E.residueFiberMap h).toAddMonoidHom)
          (LocalModuleSystem.TargetResidueFiber R M)
          (fun i ↦ (E.residueFiberι i).toAddMonoidHom)
          (fun _ _ h x ↦ E.residueFiberι_compat h x)
      Function.Bijective residueFiberLift

end Langlands.Algebra
