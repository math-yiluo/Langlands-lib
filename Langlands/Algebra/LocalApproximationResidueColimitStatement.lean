import Langlands.Algebra.LocalTowerResidueFiberRings
import Langlands.Algebra.LocalApproximationResidueFiber

/-! # Preservation of the actual residue-fibre colimits -/

open IsLocalRing
open scoped Langlands.Algebra.LocalModuleSystem

universe uI uA uB uN uR uS uM

namespace Langlands.Algebra

/-- Internal colimit-preservation statement behind the quotient-colimit observations in
the proofs of Stacks 00R7 and 046Y. For a directed local algebra system `D` and a module
system `E`, the canonical lifts out of the actual direct limits are bijective:

1. for the residue fields `κᵢ → κ`, if the base cocone is a colimit;
2. for the fibre rings `Sᵢ ⊗[Rᵢ] κᵢ → S ⊗[R] κ`, if both ring cocones are colimits;
3. for the residue modules `κᵢ ⊗[Rᵢ] Mᵢ → κ ⊗[R] M`, if `E.IsColimit`.

All transitions, cocone maps and lifts are the published actual maps. This defines the
statement only. -/
def LocalApproximationResidueColimitStatement : Prop :=
  ∀ (ι : Type uI) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : Type uR) (S : Type uS) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    (D : LocalAlgebraSystem.{uI, uA, uB, uR, uS} ι R S),
    (Function.Bijective D.baseColimitMap →
      let residueLift :
          Ring.DirectLimit (fun i ↦ ResidueField (D.base i)) (fun _ _ h ↦ D.residueMap h) →+*
            ResidueField R :=
        Ring.DirectLimit.lift (fun i ↦ ResidueField (D.base i)) (fun _ _ h ↦ D.residueMap h)
          (ResidueField R) (fun i ↦ D.residueι i) (fun _ _ h a ↦ D.residueι_compat h a)
      Function.Bijective residueLift) ∧
    (D.IsColimit →
      let fiberRingLift :
          Ring.DirectLimit D.FiberRing (fun _ _ h ↦ D.fiberRingMap h) →+*
            LocalAlgebraSystem.TargetFiberRing R S :=
        Ring.DirectLimit.lift D.FiberRing (fun _ _ h ↦ D.fiberRingMap h)
          (LocalAlgebraSystem.TargetFiberRing R S) (fun i ↦ D.fiberRingι i)
          (fun _ _ h x ↦ D.fiberRingι_compat h x)
      Function.Bijective fiberRingLift) ∧
    (∀ (M : Type uM) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
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
        Function.Bijective residueFiberLift)

end Langlands.Algebra
