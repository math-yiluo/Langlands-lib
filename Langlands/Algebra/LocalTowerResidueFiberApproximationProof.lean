import Langlands.Algebra.LocalTowerResidueFiberApproximationStatement
import Langlands.Algebra.LocalApproximationResidueColimitProof
import Langlands.Algebra.LocalTowerResidueFiberBaseChangeProof
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Approximation of the actual synchronized residue-fibre system: proof

The six approximation clauses for `E.fiberModuleSystem` are assembled from the colimit
statement `LocalApproximationResidueColimitStatement` (clause 1), the transition statement
`LocalTowerResidueFiberBaseChangeStatement` (clauses 5 and 6) and elementary component
finiteness arguments (clauses 2–4). The final theorem instantiates both statements with their
published proofs `localApproximationResidueColimit` and `localTowerResidueFiberBaseChange`.
-/

open scoped TensorProduct
open IsLocalRing

universe uI uA uB uC uN uR uS uT uM

namespace Langlands.Algebra

open scoped ResidueFiberTensor LocalModuleSystem LocalModuleTowerSystem

namespace LocalTowerResidueFiberApproximationProof

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} {T : Type uT} [CommRing R] [CommRing S] [CommRing T]
  [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)]
  {D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T}

section Colimit

/-- The package's lower fibre colimit map is the actual lift out of the lower fibre rings. -/
theorem fiberSystem_baseColimitMap_eq :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    D.fiberSystem.baseColimitMap =
      Ring.DirectLimit.lift D.rs.FiberRing (fun _ _ h ↦ D.rs.fiberRingMap h)
        (LocalAlgebraSystem.TargetFiberRing R S) (fun i ↦ D.rs.fiberRingι i)
        (fun _ _ h x ↦ D.rs.fiberRingι_compat h x) := rfl

/-- The package's upper fibre colimit map is the actual lift for the composite arrow. -/
theorem fiberSystem_algebraColimitMap_eq :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    D.fiberSystem.algebraColimitMap =
      Ring.DirectLimit.lift D.rt.FiberRing (fun _ _ h ↦ D.rt.fiberRingMap h)
        (LocalAlgebraSystem.TargetFiberRing R T) (fun i ↦ D.rt.fiberRingι i)
        (fun _ _ h x ↦ D.rt.fiberRingι_compat h x) := rfl

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module S M] [Module T M]
  [IsScalarTower R S M] [IsScalarTower S T M] [IsScalarTower R T M]
  (E : LocalModuleTowerSystem.{uI, uA, uB, uC, uN} D M)

/-- The package's residue-module colimit map is the actual lift for the middle projection. -/
theorem fiberModuleSystem_moduleColimitMap_eq :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    letI := Classical.decEq ι
    E.fiberModuleSystem.moduleColimitMap =
      AddCommGroup.DirectLimit.lift E.rsModule.ResidueFiber
        (fun _ _ h ↦ (E.rsModule.residueFiberMap h).toAddMonoidHom)
        (LocalModuleSystem.TargetResidueFiber R M)
        (fun i ↦ (E.rsModule.residueFiberι i).toAddMonoidHom)
        (fun _ _ h x ↦ E.rsModule.residueFiberι_compat h x) := rfl

end Colimit

section Components

/-- The lower fibre `S_i ⊗[R_i] κ_i` is a quotient of `S_i`, hence essentially of finite type
over `ℤ`. -/
theorem fiberRing_essFiniteType_int (hD : D.IsApproximation) (i : ι) :
    _root_.Algebra.EssFiniteType ℤ (D.rs.FiberRing i) := by
  let := hD.1.2.1 i
  let := hD.1.2.2.1 i
  let := _root_.Algebra.EssFiniteType.comp ℤ (D.rs.base i) (D.rs.alg i)
  apply _root_.Algebra.EssFiniteType.of_surjective
    (_root_.Algebra.TensorProduct.includeLeft : D.rs.alg i →ₐ[ℤ] D.rs.FiberRing i)
  exact _root_.Algebra.TensorProduct.includeLeft_surjective ℤ (D.rs.alg i)
    IsLocalRing.residue_surjective

/-- The actual upper fibre algebra `F_i → G_i` is essentially of finite type. -/
theorem upperFiberRing_essFiniteType (hD : D.IsApproximation) (i : ι) :
    _root_.Algebra.EssFiniteType (D.rs.FiberRing i) (D.UpperFiberRing i) := by
  let := hD.1.2.2.1 i
  let := hD.2.2.1 i
  let := _root_.Algebra.EssFiniteType.comp (D.rs.base i) (D.rs.alg i) (D.top i)
  let : _root_.Algebra.EssFiniteType (D.rs.base i) (D.UpperFiberRing i) := by
    apply _root_.Algebra.EssFiniteType.of_surjective
      (_root_.Algebra.TensorProduct.includeLeft :
        D.top i →ₐ[D.rs.base i] D.UpperFiberRing i)
    exact _root_.Algebra.TensorProduct.includeLeft_surjective (D.rs.base i) (D.top i)
      IsLocalRing.residue_surjective
  exact _root_.Algebra.EssFiniteType.of_comp
    (D.rs.base i) (D.rs.FiberRing i) (D.UpperFiberRing i)

variable {M : Type uM} [AddCommGroup M] [Module S M] [Module T M] [IsScalarTower S T M]
  (E : LocalModuleTowerSystem.{uI, uA, uB, uC, uN} D M)

/-- Finite generation of `M_i` over `T_i` passes to `κ_i ⊗[R_i] M_i ≃ G_i ⊗[T_i] M_i`
over `G_i`. -/
theorem residueFiber_finite (hE : E.IsApproximation) (i : ι) :
    Module.Finite (D.UpperFiberRing i) (E.rsModule.ResidueFiber i) := by
  let := hE.2.2.1 i
  exact Module.Finite.equiv (E.upperFiberModuleEquiv i)

end Components

section Assembly

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module S M] [Module T M]
  [IsScalarTower R S M] [IsScalarTower S T M] [IsScalarTower R T M]
  (E : LocalModuleTowerSystem.{uI, uA, uB, uC, uN} D M)

/-- The six approximation clauses of the residue-fibre package, from the two supporting
statements. -/
theorem fiberModuleSystem_isApproximation_of
    (hCrs : LocalApproximationResidueColimitStatement.{uI, uA, uB, uN, uR, uS, uM})
    (hCrt : LocalApproximationResidueColimitStatement.{uI, uA, uC, uN, uR, uT, uM})
    (hB : LocalTowerResidueFiberBaseChangeStatement.{uI, uA, uB, uC, uN, uR, uS, uT, uM})
    (hE : E.IsApproximation) :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    E.fiberModuleSystem.IsApproximation := by
  let := LocalAlgebraTowerSystem.composite_local R S T
  obtain ⟨hD, hM, hfinite, hbc⟩ := hE
  obtain ⟨hrs, hst, hupper, hlocST, hlocRT⟩ := hD
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, fun i ↦ fiberRing_essFiniteType_int ⟨hrs, hst, hupper, hlocST, hlocRT⟩ i,
    fun i ↦ upperFiberRing_essFiniteType ⟨hrs, hst, hupper, hlocST, hlocRT⟩ i,
    fun i ↦ residueFiber_finite E ⟨⟨hrs, hst, hupper, hlocST, hlocRT⟩, hM, hfinite, hbc⟩ i,
    fun i j h ↦ (hB ι R S T D).1 i j h (hlocST i j h),
    fun i j h ↦ (hB ι R S T D).2 M E i j h (hbc i j h)⟩
  · rw [fiberSystem_baseColimitMap_eq]
    exact (hCrs ι R S D.rs).2.1 hrs.1
  · rw [fiberSystem_algebraColimitMap_eq]
    exact (hCrt ι R T D.rt).2.1 ⟨hrs.1.1, hst.2⟩
  · rw [fiberModuleSystem_moduleColimitMap_eq]
    exact (hCrs ι R S D.rs).2.2 M E.rsModule ⟨hrs.1, hM⟩

/-- The target statement follows from the colimit statement (for `R → S` and `R → T`) and the
transition statement. -/
theorem of_supporting
    (hCrs : LocalApproximationResidueColimitStatement.{uI, uA, uB, uN, uR, uS, uM})
    (hCrt : LocalApproximationResidueColimitStatement.{uI, uA, uC, uN, uR, uT, uM})
    (hB : LocalTowerResidueFiberBaseChangeStatement.{uI, uA, uB, uC, uN, uR, uS, uT, uM}) :
    LocalTowerResidueFiberApproximationStatement.{uI, uA, uB, uC, uN, uR, uS, uT, uM} := by
  intro ι _ _ _ R S T _ _ _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ _ D E hE
  exact fiberModuleSystem_isApproximation_of E hCrs hCrt hB hE

end Assembly

end LocalTowerResidueFiberApproximationProof

/-- The actual synchronized residue-fibre system of an approximating module tower is again an
approximation. -/
theorem localTowerResidueFiberApproximation :
    LocalTowerResidueFiberApproximationStatement.{uI, uA, uB, uC, uN, uR, uS, uT, uM} :=
  LocalTowerResidueFiberApproximationProof.of_supporting
    localApproximationResidueColimit.{uI, uA, uB, uN, uR, uS, uM}
    localApproximationResidueColimit.{uI, uA, uC, uN, uR, uT, uM}
    localTowerResidueFiberBaseChange.{uI, uA, uB, uC, uN, uR, uS, uT, uM}

end Langlands.Algebra
