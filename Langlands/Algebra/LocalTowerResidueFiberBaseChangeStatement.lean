import Langlands.Algebra.LocalTowerResidueFiberRings

/-! # Canonical residue-fibre transition localization and module base change

The two actual fibre transitions after base change, `G_i ⊗[F_i] F_j → G_j` and
`G_j ⊗[G_i] N_i → N_j`, with their pure-tensor formulas, and the proposition that they are
respectively a localization at a prime and bijective. This is a statement only.
-/

open scoped TensorProduct
open IsLocalRing

universe uI uA uB uC uN uR uS uT uM

namespace Langlands.Algebra

open scoped ResidueFiberTensor LocalModuleSystem LocalModuleTowerSystem

section Maps

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
  {T : Type uT} [CommRing T] [IsLocalRing T]
  [Algebra S T] [Algebra R T] [IsScalarTower R S T] [IsLocalHom (algebraMap S T)]

namespace LocalAlgebraTowerSystem
variable (D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T)

/-- The actual upper fibre transition after base change, `G_i ⊗[F_i] F_j → G_j`, lifted from
the upper fibre transition and the fibre arrow `F_j → G_j`. The `F_i`-algebra on `F_j` is the
actual lower fibre transition, and `G_j` is an `F_i`-algebra through the common composite. -/
noncomputable def upperFiberBaseChangeMap {i j : ι} (h : i ≤ j) :
    letI := (D.rs.fiberRingMap h).toAlgebra
    D.UpperFiberRing i ⊗[D.rs.FiberRing i] D.rs.FiberRing j →+* D.UpperFiberRing j := by
  letI := (D.rs.fiberRingMap h).toAlgebra
  letI := ((D.fiberHom j).comp (D.rs.fiberRingMap h)).toAlgebra
  let f : D.UpperFiberRing i →ₐ[D.rs.FiberRing i] D.UpperFiberRing j :=
    { D.upperFiberRingMap h with commutes' := fun x ↦ D.fiberHom_map h x }
  let g : D.rs.FiberRing j →ₐ[D.rs.FiberRing i] D.UpperFiberRing j :=
    { D.fiberHom j with commutes' := fun _ ↦ rfl }
  exact (_root_.Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _)).toRingHom

/-- The actual ring transition has the prescribed value on pure tensors. -/
@[simp] theorem upperFiberBaseChangeMap_tmul {i j : ι} (h : i ≤ j)
    (g : D.UpperFiberRing i) (f : D.rs.FiberRing j) :
    letI := (D.rs.fiberRingMap h).toAlgebra
    D.upperFiberBaseChangeMap h (g ⊗ₜ[D.rs.FiberRing i] f) =
      D.upperFiberRingMap h g * D.fiberHom j f := rfl

end LocalAlgebraTowerSystem

namespace LocalModuleTowerSystem
variable {D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T}
  {M : Type uM} [AddCommGroup M] [Module T M]
  [Module S M] [IsScalarTower S T M]
  (E : LocalModuleTowerSystem.{uI, uA, uB, uC, uN} D M)

/-- The actual upper residue-module transition after base change, `G_j ⊗[G_i] N_i → N_j`,
lifted from the published upper-semilinear residue transition. The `G_i`-algebra on `G_j` is
the actual upper fibre transition, and `N_j` keeps its published upper action. -/
noncomputable def upperResidueFiberBaseChangeMap {i j : ι} (h : i ≤ j) :
    letI := (D.upperFiberRingMap h).toAlgebra
    D.UpperFiberRing j ⊗[D.UpperFiberRing i] E.rsModule.ResidueFiber i →ₗ[D.UpperFiberRing j]
      E.rsModule.ResidueFiber j := by
  letI := LocalAlgebraTowerSystem.composite_local R S T
  letI := (D.upperFiberRingMap h).toAlgebra
  letI : Module (D.UpperFiberRing i) (E.rsModule.ResidueFiber j) :=
    Module.compHom (E.rsModule.ResidueFiber j) (D.upperFiberRingMap h)
  letI : IsScalarTower (D.UpperFiberRing i) (D.UpperFiberRing j)
      (E.rsModule.ResidueFiber j) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  exact LinearMap.liftBaseChange (D.UpperFiberRing j)
    { (E.rtModule.residueFiberRingMap h).toAddMonoidHom with
      map_smul' := fun r x ↦ (E.rtModule.residueFiberRingMap h).map_smulₛₗ r x }

/-- The actual module transition has the prescribed value on pure tensors. -/
@[simp] theorem upperResidueFiberBaseChangeMap_tmul {i j : ι} (h : i ≤ j)
    (g : D.UpperFiberRing j) (x : E.rsModule.ResidueFiber i) :
    letI := (D.upperFiberRingMap h).toAlgebra
    E.upperResidueFiberBaseChangeMap h (g ⊗ₜ[D.UpperFiberRing i] x) =
      g • E.rsModule.residueFiberMap h x := by
  let := LocalAlgebraTowerSystem.composite_local R S T
  let := (D.upperFiberRingMap h).toAlgebra
  change g • E.rtModule.residueFiberMap h x = _
  rw [E.rtModule_residueFiberMap h x]

end LocalModuleTowerSystem

end Maps

/-- Canonical residue-fibre transitions of a synchronized local tower (internal support for the
proof of Stacks 00R7). For `F_i = D.rs.FiberRing i`, `G_i = D.UpperFiberRing i` and
`N_i = E.rsModule.ResidueFiber i`: if the upper transition `T_i ⊗[S_i] S_j → T_j` is a
localization at a prime, so is the actual fibre transition `G_i ⊗[F_i] F_j → G_j`; and if the
upper module transition `T_j ⊗[T_i] M_i → M_j` is bijective, so is the actual residue-module
transition `G_j ⊗[G_i] N_i → N_j`. This defines the statement only. -/
def LocalTowerResidueFiberBaseChangeStatement : Prop :=
  ∀ (ι : Type uI) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : Type uR) (S : Type uS) (T : Type uT) [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)]
    (D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T),
    (∀ (i j : ι) (h : i ≤ j), D.st.IsPrimeLocalization h →
      letI := (D.rs.fiberRingMap h).toAlgebra
      letI := (D.upperFiberBaseChangeMap h).toAlgebra
      ∃ (p : Ideal (D.UpperFiberRing i ⊗[D.rs.FiberRing i] D.rs.FiberRing j))
        (hp : p.IsPrime),
        letI := hp
        IsLocalization.AtPrime (D.UpperFiberRing j) p) ∧
    ∀ (M : Type uM) [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower S T M]
      (E : LocalModuleTowerSystem.{uI, uA, uB, uC, uN} D M) (i j : ι) (h : i ≤ j),
      Function.Bijective (E.stModule.moduleBaseChangeMap h) →
      Function.Bijective (E.upperResidueFiberBaseChangeMap h)

end Langlands.Algebra
