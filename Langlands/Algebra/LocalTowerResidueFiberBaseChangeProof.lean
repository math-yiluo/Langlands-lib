import Langlands.Algebra.LocalTowerResidueFiberRingBaseChange

/-! # Canonical residue-fibre transition localization and module base change

The ring implication is the published `localTowerResidueFiberRingBaseChange`. The module
implication follows from tensor cancellation and base change of the original bijective
module transition, with equality to the actual residue-fibre map checked on pure tensors.
-/

open scoped TensorProduct
open IsLocalRing

universe uI uA uB uC uN uR uS uT uM

namespace Langlands.Algebra

open scoped ResidueFiberTensor LocalModuleSystem LocalModuleTowerSystem

namespace LocalModuleTowerSystem

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} {T : Type uT}
  [CommRing R] [CommRing S] [CommRing T]
  [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)]
  {D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T}
  {M : Type uM} [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower S T M]
  (E : LocalModuleTowerSystem.{uI, uA, uB, uC, uN} D M)

/-- Bijectivity of the original upper module transition survives the actual residue-fibre
base change. This implication does not require a ring localization. -/
theorem upperResidueFiberBaseChangeMap_bijective {i j : ι} (h : i ≤ j)
    (hbij : Function.Bijective (E.stModule.moduleBaseChangeMap h)) :
    Function.Bijective (E.upperResidueFiberBaseChangeMap h) := by
  let := (D.topMap i j h).toAlgebra
  let := (D.upperFiberRingMap h).toAlgebra
  let : Algebra (D.top i) (D.UpperFiberRing j) :=
    ((algebraMap (D.top j) (D.UpperFiberRing j)).comp (D.topMap i j h)).toAlgebra
  let : IsScalarTower (D.top i) (D.top j) (D.UpperFiberRing j) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let : IsScalarTower (D.top i) (D.UpperFiberRing i) (D.UpperFiberRing j) :=
    IsScalarTower.of_algebraMap_smul fun t g ↦ by
      induction g using TensorProduct.inductionOn with
      | tmul u a =>
        change D.upperFiberRingMap h (t ⊗ₜ[D.rs.base i] 1) *
            (u ⊗ₜ[D.rs.base j] a) = (D.topMap i j h t * u) ⊗ₜ[D.rs.base j] a
        simp
      | add x y hx hy => simp_all [smul_add]
  -- The first action is the algebra action, while the last is the tensor action.
  let : @IsScalarTower (D.top i) (D.UpperFiberRing j) (D.UpperFiberRing j)
      (inferInstance : Algebra (D.top i) (D.UpperFiberRing j)).toSMul
      (inferInstance : SMul (D.UpperFiberRing j) (D.UpperFiberRing j))
      (inferInstance : SMul (D.top i) (D.UpperFiberRing j)) :=
    IsScalarTower.of_algebraMap_smul (R := D.top i) (A := D.UpperFiberRing j)
      (M := D.UpperFiberRing j) fun t g ↦ by
      induction g using TensorProduct.inductionOn with
      | tmul u a =>
        change (D.topMap i j h t ⊗ₜ[D.rs.base j] 1) *
            (u ⊗ₜ[D.rs.base j] a) = (D.topMap i j h t * u) ⊗ₜ[D.rs.base j] a
        simp
      | add x y hx hy => simp_all [smul_add, mul_add]
  let e :=
    ((E.upperFiberModuleEquiv i).symm.baseChange
      (D.UpperFiberRing i) (D.UpperFiberRing j) _ _).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange
        (D.top i) (D.UpperFiberRing i) (D.UpperFiberRing j)
        (D.UpperFiberRing j) (E.stModule.obj i)).trans
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange
          (D.top i) (D.top j) (D.UpperFiberRing j)
          (D.UpperFiberRing j) (E.stModule.obj i)).symm.trans
          (((LinearEquiv.ofBijective (E.stModule.moduleBaseChangeMap h) hbij).baseChange
            (D.top j) (D.UpperFiberRing j) _ _).trans (E.upperFiberModuleEquiv j))))
  have he : e.toLinearMap = E.upperResidueFiberBaseChangeMap h := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul g x =>
      induction g using TensorProduct.inductionOn with
      | tmul t b =>
        induction x using TensorProduct.inductionOn with
        | tmul a m =>
          simp only [e, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
            LinearEquiv.baseChange_tmul, upperResidueFiberBaseChangeMap_tmul]
          rw [E.upperFiberModuleEquiv_symm_tmul]
          simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            Algebra.smul_def,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
            LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply]
          change E.upperFiberModuleEquiv j
              (((D.upperFiberRingMap h (1 ⊗ₜ[D.rs.base i] a)) *
                  (t ⊗ₜ[D.rs.base j] b)) ⊗ₜ[D.top j]
                ((1 : D.top j) • E.stModule.map i j h m)) = _
          simp [mul_comm]
          rfl
        | add x y hx hy => simp_all [TensorProduct.tmul_add]
      | add g k hg hk => simp_all [TensorProduct.add_tmul]
    | add x y hx hy => simp_all
  rw [← he]
  exact e.bijective

end LocalModuleTowerSystem

/-- The actual upper residue-fibre ring and module transitions preserve the respective
prime-localization and bijectivity properties of the original upper transitions. -/
theorem localTowerResidueFiberBaseChange :
    LocalTowerResidueFiberBaseChangeStatement.{uI, uA, uB, uC, uN, uR, uS, uT, uM} := by
  intro ι _ _ _ R S T _ _ _ _ _ _ _ _ _ _ _ _ D
  refine ⟨localTowerResidueFiberRingBaseChange ι R S T D, ?_⟩
  intro M _ _ _ _ E i j h hbij
  exact E.upperResidueFiberBaseChangeMap_bijective h hbij

end Langlands.Algebra
