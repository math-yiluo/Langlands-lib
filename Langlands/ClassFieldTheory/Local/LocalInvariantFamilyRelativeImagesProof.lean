import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyLawsStatement
import Langlands.ClassFieldTheory.Local.RelativeInvariantFromAbsolute
import Langlands.ClassFieldTheory.Local.UnramifiedBaseChangeProof
import Langlands.ClassFieldTheory.Local.UnramifiedInvariantBaseChangeProof

/-! # Relative images of the local invariant family

The relative invariant of `L` is the descended absolute invariant after
transport to the image field `E` of the chosen embedding and closure
inflation. Closure inflation is injective with image the kernel of absolute
restriction to `E`, and absolute restriction multiplies the descended
invariant by `[E : F]`, so the image is the `[L : F]`-torsion of `ℚ/ℤ`.
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

open AbsoluteInvariantAssembly Langlands.LocalClassField

/-- The relative invariants of the local invariant family are injective, with
image the subgroup of `ℚ/ℤ` killed by the extension degree. -/
theorem localInvariantFamilyRelativeImages :
    LocalInvariantFamilyRelativeImagesStatement.{u} := by
  intro hEx p _ F L _ _ _ _
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let f := closureEmbedding F.Carrier L
  let E := f.fieldRange
  let invF := descendedEquiv F hEx closureInflationTowerCompatibility
    unramifiedInvariantInflationCompatibility
  have hrel : (localInvariantFamily hEx p).relative F L =
      (relativeInvariantFromAbsolute F.Carrier E invF).comp
        (relativeH2Equiv f.equivFieldRange).toAddMonoidHom := rfl
  have hinj : Function.Injective (closureInflation F.Carrier E 2) :=
    (AbsoluteH2Assembly.closureInflationExactness F.Carrier E).1
  refine ⟨?_, ?_⟩
  · rw [hrel]
    exact (relativeInvariantFromAbsolute_injective F.Carrier E invF hinj).comp
      (relativeH2Equiv f.equivFieldRange).injective
  · have htop : (relativeH2Equiv f.equivFieldRange).toAddMonoidHom.range = ⊤ :=
      AddMonoidHom.range_eq_top.mpr (relativeH2Equiv f.equivFieldRange).surjective
    rw [hrel, AddMonoidHom.range_comp, htop, ← AddMonoidHom.range_eq_map]
    let S : FiniteIntermediateExtension F.Carrier := ⟨E, inferInstance⟩
    let E' : PadicField.{u} p := S.asPadicField
    let := E'.algebra
    let : IsScalarTower (Padic p) F.Carrier E'.Carrier := IsScalarTower.of_algebraMap_eq' rfl
    let φ : AlgebraicClosure F.Carrier →ₐ[F.Carrier] AlgebraicClosure E := IsAlgClosed.lift
    let : Algebra (AlgebraicClosure F.Carrier) (AlgebraicClosure E) := φ.toRingHom.toAlgebra
    let : IsScalarTower F.Carrier (AlgebraicClosure F.Carrier) (AlgebraicClosure E) :=
      IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
    let invE := descendedEquiv E' hEx closureInflationTowerCompatibility
      unramifiedInvariantInflationCompatibility
    have hdeg : Module.finrank F.Carrier L = Module.finrank F.Carrier E :=
      f.equivFieldRange.toLinearEquiv.finrank_eq
    rw [hdeg]
    exact relativeInvariantFromAbsolute_range F.Carrier E invF invE
      (absoluteH2InflationExactness F.Carrier E).2
      (fun x => descendedHom_restriction F hEx closureInflationTowerCompatibility
        unramifiedInvariantInflationCompatibility unramifiedBaseChangeStageExistence
        closureInflationBaseChangeCompatibility unramifiedInvariantBaseChangeCompatibility E' x)

end Langlands.ClassFieldTheory.Local
