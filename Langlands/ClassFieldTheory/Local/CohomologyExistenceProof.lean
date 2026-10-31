import Langlands.ClassFieldTheory.Local.CohomologyExistence
import Langlands.ClassFieldTheory.Local.AbsoluteH1Proof
import Langlands.ClassFieldTheory.Local.AbsoluteInvariantProof
import Langlands.ClassFieldTheory.Local.AbsoluteH2InflationProof
import Langlands.ClassFieldTheory.Local.RelativeInvariantFromAbsolute
import Langlands.ClassFieldTheory.Local.RelativeH2Transport
import Langlands.ClassFieldTheory.Local.ReciprocitySystem

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v

/-- Local absolute and finite relative H1 vanish, and the actual H2 groups
admit invariant maps with the ranges specified by `CohomologyExistence`. -/
theorem cohomologyExistence : CohomologyExistence.{u,v} := by
  intro p hp F
  let : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  obtain ⟨inv, hDegree⟩ := absoluteInvariantExistence.{u} p
  refine ⟨⟨absoluteH1Vanishing F.Carrier, ⟨inv F⟩⟩, ?_⟩
  intro L _ _ _ _
  refine ⟨finiteRelativeH1Vanishing F.Carrier L, ?_⟩
  let f : L →ₐ[F.Carrier] AlgebraicClosure F.Carrier := IsAlgClosed.lift
  let E : IntermediateField F.Carrier (AlgebraicClosure F.Carrier) := f.fieldRange
  let e : L ≃ₐ[F.Carrier] E := f.equivFieldRange
  let : FiniteDimensional F.Carrier E := e.toLinearEquiv.finiteDimensional
  let : IsGalois F.Carrier E := IsGalois.of_algEquiv e
  let T : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier := ⟨E, inferInstance⟩
  let EF : PadicField.{u} p := T.asPadicField (p := p)
  let := EF.algebra
  let : IsScalarTower (Padic p) F.Carrier E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let fClosure : AlgebraicClosure F.Carrier →ₐ[F.Carrier] AlgebraicClosure E :=
    IsAlgClosed.lift
  let : Algebra (AlgebraicClosure F.Carrier) (AlgebraicClosure E) :=
    fClosure.toRingHom.toAlgebra
  let : IsScalarTower F.Carrier (AlgebraicClosure F.Carrier) (AlgebraicClosure E) :=
    IsScalarTower.of_algebraMap_eq fun x => (fClosure.commutes x).symm
  obtain ⟨hInjective, hRange⟩ := absoluteH2InflationExactness F.Carrier E
  let invE := relativeInvariantFromAbsolute F.Carrier E (inv F)
  have hInvE : Function.Injective invE :=
    relativeInvariantFromAbsolute_injective F.Carrier E (inv F) hInjective
  have hImage : invE.range = denominatorSubgroup (Module.finrank F.Carrier E) :=
    relativeInvariantFromAbsolute_range F.Carrier E (inv F) (inv EF) hRange
      (hDegree F EF)
  let c := relativeH2Equiv e
  refine ⟨invE.comp c.toAddMonoidHom, hInvE.comp c.injective, ?_⟩
  have hc : c.toAddMonoidHom.range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr c.surjective
  rw [AddMonoidHom.range_comp, hc, AddSubgroup.map_top, hImage,
    ← e.toLinearEquiv.finrank_eq]

end Langlands.ClassFieldTheory.Local
