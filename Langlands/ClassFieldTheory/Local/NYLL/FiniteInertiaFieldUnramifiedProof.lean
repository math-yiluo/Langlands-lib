import Langlands.ClassFieldTheory.Local.NYLL.RamifiedResidueStatement
import Langlands.ClassFieldTheory.Local.NYLL.SuppliedSpectralComparisonProof
import Langlands.Galois.Local.SeparableUnramifiedGaloisProof
import Langlands.Galois.Local.SeparableUnramifiedFiniteArithmetic
import Mathlib.RingTheory.Unramified.LocalRing

/-! # Relative unramifiedness of the actual finite inertia fixed field -/

noncomputable section

namespace Langlands.LocalClassField.NYLL

open IsLocalRing

universe u v

/-- The actual finite inertia fixed field has relative ramification index one
for every supplied realization of its integer ring. -/
theorem finiteInertiaFieldUnramified : FiniteInertiaFieldUnramifiedStatement.{u, v} := by
  intro p hp F E hFE htower hab TF TU
  let := TF.topology
  let := TF.valuativeRel
  let := TF.localField
  let := LocalGalois.localNormedField F.Carrier
  let := LocalGalois.localNormedField_ultrametric F.Carrier
  let := LocalGalois.localNormedField_complete F.Carrier
  let := TU.topology
  let := TU.valuativeRel
  let := TU.localField
  let U := finiteInertiaPadicField F E TF
  let : FiniteDimensional F.Carrier E.Carrier :=
    FiniteDimensional.right (Padic p) F.Carrier E.Carrier
  let : Finite (ResidueField (LocalGalois.baseIntegers F.Carrier)) :=
    LocalGalois.localResidue_finite F.Carrier
  let : Finite (ResidueField (LocalGalois.extensionIntegers F.Carrier U.Carrier)) :=
    Finite.of_equiv TU.ResidueField (suppliedSpectralResidueEquiv F U TF TU).symm.toEquiv
  have hresSpectral :
      Module.finrank (ResidueField (LocalGalois.baseIntegers F.Carrier))
          (ResidueField (LocalGalois.extensionIntegers F.Carrier U.Carrier)) =
        Module.finrank F.Carrier U.Carrier := by
    apply (LocalGalois.inertia_le_fixingSubgroup_iff_residue_finrank
      F.Carrier E.Carrier (finiteInertiaField F E TF)).mp
    change LocalGalois.inertia F.Carrier E.Carrier ≤
      (IntermediateField.fixedField (LocalGalois.inertia F.Carrier E.Carrier)).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_fixedField]
  let := PadicField.TopologicalData.relativeIntegerAlgebra TF TU
  let := PadicField.TopologicalData.relativeIntegerFieldAlgebra (E := U) TF
  let := PadicField.TopologicalData.relativeIntegerFieldTower (E := U) TF
  let := PadicField.TopologicalData.relativeIntegerTower TF TU
  let := (relativeIntegerStructure p F U TF TU).1
  let := (relativeIntegerStructure p F U TF TU).2
  let : Module TF.Integers U.Carrier := Algebra.toModule
  let : Module.IsTorsionFree TF.Integers U.Carrier :=
    Module.IsTorsionFree.trans_faithfulSMul TF.Integers F.Carrier U.Carrier
  let : Module.Free TF.Integers TU.Integers :=
    IsIntegralClosure.module_free TF.Integers F.Carrier U.Carrier TU.Integers
  have hrank : Module.finrank TF.Integers TU.Integers = Module.finrank F.Carrier U.Carrier :=
    IsIntegralClosure.rank TF.Integers F.Carrier U.Carrier TU.Integers
  have hres : Module.finrank TF.ResidueField TU.ResidueField =
      Module.finrank F.Carrier U.Carrier := by
    have h := (suppliedSpectralResidue_finrank F U TF TU).symm.trans hresSpectral
    convert h using 1
    congr 1
    ext a b
    obtain ⟨a, rfl⟩ := residue_surjective a
    obtain ⟨b, rfl⟩ := residue_surjective b
    rfl
  have hmap : (maximalIdeal TF.Integers).map (algebraMap TF.Integers TU.Integers) =
      maximalIdeal TU.Integers := by
    apply (LocalGalois.map_maximalIdeal_eq_iff_residue_finrank TF.Integers TU.Integers).mpr
    exact hres.trans hrank.symm
  let : Algebra.FormallyUnramified TF.Integers TU.Integers :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hmap
  exact Ideal.ramificationIdx_eq_one (maximalIdeal TU.Integers) TF.Integers

end Langlands.LocalClassField.NYLL
