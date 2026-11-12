import Langlands.ClassFieldTheory.Local.NYLL.RamifiedResidueStatement
import Langlands.Galois.Local.SeparableUnramifiedGaloisProof
import Mathlib.FieldTheory.Galois.Infinite
import Langlands.ClassFieldTheory.Local.NYLL.SuppliedSpectralComparisonProof

noncomputable section

namespace Langlands.LocalClassField.NYLL

open IsLocalRing

/-- The spectral residue inclusion of the actual inertia fixed field is bijective. -/
theorem spectralInertiaResidueInclusion_bijective
    (K L : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [Finite (ResidueField (LocalGalois.baseIntegers K))]
    [Finite (ResidueField (LocalGalois.extensionIntegers K
      (IntermediateField.fixedField (LocalGalois.inertia K L))))] :
    Function.Bijective (LocalGalois.residueInclusion K L
      (IntermediateField.fixedField (LocalGalois.inertia K L))) := by
  let U := IntermediateField.fixedField (LocalGalois.inertia K L)
  let j := LocalGalois.residueInclusion K L U
  have hfix : U.fixingSubgroup = LocalGalois.inertia K L :=
    IntermediateField.fixingSubgroup_fixedField _
  have hj : j.fieldRange.fixingSubgroup = ⊥ := by
    rw [← LocalGalois.map_residueHom_fixingSubgroup K L U, hfix]
    exact Subgroup.map_ker_self _
  let : IsGalois (ResidueField (LocalGalois.baseIntegers K))
      (ResidueField (LocalGalois.extensionIntegers K L)) :=
    LocalGalois.isGalois_of_finite_base _ _
  have hrange : j.fieldRange = ⊤ := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup j.fieldRange, hj]
    exact IntermediateField.fixedField_bot
  exact ⟨j.injective, AlgHom.fieldRange_eq_top.mp hrange⟩

universe u v

/-- The specific residue inclusion of the inertia fixed field is bijective
for all independent supplied realizations. -/
theorem finiteInertiaResidueMapBijective :
    FiniteInertiaResidueMapBijectiveStatement.{u,v} := by
  intro p hp F E hFE ht hgal TF TU TE
  let : FiniteDimensional F.Carrier E.Carrier :=
    FiniteDimensional.right (Padic p) F.Carrier E.Carrier
  let := TF.topology
  let := TF.valuativeRel
  let := TF.localField
  let := LocalGalois.localNormedField F.Carrier
  let := LocalGalois.localNormedField_ultrametric F.Carrier
  let := LocalGalois.localNormedField_complete F.Carrier
  let := finiteInertiaPadicTower F E TF
  let eU := suppliedSpectralIntegerEquiv F (finiteInertiaPadicField F E TF) TF TU
  let eE := suppliedSpectralIntegerEquiv F E TF TE
  let rU := suppliedSpectralResidueEquiv F (finiteInertiaPadicField F E TF) TF TU
  let rE := suppliedSpectralResidueEquiv F E TF TE
  let : Finite (ResidueField (LocalGalois.baseIntegers F.Carrier)) :=
    LocalGalois.localResidue_finite F.Carrier
  let : Finite TU.ResidueField := TU.finite_residueField
  let : Finite (ResidueField (LocalGalois.extensionIntegers F.Carrier
      (IntermediateField.fixedField (LocalGalois.inertia F.Carrier E.Carrier)))) :=
    Finite.of_injective rU rU.injective
  have hs : Function.Surjective (LocalGalois.residueInclusion F.Carrier E.Carrier
      (finiteInertiaField F E TF)) :=
    (spectralInertiaResidueInclusion_bijective F.Carrier E.Carrier).2
  have hcomm (x : ResidueField (LocalGalois.extensionIntegers F.Carrier
      (finiteInertiaField F E TF))) :
      finiteInertiaResidueMap F E TF TU TE (rU x) =
        rE (LocalGalois.residueInclusion F.Carrier E.Carrier (finiteInertiaField F E TF) x) := by
    obtain ⟨x, rfl⟩ := residue_surjective x
    change TE.residue (finiteInertiaIntegerMap F E TF TU TE (eU x)) =
      TE.residue (eE (LocalGalois.integerInclusion F.Carrier E.Carrier
        (finiteInertiaField F E TF) x))
    congr 1
  refine ⟨(finiteInertiaResidueMap F E TF TU TE).injective, ?_⟩
  intro y
  obtain ⟨z, hz⟩ := hs (rE.symm y)
  refine ⟨rU z, ?_⟩
  exact (hcomm z).trans ((congrArg rE hz).trans (rE.apply_symm_apply y))

end Langlands.LocalClassField.NYLL
