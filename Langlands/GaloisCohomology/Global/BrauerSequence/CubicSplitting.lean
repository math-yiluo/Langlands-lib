import Langlands.GaloisCohomology.Global.BrauerSequence.QuadraticComplexSplitting
import Langlands.Global.Arithmetic.CyclicCubicPrescribedLocalDegree
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # Cubic splitting of three-torsion Brauer classes over totally complex fields -/

noncomputable section

universe u

open CategoryTheory NumberField IsDedekindDomain
open Langlands.BrauerComparison Langlands.ClassFieldTheory.Local Langlands.ProfiniteCohomology
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.GaloisCohomology

set_option maxHeartbeats 1700000
set_option synthInstance.maxHeartbeats 150000

/-- A relative Brauer class killed by three becomes zero over a cyclic cubic
extension of the totally complex base after finite Galois inflation. -/
def TotallyComplexCubicRelativeBrauerSplittingStatement : Prop :=
  ∀ (F L : Type u) [Field F] [NumberField F] [IsTotallyComplex F] [Field L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (o : relativeCohomology F L 2), 3 • o = 0 →
    ∃ (E : IntermediateField F (SeparableClosure F)) (_ : FiniteDimensional F E),
      IsGalois F E ∧ Module.finrank F E = 3 ∧
      ∃ (M : Type u) (_ : Field M) (_ : Algebra E M) (_ : FiniteDimensional E M)
        (_ : IsGalois E M) (_ : Algebra F M) (_ : IsScalarTower F E M) (_ : Algebra L M)
        (_ : IsScalarTower F L M) (_ : FiniteDimensional F M) (_ : IsGalois F M),
        relativeRestriction F E M 2 (relativeInflation F L M 2 o) = 0

theorem totallyComplexCubicRelativeBrauerSplitting :
    TotallyComplexCubicRelativeBrauerSplittingStatement.{u} := by
  classical
  intro F L _ _ _ _ _ _ _ o ho
  let Ω := SeparableClosure F
  let j : L →ₐ[F] Ω := IsSepClosed.lift
  let : Algebra L Ω := j.toAlgebra
  let : IsScalarTower F L Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let x : cohomology (unitsModule F Ω) 2 :=
    (unitsTowerMap F L Ω 2).hom ((isoGroupCohomology (unitsModule F L) 2).inv.hom o)
  have hx : 3 • x = 0 := by simp only [x, ← map_nsmul, ho, map_zero]
  obtain ⟨ι⟩ := (inferInstance : Nonempty (Langlands.Galois.PlaceEmbeddings F Ω))
  have hfin := (brauerSequenceStatement F Ω ι).finite_support x
  obtain ⟨E, hE, hEg, hdeg, hloc⟩ :=
    Langlands.Global.cyclicCubicPrescribedLocalDegree F hfin.toFinset
  have : IsTotallyComplex E := isTotallyComplex_of_algebra F E
  have hres : brauerRestriction E x = 0 := by
    apply brauerRestriction_eq_zero_of_isComplex ι E IsTotallyComplex.isComplex x 3 hx
    intro v hv w _
    exact dvd_of_eq (hloc v (hfin.mem_toFinset.mpr hv) w).symm
  let L' : IntermediateField F Ω := j.fieldRange
  let eL : L ≃ₐ[F] L' := AlgEquiv.ofInjectiveField j
  let M : IntermediateField F Ω := E ⊔ L'
  let : FiniteDimensional F L' := eL.toLinearEquiv.finiteDimensional
  let : IsGalois F L' := IsGalois.of_algEquiv eL
  let : FiniteDimensional F M := inferInstance
  let : IsGalois F M := IsGalois.mk
  let iE : E →ₐ[F] M := IntermediateField.inclusion le_sup_left
  let iL : L →ₐ[F] M := (IntermediateField.inclusion le_sup_right).comp eL.toAlgHom
  let : Algebra E M := iE.toAlgebra
  let : Algebra L M := iL.toAlgebra
  let : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun a => (iE.commutes a).symm
  let : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq fun a => (iL.commutes a).symm
  let : IsScalarTower E M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower L M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite F E M
  let : IsGalois E M := IsGalois.tower_top_of_isGalois F E M
  let : IsGalois E Ω := IsGalois.tower_top_of_isGalois F E Ω
  refine ⟨E, hE, hEg, hdeg, M, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  have hinflation : x = (unitsTowerMap F M Ω 2).hom
      ((isoGroupCohomology (unitsModule F M) 2).inv.hom (relativeInflation F L M 2 o)) := by
    simp only [x]
    rw [← unitsModuleContinuousEquiv_symm_relativeToContinuous,
      ← unitsModuleContinuousEquiv_symm_relativeToContinuous, relativeToContinuous_tower]
  have hrestriction : brauerRestriction E x = (unitsTowerMap E M Ω 2).hom
      ((isoGroupCohomology (unitsModule E M) 2).inv.hom
        (relativeRestriction F E M 2 (relativeInflation F L M 2 o))) := by
    rw [hinflation]
    have hh := unitsRestriction_unitsTowerMap F E M Ω
      ((isoGroupCohomology (unitsModule F M) 2).inv.hom (relativeInflation F L M 2 o))
    rw [unitsRestriction_isoGroupCohomology_inv F E M] at hh
    exact hh
  rw [hres, ← unitsModuleContinuousEquiv_symm_relativeToContinuous] at hrestriction
  apply relativeToContinuous_two_injective E M Ω
  rw [map_zero]
  apply (unitsModuleContinuousEquiv E Ω 2).symm.injective
  rw [map_zero, ← hrestriction]

end Langlands.GaloisCohomology
