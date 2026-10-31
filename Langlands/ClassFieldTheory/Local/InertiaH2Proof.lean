import Langlands.ClassFieldTheory.Local.InertiaH2Statement
import Langlands.ClassFieldTheory.Local.ClosureUnitTransport
import Langlands.Cohomology.Continuous.EquivalenceTransport
import Langlands.Galois.Local.AbsoluteProof
import Mathlib.FieldTheory.Galois.Infinite
import Langlands.ClassFieldTheory.Local.FixedFieldUnits
import Langlands.Cohomology.Continuous.FiniteQuotientComparisonProof
import Langlands.ClassFieldTheory.Local.FiniteNormH2Proof
import Langlands.ClassFieldTheory.Local.InertiaFixedFieldNormProof

/-! # Vanishing of actual continuous local inertia H2 -/

noncomputable section

open CategoryTheory Langlands.Continuous

namespace Langlands.ClassFieldTheory.Local

universe u

-- The finite-stage helper below is reused from Worker 10's private draft.
private theorem absoluteH2_of_finiteRelativeH2 (K : Type u) [Field K] [CharZero K]
    (hfinite : ∀ (E : IntermediateField K (AlgebraicClosure K))
      [FiniteDimensional K E] [IsGalois K E],
      Subsingleton (relativeCohomology K E 2)) :
    Subsingleton (absoluteCohomology K 2) := by
  let : CompactSpace (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure K/K))
  let A : DiscreteModule IntegerScalars.{u} (Field.absoluteGaloisGroup K) :=
    { toTopRep := absoluteUnits K
      isDiscrete := inferInstance
      continuous_action := continuous_unitAction K (AlgebraicClosure K) }
  have hstage (N : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
      Subsingleton (groupCohomology (finiteQuotientRep A.toRep N) 2) := by
    let H : ClosedSubgroup Gal(AlgebraicClosure K/K) :=
      ⟨N.toSubgroup, N.toOpenSubgroup.isClosed⟩
    let : H.Normal := N.isNormal'
    let E := IntermediateField.fixedField H.toSubgroup
    have hopen : IsOpen E.fixingSubgroup.carrier := by
      rw [InfiniteGalois.fixingSubgroup_fixedField H]
      exact N.toOpenSubgroup.isOpen
    let : FiniteDimensional K E := (InfiniteGalois.isOpen_iff_finite E).mp hopen
    let : Subsingleton (relativeCohomology K E 2) := hfinite E
    exact (fixedFieldCohomologyIso K (AlgebraicClosure K) H 2).toLinearEquiv.injective.subsingleton
  have hz : Limits.IsZero (finiteQuotientCohomology A.toRep 2) := by
    rw [Limits.IsZero.iff_id_eq_zero]
    apply Limits.colimit.hom_ext
    intro N
    let := hstage (OrderDual.ofDual N)
    exact (ModuleCat.isZero_of_subsingleton
      (groupCohomology (finiteQuotientRep A.toRep (OrderDual.ofDual N)) 2)).eq_of_src _ _
  let := ModuleCat.subsingleton_of_isZero hz
  exact (finiteQuotientComparisonLinearEquiv A 2).symm.injective.subsingleton

/-- Transfer vanishing from the actual inertia fixed field. -/
private theorem inertiaH2Vanishing_of_fixedField
    (h : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
      Subsingleton (absoluteCohomology
        (IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)) 2)) :
    InertiaH2Vanishing.{u} := by
  intro p hp F
  let K := F.Carrier
  let : CharZero K := Algebra.charZero_of_charZero (Padic p) K
  let I := F.absoluteInertia F.canonicalTopologicalData
  let H : ClosedSubgroup (Field.absoluteGaloisGroup K) :=
    ⟨I, F.absoluteInertia_isClosed F.canonicalTopologicalData⟩
  let U := IntermediateField.fixedField I
  let : IsGalois K U := IsGalois.of_fixedField_normal_subgroup I
    (hn := F.absoluteInertia_normal F.canonicalTopologicalData)
  let : Normal K U := inferInstance
  let j : AlgebraicClosure K →ₐ[K] AlgebraicClosure U := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure U) := j.toRingHom.toAlgebra
  let : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure U) :=
    IsScalarTower.of_algHom j
  let : Subsingleton (absoluteCohomology U 2) := h p F
  have hfix : U.fixingSubgroup = I := InfiniteGalois.fixingSubgroup_fixedField H
  change Subsingleton (continuousCohomology (k := IntegerScalars.{u}) 2
    (TopRep.res I.subtype (absoluteUnits K)))
  rw [← hfix]
  exact (Langlands.Continuous.continuousCohomologyIso
    (closureSubgroupEquiv K U) (closureSubgroupCoefficientsIso K U) 2).toContinuousLinearEquiv.injective.subsingleton

/-- Actual canonical inertia has vanishing continuous H2 with its restricted
discrete algebraic-closure unit action. -/
theorem inertiaH2Vanishing : InertiaH2Vanishing.{u} := by
  apply inertiaH2Vanishing_of_fixedField
  intro p hp F
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
  apply absoluteH2_of_finiteRelativeH2 U
  intro L hfin hgal
  apply finiteNormH2Vanishing.{u, u} U L
  intro E
  exact inertiaFixedFieldNormSurjectivity.{u} p F E L

end Langlands.ClassFieldTheory.Local
