import Langlands.ClassFieldTheory.Local.AbsoluteH2InflationStatement
import Langlands.ClassFieldTheory.Local.RelativeH2InflationProof
import Langlands.ClassFieldTheory.Local.FixedFieldStageInflation
import Langlands.ClassFieldTheory.Local.ClosureCohomologyTransport
import Langlands.Cohomology.Continuous.FiniteStageExactnessLimitProof
import Langlands.ClassFieldTheory.Local.FixedFieldStageClosureInflation
import Langlands.ClassFieldTheory.Local.FixedFieldStageRestriction

noncomputable section

open CategoryTheory Langlands.Continuous

namespace Langlands.ClassFieldTheory.Local

universe u

namespace AbsoluteH2Assembly

theorem linearExactness_of_comparison
    {R A B C A' B' C' : Type u} [CommRing R]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [Module R A] [Module R B] [Module R C]
    [Module R A'] [Module R B'] [Module R C']
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (f' : A' →ₗ[R] B') (g' : B' →ₗ[R] C')
    (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C')
    (hf : ∀ x, eB (f x) = f' (eA x))
    (hg : ∀ y, eC (g y) = g' (eB y))
    (h : Function.Injective f' ∧ LinearMap.range f' = LinearMap.ker g') :
    Function.Injective f ∧ LinearMap.range f = LinearMap.ker g := by
  constructor
  · intro x y hxy
    apply eA.injective
    apply h.1
    rw [← hf, ← hf, hxy]
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply eC.injective
      rw [map_zero, hg, hf]
      exact LinearMap.mem_ker.mp (h.2 ▸ LinearMap.mem_range_self f' (eA x))
    · intro hy
      have hy' : eB y ∈ LinearMap.ker g' := by
        apply LinearMap.mem_ker.mpr
        rw [← hg, LinearMap.mem_ker.mp hy, map_zero]
      rw [← h.2] at hy'
      obtain ⟨x, hx⟩ := hy'
      refine ⟨eA.symm x, ?_⟩
      apply eB.injective
      rw [hf, eA.apply_symm_apply, hx]

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the actual finite-stage maps follows from finite Galois exactness. -/
theorem finiteStageExactness
    (K : Type u) [Field K] [CharZero K]
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsGalois K E]
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (h : N ≤ finiteGaloisFixingSubgroup K E) :
    Function.Injective (finiteInflation (absoluteUnitDiscreteModule K).toRep 2 h) ∧
      LinearMap.range (finiteInflation (absoluteUnitDiscreteModule K).toRep 2 h).hom =
        LinearMap.ker (finiteRestriction (absoluteUnitDiscreteModule K)
          (finiteGaloisFixingSubgroup K E).toOpenSubgroup N 2).hom := by
  let := finiteStageRestrictedAlgebra K E N h
  let := finiteStageRestrictedTowerBase K E N h
  apply linearExactness_of_comparison
    (finiteInflation (absoluteUnitDiscreteModule K).toRep 2 h).hom
    (finiteRestriction (absoluteUnitDiscreteModule K)
      (finiteGaloisFixingSubgroup K E).toOpenSubgroup N 2).hom
    (relativeInflation K E (finiteStageFixedField K N) 2).hom
    (relativeRestriction K E (finiteStageFixedField K N) 2).hom
    (finiteGaloisStageRelativeIso K E 2).toLinearEquiv
    (finiteStageRelativeIso K N 2).toLinearEquiv
    (finiteStageRestrictedRelativeIso K E N h 2).toLinearEquiv
  · intro x
    exact congrArg (fun f => f x) (finiteGaloisStageRelativeIso_inflation K E 2 h)
  · intro x
    exact congrArg (fun f => f x) (finiteStageRelativeIso_restriction K E N h 2)
  · exact finiteRelativeH2InflationExactness K E (finiteStageFixedField K N)

set_option backward.isDefEq.respectTransparency false in
/-- Closure inflation identifies finite relative degree-two classes with the
kernel of restriction to the actual fixing subgroup. -/
theorem closureInflationExactness
    (K : Type u) [Field K] [CharZero K]
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsGalois K E] :
    Function.Injective (closureInflation K E 2) ∧
      (closureInflation K E 2).range =
        (continuousRestriction (absoluteUnitDiscreteModule K)
          (finiteGaloisFixingSubgroup K E).toSubgroup 2).hom.toAddMonoidHom.ker := by
  let H := finiteGaloisFixingSubgroup K E
  let eSource := (finiteGaloisStageRelativeIso K E 2).toLinearEquiv.toAddEquiv
  have hSource : ∀ x,
      finiteStageToContinuous (absoluteUnitDiscreteModule K) H 2 x =
        closureInflation K E 2 (eSource x) :=
    finiteGaloisStageRelativeIso_closureInflation K E 2
  let : CompactSpace (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure K/K))
  obtain ⟨hinj, hex⟩ :=
    finiteStageExactnessLimit IntegerScalars.{u} (Field.absoluteGaloisGroup K)
      (absoluteUnitDiscreteModule K) H 2
      (fun N h => finiteStageExactness K E N h)
  constructor
  · intro x y hxy
    have hxy' : finiteStageToContinuous (absoluteUnitDiscreteModule K) H 2 (eSource.symm x) =
        finiteStageToContinuous (absoluteUnitDiscreteModule K) H 2 (eSource.symm y) := by
      simpa only [hSource, eSource.apply_symm_apply] using hxy
    exact eSource.symm.injective (hinj hxy')
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      apply AddMonoidHom.mem_ker.mpr
      change continuousRestriction (absoluteUnitDiscreteModule K) H.toSubgroup 2
        (closureInflation K E 2 x) = 0
      have hm :
          finiteStageToContinuous (absoluteUnitDiscreteModule K) H 2 (eSource.symm x) ∈
            LinearMap.range (finiteStageToContinuous (absoluteUnitDiscreteModule K) H 2).hom :=
        ⟨eSource.symm x, rfl⟩
      rw [hex] at hm
      have hz := LinearMap.mem_ker.mp hm
      change continuousRestriction (absoluteUnitDiscreteModule K) H.toSubgroup 2
        (finiteStageToContinuous (absoluteUnitDiscreteModule K) H 2 (eSource.symm x)) = 0 at hz
      rw [hSource, eSource.apply_symm_apply] at hz
      exact hz
    · intro hy
      have hz : continuousRestriction (absoluteUnitDiscreteModule K) H.toSubgroup 2 y = 0 :=
        AddMonoidHom.mem_ker.mp hy
      have hm : y ∈ LinearMap.range (finiteStageToContinuous (absoluteUnitDiscreteModule K) H 2).hom := by
        rw [hex]
        exact hz
      obtain ⟨x, hx⟩ := hm
      exact ⟨eSource x, (hSource x).symm.trans hx⟩

end AbsoluteH2Assembly

set_option backward.isDefEq.respectTransparency false in
/-- Degree-two inflation is injective with range the absolute restriction kernel. -/
theorem absoluteH2InflationExactness : AbsoluteH2InflationExactness.{u} := by
  intro K _ _ E _ _ _ _
  obtain ⟨hinj, hex⟩ := AbsoluteH2Assembly.closureInflationExactness K E
  refine ⟨hinj, hex.trans ?_⟩
  ext x
  change continuousRestriction (absoluteUnitDiscreteModule K)
      (finiteGaloisFixingSubgroup K E).toSubgroup 2 x = 0 ↔
    absoluteRestriction K E 2 x = 0
  exact (absoluteRestriction_eq_zero_iff_subgroup K E 2 x).symm

end Langlands.ClassFieldTheory.Local
