import Langlands.ClassFieldTheory.Local.AbsoluteRestrictionImage
import Langlands.ClassFieldTheory.Local.FixedFieldStages
import Langlands.Cohomology.Continuous.EquivalenceTransport
import Langlands.Cohomology.Continuous.Corestriction

noncomputable section

open CategoryTheory Langlands.Continuous

namespace Langlands.ClassFieldTheory.Local

universe u

local instance absoluteGroupCompact (K : Type u) [Field K] [CharZero K] :
    CompactSpace (Field.absoluteGaloisGroup K) :=
  inferInstanceAs (CompactSpace Gal(AlgebraicClosure K/K))

namespace AbsoluteRestriction

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]

/-- The supplied closure equivalence on the actual unit modules. -/
def unitLinearEquiv : absoluteUnits K ≃ₗ[IntegerScalars.{u}] absoluteUnits L :=
  (Units.mapEquiv (closureEquiv K L).toMulEquiv).toAdditive.toIntLinearEquiv.restrictScalars
    IntegerScalars.{u}

/-- Discrete topology makes the coefficient equivalence continuous in both directions. -/
def unitContinuousEquiv : absoluteUnits K ≃L[IntegerScalars.{u}] absoluteUnits L :=
  { unitLinearEquiv K L with
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

/-- Its forward map is exactly the existing absolute-restriction coefficient map. -/
theorem unitLinearEquiv_apply (x : absoluteUnits K) :
    unitLinearEquiv K L x = absoluteRestrictionCoefficients K L x := rfl

/-- The inverse coefficient map, equivariant for the actual absolute Galois map. -/
def coefficientsInverse :
    absoluteUnits L ⟶ TopRep.res (Field.absoluteGaloisGroup.mapOfAlgebra K L) (absoluteUnits K) where
  hom' :=
    { toContinuousLinearMap := (unitContinuousEquiv K L).symm.toContinuousLinearMap
      isIntertwining' σ := by
        apply ContinuousLinearMap.ext
        intro x
        apply (unitLinearEquiv K L).injective
        change unitLinearEquiv K L
          ((unitLinearEquiv K L).symm ((absoluteUnits L).ρ σ x)) =
            unitLinearEquiv K L
              ((absoluteUnits K).ρ (Field.absoluteGaloisGroup.mapOfAlgebra K L σ)
                ((unitLinearEquiv K L).symm x))
        rw [LinearEquiv.apply_symm_apply]
        have h := TopRep.hom_comm_apply (absoluteRestrictionCoefficients K L) σ
          ((unitLinearEquiv K L).symm x)
        change unitLinearEquiv K L
          ((absoluteUnits K).ρ (Field.absoluteGaloisGroup.mapOfAlgebra K L σ)
            ((unitLinearEquiv K L).symm x)) =
              (absoluteUnits L).ρ σ
                (unitLinearEquiv K L ((unitLinearEquiv K L).symm x)) at h
        rw [LinearEquiv.apply_symm_apply] at h
        exact h.symm }

/-- Absolute restriction has an intrinsic coefficient isomorphism for the supplied embedding. -/
def coefficientsIso :
    TopRep.res (Field.absoluteGaloisGroup.mapOfAlgebra K L) (absoluteUnits K) ≅ absoluteUnits L where
  hom := absoluteRestrictionCoefficients K L
  inv := coefficientsInverse K L
  hom_inv_id := by
    ext x
    exact (unitLinearEquiv K L).symm_apply_apply x
  inv_hom_id := by
    ext x
    exact (unitLinearEquiv K L).apply_symm_apply x

@[simp] theorem coefficientsIso_hom :
    (coefficientsIso K L).hom = absoluteRestrictionCoefficients K L := rfl

variable [CharZero K]

local instance subgroupIsTopologicalGroup : IsTopologicalGroup (openSubgroup K L) := by
  change IsTopologicalGroup (imageField K L).fixingSubgroup
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient isomorphism over the actual open image of absolute restriction. -/
def subgroupCoefficientsIso :
    TopRep.res (groupEquiv K L).toMonoidHom
      ((absoluteUnitDiscreteModule K).restrict (openSubgroup K L).toSubgroup).toTopRep ≅
        absoluteUnits L :=
  coefficientsIso K L

set_option backward.isDefEq.respectTransparency false in
/-- Group and coefficient transport from the open image to upper absolute cohomology. -/
def subgroupCohomologyIso (q : ℕ) :
    continuousCohomology q
      ((absoluteUnitDiscreteModule K).restrict (openSubgroup K L).toSubgroup).toTopRep ≅
        absoluteCohomology L q :=
  Langlands.Continuous.continuousCohomologyIso (groupEquiv K L)
    (subgroupCoefficientsIso K L) q

@[simp]
theorem subgroupCohomologyIso_hom (q : ℕ) :
    (subgroupCohomologyIso K L q).hom =
      ContinuousCohomology.map (subgroupMap K L) (subgroupCoefficientsIso K L).hom q := rfl

set_option backward.isDefEq.respectTransparency false in
/-- This transport identifies genuine subgroup restriction with absolute restriction. -/
theorem continuousRestriction_comp_subgroupCohomologyIso (q : ℕ) :
    continuousRestriction (absoluteUnitDiscreteModule K) (openSubgroup K L).toSubgroup q ≫
        (subgroupCohomologyIso K L q).hom =
      absoluteRestriction K L q := by
  unfold continuousRestriction subgroupCohomologyIso
  rw [Langlands.Continuous.continuousCohomologyIso_hom,
    ← ContinuousCohomology.map_comp]
  rfl

end AbsoluteRestriction

variable (K L : Type u) [Field K] [Field L] [CharZero K]
  [Algebra K L] [FiniteDimensional K L]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]

/-- Absolute corestriction for any finite extension, on the underlying continuous
cohomology modules, using the exact supplied closure embedding. -/
def absoluteCorestriction (q : ℕ) :
    (forget₂ (TopModuleCat.{u} IntegerScalars.{u}) (ModuleCat.{u} IntegerScalars.{u})).obj
        (absoluteCohomology L q) ⟶
      (forget₂ (TopModuleCat.{u} IntegerScalars.{u}) (ModuleCat.{u} IntegerScalars.{u})).obj
        (absoluteCohomology K q) :=
  (forget₂ (TopModuleCat.{u} IntegerScalars.{u}) (ModuleCat.{u} IntegerScalars.{u})).map
      (AbsoluteRestriction.subgroupCohomologyIso K L q).inv ≫
    continuousCorestriction (absoluteUnitDiscreteModule K)
      (AbsoluteRestriction.openSubgroup K L) q

set_option backward.isDefEq.respectTransparency false in
/-- Corestriction after forward transport is precisely the Library's open-subgroup transfer. -/
theorem subgroupCohomologyIso_comp_absoluteCorestriction (q : ℕ) :
    (forget₂ (TopModuleCat.{u} IntegerScalars.{u}) (ModuleCat.{u} IntegerScalars.{u})).map
        (AbsoluteRestriction.subgroupCohomologyIso K L q).hom ≫
      absoluteCorestriction K L q =
        continuousCorestriction (absoluteUnitDiscreteModule K)
          (AbsoluteRestriction.openSubgroup K L) q := by
  unfold absoluteCorestriction
  rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Every finite normal stage inside the actual image computes this absolute transfer. -/
theorem finiteStageToContinuous_comp_absoluteCorestriction
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (hN : N.toSubgroup ≤ (AbsoluteRestriction.openSubgroup K L).toSubgroup) (q : ℕ) :
    finiteStageToContinuous
        ((absoluteUnitDiscreteModule K).restrict (AbsoluteRestriction.openSubgroup K L).toSubgroup)
        (restrictOpenNormal (AbsoluteRestriction.openSubgroup K L) N) q ≫
      (forget₂ (TopModuleCat.{u} IntegerScalars.{u}) (ModuleCat.{u} IntegerScalars.{u})).map
        (AbsoluteRestriction.subgroupCohomologyIso K L q).hom ≫
      absoluteCorestriction K L q =
    finiteCorestriction (absoluteUnitDiscreteModule K).toRep
        (AbsoluteRestriction.openSubgroup K L) N hN q ≫
      finiteStageToContinuous (absoluteUnitDiscreteModule K) N q := by
  rw [subgroupCohomologyIso_comp_absoluteCorestriction]
  exact finiteStageToContinuous_comp_corestriction (absoluteUnitDiscreteModule K)
    (AbsoluteRestriction.openSubgroup K L) N hN q

end Langlands.ClassFieldTheory.Local
