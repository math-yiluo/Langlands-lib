import Langlands.Geometry.FormalGroup.SpecialAtlasSubfieldTwist
import Langlands.Algebra.EtaleOrderConjugation
import Langlands.Algebra.LocalDivisionConjugationResidue
import Langlands.CommutativeAlgebra.HenselianEtaleResidueAutomorphism
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Arbitrary division-unit twists of the actual special formal atlases -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v s

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel CentralDivision ModuleLaw
open DivisionValuation (Residue reduction conjInteger conjResidue)

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance : Field (Residue (localReducedNormValuation K D)) :=
  localDivisionResidueField K D
local instance : Algebra 𝓀[K] (Residue (localReducedNormValuation K D)) :=
  localDivisionResidueAlgebra K D

private theorem conjInteger_inv (g : Dˣ) (x : IntegerRing K D) :
    conjInteger (localReducedNormValuation K D) g⁻¹ x = conjugation K D g x := by
  apply Subtype.ext
  rw [DivisionValuation.conjInteger_coe, conjugation_coe, inv_inv]

private def divisionResidueConjugation (g : Dˣ) :
    Residue (localReducedNormValuation K D) →ₐ[𝓀[K]] Residue (localReducedNormValuation K D) where
  toRingHom := conjResidue (localReducedNormValuation K D) g⁻¹
  commutes' a := by
    obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective (R := 𝒪[K]) a
    change conjResidue (localReducedNormValuation K D) g⁻¹
        (reduction (localReducedNormValuation K D) (algebraMap 𝒪[K] (IntegerRing K D) a₀)) =
      reduction (localReducedNormValuation K D) (algebraMap 𝒪[K] (IntegerRing K D) a₀)
    rw [DivisionValuation.conjResidue_reduction, conjInteger_inv, AlgEquiv.commutes]

private theorem divisionResidueConjugation_reduction (g : Dˣ) (x : IntegerRing K D) :
    divisionResidueConjugation K D g (reduction (localReducedNormValuation K D) x) =
      reduction (localReducedNormValuation K D) (conjugation K D g x) := by
  change conjResidue (localReducedNormValuation K D) g⁻¹ (reduction (localReducedNormValuation K D) x) = _
  rw [DivisionValuation.conjResidue_reduction, conjInteger_inv]

local instance : IsLocalHom ((reduction (localReducedNormValuation K D)).comp
    (subfieldIntegerInclusion K D ι).toRingHom) where
  map_nonunit c hc :=
    (DivisionValuation.isUnit_iff_value_eq_one (localDivisionSubfieldValuation K D ι) c).mpr
      ((DivisionValuation.reduction_ne_zero_iff (localReducedNormValuation K D)
        (subfieldIntegerInclusion K D ι c)).mp (isUnit_iff_ne_zero.mp hc))

private def subfieldResidueInclusion [IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι))] :
    IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]]
      Residue (localReducedNormValuation K D) where
  toRingHom := IsLocalRing.ResidueField.lift ((reduction (localReducedNormValuation K D)).comp
    (subfieldIntegerInclusion K D ι).toRingHom)
  commutes' a := by
    obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective (R := 𝒪[K]) a
    change reduction (localReducedNormValuation K D)
        (subfieldIntegerInclusion K D ι (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι) a₀)) =
      reduction (localReducedNormValuation K D) (algebraMap 𝒪[K] (IntegerRing K D) a₀)
    rw [AlgHom.commutes]

private theorem subfieldResidueInclusion_reduction
    [IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι))]
    (x : SubfieldIntegerRing K D ι) :
    subfieldResidueInclusion K D ι (IsLocalRing.residue (SubfieldIntegerRing K D ι) x) =
      reduction (localReducedNormValuation K D) (subfieldIntegerInclusion K D ι x) := rfl

/-- Every division unit has an integral conjugation factorization on the fixed unramified order. -/
theorem conjugationSubfieldFactorization (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) (g : Dˣ) :
    ConjugationSubfieldFactorization K D ι g := by
  let C := SubfieldIntegerRing K D ι
  let kC := IsLocalRing.ResidueField C
  let kD := Residue (localReducedNormValuation K D)
  let : FiniteDimensional K L := hL.1
  let : Module.Finite 𝒪[K] C := hL.2.1
  let : Algebra.Etale 𝒪[K] C := hL.2.2.1
  let : HenselianLocalRing C := localDivisionSubfield_henselian K D ι
  let : FaithfulSMul 𝒪[K] C := (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
    intro a b h
    apply Subtype.ext
    exact (algebraMap K L).injective (congrArg Subtype.val h))
  let j := subfieldResidueInclusion K D ι
  let : Finite kC := Finite.of_injective j j.injective
  let : Algebra kC kD := j.toRingHom.toAlgebra
  let : IsScalarTower 𝓀[K] kC kD := .of_algebraMap_eq' j.comp_algebraMap.symm
  let α := divisionResidueConjugation K D g
  let σ := α.restrictNormal' kC
  let β := HenselianEtale.liftResidueAut σ
  let i := subfieldIntegerInclusion K D ι
  let f := (conjugation K D g).toAlgHom.comp i
  let f' := i.comp β.toAlgHom
  have hred (c : C) :
      reduction (localReducedNormValuation K D) (f c) =
        reduction (localReducedNormValuation K D) (f' c) := by
    change reduction (localReducedNormValuation K D) (conjugation K D g (i c)) =
      reduction (localReducedNormValuation K D) (i (β c))
    rw [← divisionResidueConjugation_reduction, ← subfieldResidueInclusion_reduction,
      ← subfieldResidueInclusion_reduction, HenselianEtale.residue_liftResidueAut]
    exact (α.restrictNormal_commutes kC (IsLocalRing.residue C c)).symm
  obtain ⟨a, ha⟩ := EtaleOrderConjugation.exists_integerUnit_conj
    (localReducedNormValuation K D) f f' hred
  exact ⟨a, β.toRingEquiv, fun c => (ha c).trans (conjugation_integerUnit K D a (i (β c))).symm⟩

variable {K D ι}
variable {R S : Type v} [CommRing R] [Algebra 𝒪[K] R]
  [CommRing S] [Algebra 𝒪[K] S]

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace SpecialModule

/-- The actual conjugated order action gives a special module for every division unit. -/
def twistDivisionUnit (X : SpecialModule K D ι R) (g : Dˣ) : SpecialModule K D ι R :=
  X.twistOfSubfieldFactorization g (conjugationSubfieldFactorization K D ι X.unramified g)

theorem twistDivisionUnit_height_iff (X : SpecialModule K D ι R) (g : Dˣ) (π : 𝒪[K]) :
    (X.twistDivisionUnit g).HasHeightSquared π ↔ X.HasHeightSquared π := Iff.rfl

theorem twistDivisionUnit_map (X : SpecialModule K D ι R) (g : Dˣ) (θ : R →ₐ[𝒪[K]] S) :
    (X.twistDivisionUnit g).mapSameUniverse θ = (X.mapSameUniverse θ).twistDivisionUnit g := rfl

end SpecialModule

namespace SpecialAtlas

/-- The special atlas for the inverse-conjugated action of any division unit. -/
def twistDivisionUnit (X : SpecialAtlas K D ι R) (g : Dˣ) : SpecialAtlas K D ι R :=
  X.twistOfSubfieldFactorization g (conjugationSubfieldFactorization K D ι X.unramified g)

/-- The actual whole-order rational atlas maps identify the original atlas with its twist. -/
def twistDivisionUnitQuasiIsogeny (X : SpecialAtlas K D ι R) (g : Dˣ) :
    BasicAtlas.OrderAction.QuasiIsogeny K X.order (X.twistDivisionUnit g).order rfl :=
  atlasTwistQuasiIsogeny K D X.order g

theorem twistDivisionUnit_height_iff (X : SpecialAtlas K D ι R) (g : Dˣ) (π : 𝒪[K]) :
    (X.twistDivisionUnit g).HasHeightSquared π ↔ X.HasHeightSquared π := Iff.rfl

theorem twistDivisionUnit_baseChange (X : SpecialAtlas K D ι R) (g : Dˣ) (B : CommAlgCat.{v} R) :
    (X.twistDivisionUnit g).baseChange B = (X.baseChange B).twistDivisionUnit g := rfl

@[simp]
theorem twistDivisionUnit_integerUnit (X : SpecialAtlas K D ι R) (a : (IntegerRing K D)ˣ) :
    X.twistDivisionUnit (integerUnit K D a) = X.twistIntegerUnit a := rfl

namespace HeightSquaredAtlas

/-- Keep the scalar-kernel height certificate under any division-unit twist. -/
def twistDivisionUnit {π : 𝒪[K]}
    (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π) (g : Dˣ) :
    HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π :=
  ⟨X.val.twistDivisionUnit g, X.property⟩

end HeightSquaredAtlas
end SpecialAtlas
end Langlands.FormalGroup.LocalDivision
