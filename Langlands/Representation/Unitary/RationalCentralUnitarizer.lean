import Langlands.Representation.Unitary.CentralUnitarizer
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.Representation.Plancherel.RationalCentralQuotient

/-! # Central unitarizers through the actual rational-character valuation image -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands

universe u v

namespace CentralUnitarization

open Plancherel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance instRationalCentralUnitarizer1 : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance instRationalCentralUnitarizer2 : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- Restricting the actual valuation projection to the full abstract center
has exactly the restriction of the common norm kernel as its kernel. -/
theorem rationalCentralValuation_ker :
    (((rationalCharacterValuation G).rangeRestrict).comp
      (Subgroup.center (GroupScheme.rationalPoints G)).subtype).ker =
      (rationalCommonNormKernel G).subgroupOf
        (Subgroup.center (GroupScheme.rationalPoints G)) := by
  rw [← MonoidHom.comap_ker, MonoidHom.ker_rangeRestrict,
    rationalCharacterValuation_ker]
  rfl

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- No comparison of the scheme center with the full abstract center is needed
to put a central torus's actual valuation image inside the latter image. -/
theorem finiteIndex_rationalCentralValuationImage
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    ((((rationalCharacterValuation G).rangeRestrict).comp
      (Subgroup.center (GroupScheme.rationalPoints G)).subtype).range).FiniteIndex := by
  let := hindex
  apply Subgroup.finiteIndex_of_le (H := RenardCartan.splitValuationImage s)
  rintro b ⟨t, rfl⟩
  exact ⟨⟨GroupScheme.rationalPoints.map s t,
    hs.range_le_center ⟨t, rfl⟩⟩, rfl⟩

/-- The actual norm-kernel topology theorem supplies the ambient open kernel. -/
theorem isOpen_rationalValuationProjection_ker :
    IsOpen (((rationalCharacterValuation G).rangeRestrict).ker :
      Set (GroupScheme.rationalPoints G)) := by
  rw [MonoidHom.ker_rangeRestrict, rationalCharacterValuation_ker]
  exact isOpen_rationalCommonNormKernel G

/-- A positive character of the actual rational-point group. Compactness is
explicitly required on the full abstract center, and finite index on the
actual split-component valuation image. -/
def rationalCentralUnitarizer
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    (hK : IsCompact ((rationalCommonNormKernel G).subgroupOf
      (Subgroup.center (GroupScheme.rationalPoints G)) :
        Set (Subgroup.center (GroupScheme.rationalPoints G))))
    (χ : Subgroup.center (GroupScheme.rationalPoints G) →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center (GroupScheme.rationalPoints G)))) :
    GroupScheme.rationalPoints G →* ℝ≥0ˣ := by
  letI := finiteIndex_rationalCentralValuationImage G s hs hindex
  exact centralUnitarizer (rationalCharacterValuation G).rangeRestrict
    (by simpa only [rationalCentralValuation_ker] using hK) χ hχ

@[simp]
theorem rationalCentralUnitarizer_restrict
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    (hK : IsCompact ((rationalCommonNormKernel G).subgroupOf
      (Subgroup.center (GroupScheme.rationalPoints G)) :
        Set (Subgroup.center (GroupScheme.rationalPoints G))))
    (χ : Subgroup.center (GroupScheme.rationalPoints G) →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center (GroupScheme.rationalPoints G))))
    (z : Subgroup.center (GroupScheme.rationalPoints G)) :
    rationalCentralUnitarizer G s hs hindex hK χ hχ z =
      (PositiveCharacter.normCharacter χ z)⁻¹ := by
  let := finiteIndex_rationalCentralValuationImage G s hs hindex
  exact centralUnitarizer_restrict _ _ χ hχ z

theorem isOpen_ker_rationalCentralUnitarizer
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    (hK : IsCompact ((rationalCommonNormKernel G).subgroupOf
      (Subgroup.center (GroupScheme.rationalPoints G)) :
        Set (Subgroup.center (GroupScheme.rationalPoints G))))
    (χ : Subgroup.center (GroupScheme.rationalPoints G) →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center (GroupScheme.rationalPoints G)))) :
    IsOpen ((rationalCentralUnitarizer G s hs hindex hK χ hχ).ker :
      Set (GroupScheme.rationalPoints G)) := by
  let := finiteIndex_rationalCentralValuationImage G s hs hindex
  exact isOpen_ker_centralUnitarizer _ (isOpen_rationalValuationProjection_ker G) _ χ hχ

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- The norm-one scalar character of the actual twisted representation,
constructed using precisely the actual rational-character valuation quotient. -/
def rationalTwistUnitaryCentralCharacter
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    (hK : IsCompact ((rationalCommonNormKernel G).subgroupOf
      (Subgroup.center (GroupScheme.rationalPoints G)) :
        Set (Subgroup.center (GroupScheme.rationalPoints G))))
    (ρ : Representation ℂ (GroupScheme.rationalPoints G) V)
    (χ : Subgroup.center (GroupScheme.rationalPoints G) →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center (GroupScheme.rationalPoints G))))
    (hact : ∀ (z : Subgroup.center (GroupScheme.rationalPoints G)) (v : V),
      ρ z v = (χ z : ℂ) • v) :
    UnitaryCentralCharacter
      (twist (positiveUnitsToComplex.comp
        (rationalCentralUnitarizer G s hs hindex hK χ hχ)) ρ) := by
  letI := finiteIndex_rationalCentralValuationImage G s hs hindex
  exact unitaryCentralCharacter _ (isOpen_rationalValuationProjection_ker G) _ ρ χ hχ hact

/-- Admissible Schur supplies the scalar character; the two remaining
actual-group structural inputs are not inferred from reductivity here. -/
theorem exists_rationalPositiveTwist_unitaryCentralCharacter
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    (hK : IsCompact ((rationalCommonNormKernel G).subgroupOf
      (Subgroup.center (GroupScheme.rationalPoints G)) :
        Set (Subgroup.center (GroupScheme.rationalPoints G))))
    (ρ : Representation ℂ (GroupScheme.rationalPoints G) V)
    (ha : IsAdmissible ρ) (hi : Representation.IsIrreducible ρ) :
    ∃ ν : GroupScheme.rationalPoints G →* ℝ≥0ˣ,
      IsOpen (ν.ker : Set (GroupScheme.rationalPoints G)) ∧
      Nonempty (UnitaryCentralCharacter (twist (positiveUnitsToComplex.comp ν) ρ)) := by
  obtain ⟨χ, ⟨hlc, hact⟩, _⟩ := admissibleSchur_centralCharacter ρ ha hi
  have hχ : IsOpen (χ.ker : Set (Subgroup.center (GroupScheme.rationalPoints G))) :=
    hlc.isOpen_fiber 1
  exact ⟨rationalCentralUnitarizer G s hs hindex hK χ hχ,
    isOpen_ker_rationalCentralUnitarizer G s hs hindex hK χ hχ,
    ⟨rationalTwistUnitaryCentralCharacter G s hs hindex hK ρ χ hχ hact⟩⟩

end CentralUnitarization
end Langlands
