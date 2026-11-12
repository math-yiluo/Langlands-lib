import Langlands.ClassFieldTheory.Local.CommonClosureExistenceReduction
import Langlands.ClassFieldTheory.Local.FiniteGeometricCupArtinComparison

/-! # Common-closure reciprocity existence from geometric finite cup comparison -/

noncomputable section

namespace Langlands.LocalClassField

open Weil.Local FiniteQuotientTransport ClassFieldTheory.Local

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance geometricReductionBaseCharZero : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier

namespace CommonClosure

/-- The exact finite inverse-cup character comparison implies the genuine
Galois transfer square for the unconditionally constructed family. -/
theorem constructedReciprocityFamily_galoisTransfer_of_geometricComparison
    (hcompare : FiniteGeometricCupArtinCharacterComparison.{u}) :
    GaloisTransferRelation F (constructedReciprocityFamily F) := by
  intro E L h a
  let := (canonicalData F E).topology
  let := (canonicalData F L).topology
  apply finiteAbelianRestriction_separates F.Carrier L
  intro M hLM
  let hEM := h.trans hLM
  let : Algebra E.field L.field := (IntermediateField.inclusion h).toAlgebra
  let := finiteRestrictionAlgebra F.Carrier E M hEM
  let := finiteRestrictionAlgebra F.Carrier L M hLM
  let : IsScalarTower F.Carrier E.field L.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F.Carrier E.field M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F.Carrier L.field M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower E.field L.field M := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional E.field L.field := FiniteDimensional.right F.Carrier E.field L.field
  let : FiniteDimensional E.field M := FiniteDimensional.right F.Carrier E.field M
  let : FiniteDimensional L.field M := FiniteDimensional.right F.Carrier L.field M
  let : Normal E.field M := Normal.tower_top_of_normal F.Carrier E.field M
  let : Normal L.field M := Normal.tower_top_of_normal F.Carrier L.field M
  let : IsGalois E.field M := ⟨⟩
  let : IsGalois L.field M := ⟨⟩
  let : Algebra (Padic p) E.field := (E.asPadicField (p := p)).algebra
  let : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
  let : IsScalarTower (Padic p) E.field L.field := IsScalarTower.of_algebraMap_eq' rfl
  change finiteAbelianRestriction F.Carrier L M hLM
      (E.galoisAbelianTransfer L h
        (galoisHom F (canonicalData F) (localResidueDegree F) (constructedReciprocityFamily F) E a)) =
    finiteAbelianRestriction F.Carrier L M hLM
      (galoisHom F (canonicalData F) (localResidueDegree F) (constructedReciprocityFamily F) L
        (E.unitsInclusion L h a))
  rw [finiteAbelianRestriction_transfer]
  change relativeGaloisAbelianTransfer E.field L.field M
      (candidateFiniteRestriction F (constructedReciprocityFamily F) E M hEM a) =
    candidateFiniteRestriction F (constructedReciprocityFamily F) L M hLM
      (E.unitsInclusion L h a)
  rw [candidateFiniteRestriction_constructed, candidateFiniteRestriction_constructed]
  exact (FiniteArtinTransferReduction.geometricTransfer_of_geometricCupComparison
    (E.asPadicField (p := p)) (L.asPadicField (p := p)) M hcompare a).symm

/-- The same finite comparison implies the genuine common-closure Weil
transfer square, through the proved Galois-to-Weil transfer comparison. -/
theorem constructedReciprocityFamily_transfer_of_geometricComparison
    (hcompare : FiniteGeometricCupArtinCharacterComparison.{u}) :
    TransferRelation F (canonicalData F) (localResidueDegree F) (constructedReciprocityFamily F) :=
  (transferRelation_iff_galoisTransferRelation F (constructedReciprocityFamily F)).mpr
    (constructedReciprocityFamily_galoisTransfer_of_geometricComparison F hcompare)

/-- All normalized system laws for the constructed family follow from
the one exact finite inverse-cup character comparison. -/
theorem constructedReciprocityFamily_normalized_of_geometricComparison
    (hcompare : FiniteGeometricCupArtinCharacterComparison.{u}) (T : F.TopologicalData) :
    NormalizedSystemRelation F (canonicalData F) (localResidueDegree F) T
      (constructedReciprocityFamily F) :=
  ⟨⟨constructedReciprocityFamily_norm F,
      constructedReciprocityFamily_transfer_of_geometricComparison F hcompare,
      constructedReciprocityFamily_conjugation F,
      constructedReciprocityFamily_density F,
      constructedReciprocityFamily_completion F⟩,
    constructedReciprocityFamily_normalization F T⟩

/-- The constructed actual family packaged with all its normalized system
laws, conditional only on the exact finite comparison. -/
def normalizedSystemOfGeometricComparison
    (hcompare : FiniteGeometricCupArtinCharacterComparison.{u}) (T : F.TopologicalData) :
    {e : CandidateFamily F (canonicalData F) (localResidueDegree F) //
      NormalizedSystemRelation F (canonicalData F) (localResidueDegree F) T e} :=
  ⟨constructedReciprocityFamily F, constructedReciprocityFamily_normalized_of_geometricComparison F hcompare T⟩

end CommonClosure

/-- The unchanged common-closure existence target is reduced to the exact
finite geometric character comparison, with no other unproved premise. -/
theorem commonClosureReciprocityExistence_of_finiteGeometricCupComparison
    (hcompare : FiniteGeometricCupArtinCharacterComparison.{u}) :
    CommonClosureReciprocityExistence.{u} := by
  intro p _ F T
  exact ⟨(CommonClosure.normalizedSystemOfGeometricComparison F hcompare T).val,
    (CommonClosure.normalizedSystemOfGeometricComparison F hcompare T).property⟩

end Langlands.LocalClassField
