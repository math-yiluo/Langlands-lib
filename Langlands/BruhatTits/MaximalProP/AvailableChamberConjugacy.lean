import Langlands.BruhatTits.MaximalProP.AvailableCompactOvergroup
import Langlands.Geometry.Building.BuildingChamberIncidence
import Langlands.Group.TitsBorelChambers

/-! # Conjugacy of actual chamber fixers in the zero subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.IntegralModels
  Langlands.Group Langlands.Group.TitsSystem Langlands.Group.RelativeWeyl

namespace Langlands.BruhatTits.MaximalProP

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {D : KPBuildingDatum G}

/-- Chamber maximality and the Tits facet correspondence identify any actual
chamber stabilizer with a conjugate of the distinguished Iwahori subgroup. -/
theorem exists_chamber_stabilizer_eq_conjugate_of_tits
    {Ca : Set D.base.Apartment} {W : Type u} [Group W]
    {π : D.base.normalizerInZero →* W} {Sgen : Set W}
    (hA : D.base.SatisfiesApartmentAxioms)
    (hT : D.base.IsBuildingTitsSystem Ca π Sgen)
    (C : BuildingFacet D.base.toValuationBuildingData) (hC : D.base.IsChamber C.val) :
    ∃ g : D.base.zeroSubgroup, D.base.facetZeroStabilizer C =
      conjugateSubgroup g (D.base.chamberZeroStabilizerIn Ca) := by
  obtain ⟨g, hg⟩ := hT.isParabolic_facetZeroStabilizer C
  obtain ⟨E, hE⟩ := hT.exists_facetZeroStabilizer_eq
    (hT.isTitsSystem.isAdmissibleParabolic_conjugate_borel g)
  have hCE : FacetPrecedes D.base.toValuationBuildingData C E := by
    apply (hT.facetPrecedes_iff C E).mpr
    rw [hE]
    exact hg
  have hsame := D.base.eq_of_isChamber_of_facetPrecedes hA hC hCE
  exact ⟨g, hsame.symm ▸ hE⟩

/-- Under the single-group axioms, any two actual chamber fixers are conjugate
by an element of the zero subgroup. -/
theorem exists_chamber_fixer_conjugator (hD : D.SatisfiesGroupAxioms)
    (C E : BuildingFacet D.base.toValuationBuildingData)
    (hC : D.base.IsChamber C.val) (hE : D.base.IsChamber E.val) :
    ∃ g : D.base.zeroSubgroup, facetZeroFixer D E =
      conjugateSubgroup (g : rationalPoints G) (facetZeroFixer D C) := by
  have hA := hD.affineRootSystem.apartmentAxioms
  have hΨ := hA.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
  obtain ⟨p, hp, -⟩ := hΨ.exists_regularPoint_closure (Classical.arbitrary D.base.Apartment)
  obtain ⟨W, instW, π, Sgen, hT⟩ := hD.titsSystem _ ⟨p, hp, rfl⟩
  obtain ⟨gC, hgC⟩ := exists_chamber_stabilizer_eq_conjugate_of_tits hA hT C hC
  obtain ⟨gE, hgE⟩ := exists_chamber_stabilizer_eq_conjugate_of_tits hA hT E hE
  let g := gE * gC⁻¹
  have heq : D.base.facetZeroStabilizer E =
      conjugateSubgroup g (D.base.facetZeroStabilizer C) := by
    rw [hgC, hgE, ← conjugateSubgroup_mul]
    simp only [g, mul_assoc, inv_mul_cancel, mul_one]
  have hmap : (conjugateSubgroup g (D.base.facetZeroStabilizer C)).map
      D.base.zeroSubgroup.subtype = conjugateSubgroup (g : rationalPoints G)
        ((D.base.facetZeroStabilizer C).map D.base.zeroSubgroup.subtype) := by
    simp only [conjugateSubgroup, Subgroup.map_map]
    congr 1
  have heq' := congrArg (Subgroup.map D.base.zeroSubgroup.subtype) heq
  rw [hmap, map_facetZeroStabilizer_eq_facetZeroFixer hD,
    map_facetZeroStabilizer_eq_facetZeroFixer hD] at heq'
  exact ⟨g, heq'⟩

/-- Choose an actual zero-subgroup conjugator carrying the first chamber fixer
to the second, retaining the ambient subgroup equality. -/
def chamberFixerConjugator (hD : D.SatisfiesGroupAxioms)
    (C E : BuildingFacet D.base.toValuationBuildingData)
    (hC : D.base.IsChamber C.val) (hE : D.base.IsChamber E.val) :
    {g : D.base.zeroSubgroup // facetZeroFixer D E =
      conjugateSubgroup (g : rationalPoints G) (facetZeroFixer D C)} :=
  ⟨(exists_chamber_fixer_conjugator hD C E hC hE).choose,
    (exists_chamber_fixer_conjugator hD C E hC hE).choose_spec⟩

end Langlands.BruhatTits.MaximalProP
