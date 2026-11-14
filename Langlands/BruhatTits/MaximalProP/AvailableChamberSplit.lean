import Langlands.BruhatTits.MaximalProP.AvailableClassification
import Langlands.Geometry.Building.TitsNormalizerApartmentStabilizer
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.Group.SplitTitsSylow

/-! # Chamber normalizers from pro-p Iwahori factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.IntegralModels
  Langlands.AlgebraicGeometry.PointTopology Langlands.Cohomology
  Langlands.Group.RelativeWeyl
open Langlands.Geometry.Building.ParahoricBuildingData

namespace Langlands.BruhatTits.MaximalProP

/-- Move the third factor past a normalizing middle factor. -/
private theorem exists_two_factors_of_three
    {Γ Z : Type*} [Group Γ] [Group Z]
    (U V W : Subgroup Γ) (K : Subgroup Z) (f : Z →* Γ)
    (hV : V ≤ U) (hW : W ≤ U)
    (hK : K.map f ≤ Subgroup.normalizer (U : Set Γ))
    (b : Γ) (hb : ∃ a : V, ∃ z : K, ∃ v : W,
      b = (a : Γ) * f (z : Z) * (v : Γ)) :
    ∃ q : U × K, b = (q.1 : Γ) * f (q.2 : Z) := by
  obtain ⟨a, z, v, rfl⟩ := hb
  have hcN : f (z : Z) ∈ Subgroup.normalizer (U : Set Γ) := hK ⟨z, z.property, rfl⟩
  have hcv : f (z : Z) * (v : Γ) * (f (z : Z))⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp hcN _).mp (hW v.property)
  refine ⟨(⟨(a : Γ) * (f (z : Z) * (v : Γ) * (f (z : Z))⁻¹),
    U.mul_mem (hV a.property) hcv⟩, z), ?_⟩
  simp only [mul_assoc, inv_mul_cancel, mul_one]

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {D : KPBuildingDatum G}

local instance chamberSplitPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- The setwise zero stabilizer of an apartment chamber is its actual facet
fixer, under the single-group axioms. -/
theorem zeroStabilizer_eq_chamberFacetZeroFixer (hD : D.SatisfiesGroupAxioms)
    {Ca : Set D.base.Apartment} (hCa : AffineRootSystem.IsChamber D.base.affineRoots Ca) :
    D.base.zeroStabilizer (D.base.apartmentMap '' Ca) =
      facetZeroFixer D (chamberFacet hCa.isFacet) := by
  rw [← map_facetZeroStabilizer_eq_facetZeroFixer hD]
  exact (D.base.map_zeroStabilizerIn _).symm

/-- An apartment chamber represents a chamber in the quotient building. -/
theorem isChamber_chamberFacet
    {Ca : Set D.base.Apartment} (hCa : AffineRootSystem.IsChamber D.base.affineRoots Ca) :
    D.base.IsChamber (chamberFacet hCa.isFacet).val := by
  refine ⟨1, Ca, hCa, ?_⟩
  simp only [chamberFacet, one_smul]

/-- A pro-p unipotent Iwahori factor belongs to the positive subgroup. -/
theorem unipotent_factor_le_chamber_positive
    (hD : D.SatisfiesGroupAxioms)
    {Ca : Set D.base.Apartment} (hCa : AffineRootSystem.IsChamber D.base.affineRoots Ca)
    (ν : cocharacterLattice D.base.S)
    (hU : IsProPSubgroup (ringChar 𝓀[F])
      (D.base.zeroStabilizerUnipotentPoints ν (D.base.apartmentMap '' Ca))) :
    D.base.zeroStabilizerUnipotentPoints ν (D.base.apartmentMap '' Ca) ≤
      facetPositiveSubgroup D (chamberFacet hCa.isFacet) := by
  apply le_chamber_positive_of_isProP hD (facetReductiveComparisons hD)
    (chamberFacet hCa.isFacet) (isChamber_chamberFacet hCa) _ hU
  rw [← zeroStabilizer_eq_chamberFacetZeroFixer hD hCa]
  exact inf_le_right

/-- If the two unipotent Iwahori factors are pro-p, every chamber fixer element
is a positive-subgroup element times an actual centralizer-zero point. -/
theorem exists_chamber_positive_mul_centralizerZero
    (hD : D.SatisfiesGroupAxioms)
    {Ca : Set D.base.Apartment} (hCa : AffineRootSystem.IsChamber D.base.affineRoots Ca)
    (ν : cocharacterLattice D.base.S) (hν : IsGenericCocharacter D.base.i ν)
    (hpos : IsProPSubgroup (ringChar 𝓀[F])
      (D.base.zeroStabilizerUnipotentPoints ν (D.base.apartmentMap '' Ca)))
    (hneg : IsProPSubgroup (ringChar 𝓀[F])
      (D.base.zeroStabilizerUnipotentPoints (-ν) (D.base.apartmentMap '' Ca)))
    (b : rationalPoints G) (hb : b ∈ facetZeroFixer D (chamberFacet hCa.isFacet)) :
    ∃ q : facetPositiveSubgroup D (chamberFacet hCa.isFacet) × D.base.centralizerZero,
      b = (q.1 : rationalPoints G) *
        rationalPoints.map D.base.centralizer.j (q.2 : rationalPoints D.base.centralizer.Z) := by
  have hfix := zeroStabilizer_eq_chamberFacetZeroFixer hD hCa
  have hI := hD.iwahoriDecomposition Ca hCa ν hν
  apply exists_two_factors_of_three
    (facetPositiveSubgroup D (chamberFacet hCa.isFacet))
    (D.base.zeroStabilizerUnipotentPoints ν (D.base.apartmentMap '' Ca))
    (D.base.zeroStabilizerUnipotentPoints (-ν) (D.base.apartmentMap '' Ca))
    D.base.centralizerZero (rationalPoints.map D.base.centralizer.j)
    (unipotent_factor_le_chamber_positive hD hCa ν hpos)
    (unipotent_factor_le_chamber_positive hD hCa (-ν) hneg)
  · intro c hc
    have hcI := hI.map_centralizerZero_le hc
    rw [hfix] at hcI
    exact (facetZeroFixer_le_facetPositiveZeroNormalizer hD _ hcI).1
  · have hb' : b ∈ Set.range
        (D.base.zeroStabilizerProduct (D.base.apartmentMap '' Ca) ν) := by
      rw [hI.range_product, hfix]
      exact hb
    obtain ⟨⟨a, z, v⟩, hprod⟩ := hb'
    exact ⟨a, z, v, hprod.symm⟩

/-- Choose actual positive and centralizer-zero factors of an Iwahori element,
retaining their multiplication identity. -/
def chamberPositiveCentralizerFactors
    (hD : D.SatisfiesGroupAxioms)
    {Ca : Set D.base.Apartment} (hCa : AffineRootSystem.IsChamber D.base.affineRoots Ca)
    (ν : cocharacterLattice D.base.S) (hν : IsGenericCocharacter D.base.i ν)
    (hpos : IsProPSubgroup (ringChar 𝓀[F])
      (D.base.zeroStabilizerUnipotentPoints ν (D.base.apartmentMap '' Ca)))
    (hneg : IsProPSubgroup (ringChar 𝓀[F])
      (D.base.zeroStabilizerUnipotentPoints (-ν) (D.base.apartmentMap '' Ca)))
    (b : facetZeroFixer D (chamberFacet hCa.isFacet)) :
    {q : facetPositiveSubgroup D (chamberFacet hCa.isFacet) × D.base.centralizerZero //
      (b : rationalPoints G) = (q.1 : rationalPoints G) *
        rationalPoints.map D.base.centralizer.j (q.2 : rationalPoints D.base.centralizer.Z)} :=
  ⟨(exists_chamber_positive_mul_centralizerZero hD hCa ν hν hpos hneg b b.property).choose,
    (exists_chamber_positive_mul_centralizerZero hD hCa ν hν hpos hneg b b.property).choose_spec⟩

/-- The split Tits-system argument identifies the positive normalizer for an
apartment chamber once its two unipotent factors are pro-p. -/
theorem chamber_normalizer_eq_of_unipotent_factors
    (hD : D.SatisfiesGroupAxioms)
    {Ca : Set D.base.Apartment} (hCa : AffineRootSystem.IsChamber D.base.affineRoots Ca)
    (ν : cocharacterLattice D.base.S) (hν : IsGenericCocharacter D.base.i ν)
    (hpos : IsProPSubgroup (ringChar 𝓀[F])
      (D.base.zeroStabilizerUnipotentPoints ν (D.base.apartmentMap '' Ca)))
    (hneg : IsProPSubgroup (ringChar 𝓀[F])
      (D.base.zeroStabilizerUnipotentPoints (-ν) (D.base.apartmentMap '' Ca))) :
    facetPositiveZeroNormalizer D (chamberFacet hCa.isFacet) =
      facetZeroFixer D (chamberFacet hCa.isFacet) := by
  let C : BuildingFacet D.base.toValuationBuildingData := chamberFacet hCa.isFacet
  let A := D.base.zeroSubgroup
  let U := (facetPositiveSubgroup D C).subgroupOf A
  let B := D.base.chamberZeroStabilizerIn Ca
  have hfix := zeroStabilizer_eq_chamberFacetZeroFixer hD hCa
  have hBmap : B.map A.subtype = facetZeroFixer D C := by
    exact (D.base.map_zeroStabilizerIn _).trans hfix
  have hU0 : facetPositiveSubgroup D C ≤ A :=
    facetPositiveSubgroup_le_zeroSubgroup D C hD
  have hUB : U ≤ B := by
    intro x hx
    have h := facetPositiveSubgroup_le_facetZeroFixer D C hD hx
    rw [← hfix] at h
    exact h.2
  have hBU : B ≤ Subgroup.normalizer (U : Set A) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hU0]
    intro x hx
    have hxI : (x : rationalPoints G) ∈ facetZeroFixer D C := by
      rw [← hfix]
      exact ⟨x.property, hx⟩
    exact (facetZeroFixer_le_facetPositiveZeroNormalizer hD C hxI).1
  obtain ⟨W, instW, π, Sgen, hT⟩ := hD.titsSystem Ca hCa
  have hsplit : ∀ b ∈ B, ∃ u ∈ U, ∃ t : D.base.normalizerInZero,
      π t = 1 ∧ b = u * t := by
    intro b hb
    have hbI : (b : rationalPoints G) ∈ facetZeroFixer D C := by
      rw [← hfix]
      exact ⟨b.property, hb⟩
    obtain ⟨q, hq⟩ := exists_chamber_positive_mul_centralizerZero hD hCa ν hν hpos hneg b hbI
    let c := rationalPoints.map D.base.centralizer.j (q.2 : rationalPoints D.base.centralizer.Z)
    have hcI : c ∈ facetZeroFixer D C := by
      rw [← hfix]
      exact (hD.iwahoriDecomposition Ca hCa ν hν).map_centralizerZero_le
        ⟨q.2, q.2.property, rfl⟩
    have hc0 : c ∈ A := hcI.2
    have hcN : c ∈ normalizerPoints D.base.i :=
      (D.base.centralizer.toNormalizer q.2).property
    let t : D.base.normalizerInZero := ⟨⟨c, hc0⟩, hcN⟩
    refine ⟨⟨q.1, hU0 q.1.property⟩, q.1.property, t, ?_, ?_⟩
    · apply (hT.isTitsSystem.mem_iff t).mp
      exact (show c ∈ D.base.zeroStabilizer (D.base.apartmentMap '' Ca) by
        rw [hfix]; exact hcI).2
    · exact Subtype.ext hq
  have hnorm : Subgroup.normalizer (U : Set A) = B :=
    hT.isTitsSystem.normalizer_eq_of_split hUB hBU hsplit
  have hmap := congrArg (Subgroup.map A.subtype) hnorm
  rw [← Subgroup.subgroupOf_normalizer_eq hU0,
    Subgroup.subgroupOf_map_subtype, hBmap] at hmap
  exact hmap

end Langlands.BruhatTits.MaximalProP
