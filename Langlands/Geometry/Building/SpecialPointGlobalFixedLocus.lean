import Langlands.Geometry.Building.SpecialPointFixedLocus
import Langlands.Geometry.Building.ApartmentFixedPointReduction

/-! # The global fixed locus of a special point's norm-one stabilizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- Conjugating a norm-one point stabilizer element gives one for the translated
point, since the actual common rational-character norm kernel is normal. -/
theorem conj_mem_compactStabilizer (g : rationalPoints G)
    {x : B.ReducedBuilding} {h : rationalPoints G}
    (hh : h ∈ B.compactStabilizer x) :
    g * h * g⁻¹ ∈ B.compactStabilizer (g • x) := by
  obtain ⟨hnorm, hfix⟩ := B.mem_compactStabilizer.mp hh
  apply B.mem_compactStabilizer.mpr
  refine ⟨(rationalCommonNormKernel_normal G).conj_mem h hnorm g, ?_⟩
  simpa only [mul_smul, inv_smul_smul] using congrArg (g • ·) hfix

/-- With actual common apartments, the apartment-local calculation at a special
point gives uniqueness on the whole original quotient. -/
theorem eq_of_compactStabilizer_fixed_of_special_apartmentPoint
    (hA : B.SatisfiesApartmentAxioms)
    (hE : RelativeRoot.HasOppositeFactorPairs B.i)
    (hinj : Function.Injective B.apartmentMap)
    {x : B.Apartment} (hx : AffineRootSystem.IsSpecialPoint B.affineRoots x)
    (hcommon : B.HasCommonApartmentWith (B.apartmentMap x))
    {y : B.ReducedBuilding}
    (hy : ∀ g : rationalPoints G,
      g ∈ B.compactStabilizer (B.apartmentMap x) → g • y = y) :
    y = B.apartmentMap x := by
  apply B.eq_of_compactStabilizer_fixed_of_apartment
    hA.topologyCompatible x hcommon _ y hy
  intro z hz hfixed
  exact B.eq_of_compactStabilizer_fixed_of_isSpecialPoint hA hE hinj hx hz hfixed

/-- Global uniqueness is preserved by translating the special apartment point
and its actual norm-one stabilizer in the existing rational-point action. -/
theorem eq_of_compactStabilizer_fixed_of_special_translate
    (hA : B.SatisfiesApartmentAxioms)
    (hE : RelativeRoot.HasOppositeFactorPairs B.i)
    (hinj : Function.Injective B.apartmentMap)
    {x : B.Apartment} (hx : AffineRootSystem.IsSpecialPoint B.affineRoots x)
    (hcommon : B.HasCommonApartmentWith (B.apartmentMap x))
    (g : rationalPoints G) {y : B.ReducedBuilding}
    (hy : ∀ h : rationalPoints G,
      h ∈ B.compactStabilizer (g • B.apartmentMap x) → h • y = y) :
    y = g • B.apartmentMap x := by
  have hfixed : ∀ h : rationalPoints G,
      h ∈ B.compactStabilizer (B.apartmentMap x) →
        h • (g⁻¹ • y) = g⁻¹ • y := by
    intro h hh
    have hc := hy (g * h * g⁻¹) (B.conj_mem_compactStabilizer g hh)
    have hc' := congrArg (g⁻¹ • ·) hc
    simpa only [mul_smul, inv_smul_smul] using hc'
  have heq := B.eq_of_compactStabilizer_fixed_of_special_apartmentPoint
    hA hE hinj hx hcommon hfixed
  simpa only [smul_inv_smul] using congrArg (g • ·) heq

/-- A special point in any actual translated apartment is globally determined
by its norm-one stabilizer under common-apartment coverage of base points. -/
theorem eq_of_compactStabilizer_fixed_of_special_buildingPoint
    (hA : B.SatisfiesApartmentAxioms)
    (hE : RelativeRoot.HasOppositeFactorPairs B.i)
    (hinj : Function.Injective B.apartmentMap)
    (hcommon : ∀ x : B.Apartment,
      B.HasCommonApartmentWith (B.apartmentMap x))
    {z : B.ReducedBuilding} (hz : B.IsSpecialPoint z)
    {y : B.ReducedBuilding}
    (hy : ∀ g : rationalPoints G,
      g ∈ B.compactStabilizer z → g • y = y) :
    y = z := by
  obtain ⟨g, x, rfl, hx⟩ := hz
  exact B.eq_of_compactStabilizer_fixed_of_special_translate
    hA hE hinj hx (hcommon x) g hy

/-- Construct the unique-element structure on the actual fixed-point subtype
of the existing norm-one stabilizer at the supplied special point. -/
@[instance_reducible] def specialPointFixedLocusUnique
    (hA : B.SatisfiesApartmentAxioms)
    (hE : RelativeRoot.HasOppositeFactorPairs B.i)
    (hinj : Function.Injective B.apartmentMap)
    (hcommon : ∀ x : B.Apartment,
      B.HasCommonApartmentWith (B.apartmentMap x))
    (z : B.ReducedBuilding) (hz : B.IsSpecialPoint z) :
    Unique (MulAction.fixedPoints (B.compactStabilizer z) B.ReducedBuilding) where
  default := ⟨z, fun g => (B.mem_compactStabilizer.mp g.property).2⟩
  uniq y := Subtype.ext
    (B.eq_of_compactStabilizer_fixed_of_special_buildingPoint hA hE hinj hcommon hz
      (fun g hg => y.property ⟨g, hg⟩))

end Langlands.Geometry.Building.ValuationBuildingData
