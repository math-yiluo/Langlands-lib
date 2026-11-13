import Langlands.Geometry.Building.GenericVertexApartmentRigidity
import Langlands.Geometry.Building.IntegerValuationCommonApartments

/-! # Global vertex fixed loci from common apartments -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Common apartments extend vertex rigidity for sharp fixers from the base
apartment to the entire actual quotient. -/
theorem eq_of_vertex_of_fixed_by_sharpFixer_of_commonApartments
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hcommon : D.HasCommonApartments)
    {x : D.Apartment} (hx : AffineRootSystem.IsVertex D.affineRoots x)
    (y : D.ReducedBuilding)
    (hfix : ∀ g : rationalPoints G, g ∈ D.sharpFixer {x} → g • y = y) :
    y = D.apartmentMap x := by
  obtain ⟨b, rfl⟩ := D.exists_apartmentMap_eq_of_fixed_by_sharpFixer x y
    (hcommon (D.apartmentMap x) y) hfix
  exact congrArg D.apartmentMap (D.eq_of_vertex_of_fixed_by_sharpFixer hG hi hx hfix)

end KPApartmentData

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    (B : IntegerValuationBuildingData v G)

/-- Common apartments suffice for the singleton fixed-locus conclusion for
every actual vertex one-stabilizer. -/
theorem eq_of_vertex_of_fixed_by_oneStabilizer_of_commonApartments
    (hcommon : B.apartment.HasCommonApartments)
    {x : B.ReducedBuilding} (hx : B.IsVertex x) (y : B.ReducedBuilding)
    (hfix : ∀ h : rationalPoints G, h ∈ B.oneStabilizer x → h • y = y) : y = x := by
  obtain ⟨g, a, rfl, ha⟩ := hx
  have heq : g⁻¹ • y = B.apartmentMap a := by
    apply B.apartment.eq_of_vertex_of_fixed_by_sharpFixer_of_commonApartments
      B.isConnectedReductive B.isMaximalSplitTorus hcommon ha
    intro h hh
    have hhK := B.sharpFixer_le_oneStabilizer a hh
    have hhg := B.conj_mem_oneStabilizer g hhK
    have hy := congrArg (fun z : B.ReducedBuilding => g⁻¹ • z) (hfix _ hhg)
    simpa only [mul_smul, inv_smul_smul] using hy
  calc
    y = g • (g⁻¹ • y) := (smul_inv_smul g y).symm
    _ = g • B.apartmentMap a := by rw [heq]

end IntegerValuationBuildingData

/-- Common apartments imply singleton fixed loci for all actual vertex
one-stabilizers of integer-valued building data. -/
def VertexFixedLocusFromCommonApartmentsStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    (B : IntegerValuationBuildingData v G),
    B.apartment.HasCommonApartments →
    ∀ x : B.ReducedBuilding, B.IsVertex x →
      ∀ y : B.ReducedBuilding,
        (∀ g ∈ B.oneStabilizer x, g • y = y) → y = x

/-- The actual quotient transport and apartment rigidity prove the conditional
global fixed-locus statement. -/
theorem vertexFixedLocusFromCommonApartments :
    VertexFixedLocusFromCommonApartmentsStatement.{u} := by
  intro k _ G _ v B hcommon x hx y hfix
  exact B.eq_of_vertex_of_fixed_by_oneStabilizer_of_commonApartments hcommon hx y hfix

namespace MaximalUnramified

/-- The remaining common-apartment premise gives the full vertex fixed-locus
conclusion needed in the maximal-bounded argument. -/
theorem vertex_fixed_of_commonApartments
    (hcommon : CommonApartmentsStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (LocalGalois.Separable.inertiaFixedField F))))
    [IsAffineHom G.X.hom] (B : BuildingData F G)
    {x : B.ReducedBuilding} (hx : B.IsVertex x) (y : B.ReducedBuilding)
    (hfix : ∀ g : rationalPoints G, g ∈ B.oneStabilizer x → g • y = y) : y = x :=
  B.eq_of_vertex_of_fixed_by_oneStabilizer_of_commonApartments (hcommon F G B) hx y hfix

end MaximalUnramified
end Langlands.Geometry.Building
