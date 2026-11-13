import Langlands.Geometry.Building.ApartmentQuotientComparison
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData

/-! # Common apartments for the actual integer-valued quotient -/

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

/-- Every two points of the existing quotient belong to one translated
apartment. This is an explicit geometric premise. -/
def HasCommonApartments : Prop :=
  ApartmentQuotient.HasCommonTranslatedApartment D.sharpFixerFamily

/-- If a point shares an apartment with the base point and is fixed by its
sharp fixer, it is in the base apartment. -/
theorem exists_apartmentMap_eq_of_fixed_by_sharpFixer
    (x : D.Apartment) (y : D.ReducedBuilding)
    (hcommon : ∃ (g : rationalPoints G) (a b : D.Apartment),
      g • D.apartmentMap a = D.apartmentMap x ∧ g • D.apartmentMap b = y)
    (hfix : ∀ g : rationalPoints G, g ∈ D.sharpFixer {x} → g • y = y) :
    ∃ b : D.Apartment, D.apartmentMap b = y := by
  obtain ⟨g, a, b, ha, hb⟩ := hcommon
  have heq :
      ApartmentQuotient.mk D.sharpFixerFamily (1, x) =
        ApartmentQuotient.mk D.sharpFixerFamily (g, a) := by
    have ha' := ha.symm
    change ApartmentQuotient.mk D.sharpFixerFamily (1, x) =
      ApartmentQuotient.mk D.sharpFixerFamily (g * 1, a) at ha'
    simpa only [mul_one] using ha'
  obtain ⟨n, -, hn⟩ :=
    (ApartmentQuotient.mk_eq_mk_iff D.sharpFixerFamily 1 g x a).mp heq
  have hp : g * (n : rationalPoints G) ∈ D.sharpFixer {x} := by
    change 1⁻¹ * g * (n : rationalPoints G) ∈ D.sharpFixer {x} at hn
    simpa only [inv_one, one_mul] using hn
  refine ⟨n⁻¹ • b, ?_⟩
  calc
    D.apartmentMap (n⁻¹ • b) =
        (g * (n : rationalPoints G))⁻¹ • (g • D.apartmentMap b) := by
      rw [D.apartmentMap_smul]
      simp only [mul_inv_rev, mul_smul, inv_smul_smul, Subgroup.coe_inv]
    _ = y := by rw [hb]; exact hfix _ (inv_mem hp)

end KPApartmentData

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    (B : IntegerValuationBuildingData v G)

/-- Conjugation carries the actual one-stabilizer into the one-stabilizer
of the translated point. -/
theorem conj_mem_oneStabilizer (g : rationalPoints G)
    {y : B.ReducedBuilding} {h : rationalPoints G} (hh : h ∈ B.oneStabilizer y) :
    g * h * g⁻¹ ∈ B.oneStabilizer (g • y) := by
  obtain ⟨hhK, hhfix⟩ := B.mem_oneStabilizer.mp hh
  refine B.mem_oneStabilizer.mpr ⟨Subgroup.Normal.conj_mem
    (inferInstance : (characterValuationKernel v G).Normal) h hhK g, ?_⟩
  simp only [mul_smul, inv_smul_smul, hhfix]

end IntegerValuationBuildingData

namespace MaximalUnramified

/-- The common-apartment obligation for the actual integer-valued building
over the maximal unramified extension. It is not supplied by the data. -/
def CommonApartmentsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (LocalGalois.Separable.inertiaFixedField F))))
    [IsAffineHom G.X.hom] (B : BuildingData F G),
    B.apartment.HasCommonApartments

end MaximalUnramified
end Langlands.Geometry.Building
