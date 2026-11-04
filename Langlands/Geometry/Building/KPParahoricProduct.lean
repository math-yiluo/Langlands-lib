import Langlands.Geometry.Building.KPParahoric
import Langlands.Geometry.Building.KPZeroNormKernel
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The actual centralizer-sharp product in a parahoric
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

namespace ValuationBuildingData

variable (B : ValuationBuildingData G)

/-- The actual norm-one centralizer normalizes every sharp fixer. -/
theorem map_normKernel_le_normalizer_sharpFixer (Ω : Set B.Apartment) :
    (rationalCommonNormKernel B.centralizer.Z).map (rationalPoints.map B.centralizer.j) ≤
      Subgroup.normalizer (B.sharpFixer Ω : Set (rationalPoints G)) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro z hz g hg
  obtain ⟨z, hz, rfl⟩ := hz
  have hΩ : B.centralizer.toNormalizer z • Ω = Ω := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change B.centralizer.toNormalizer z • y ∈ Ω
      rwa [B.isOmegaCompatible.smul_eq_self hz y]
    · intro hx
      exact ⟨x, hx, B.isOmegaCompatible.smul_eq_self hz x⟩
  have h := B.apartment.sharpFixer_le_comap (B.centralizer.toNormalizer z) Ω hg
  rw [hΩ] at h
  exact h

end ValuationBuildingData

namespace ParahoricBuildingData

variable (P : ParahoricBuildingData G)

/-- The full supplied centralizer-zero factor normalizes the actual sharp fixer. -/
theorem map_centralizerZero_le_normalizer_sharpFixer (Ω : Set P.Apartment) :
    P.centralizerZero.map (rationalPoints.map P.centralizer.j) ≤
      Subgroup.normalizer (P.sharpFixer Ω : Set (rationalPoints G)) :=
  (Subgroup.map_mono P.zeroDatum.centralizerZero_le_rationalCommonNormKernel).trans
    (P.toValuationBuildingData.map_normKernel_le_normalizer_sharpFixer Ω)

/-- The actual join defining a full parahoric is its centralizer-sharp set product. -/
theorem coe_parahoric_eq_mul (Ω : Set P.Apartment) :
    (P.parahoric Ω : Set (rationalPoints G)) =
      (P.centralizerZero.map (rationalPoints.map P.centralizer.j) : Set (rationalPoints G)) *
        (P.sharpFixer Ω : Set (rationalPoints G)) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (P.map_centralizerZero_le_normalizer_sharpFixer Ω)

/-- The factors can also be placed in the opposite order. -/
theorem coe_parahoric_eq_mul_reverse (Ω : Set P.Apartment) :
    (P.parahoric Ω : Set (rationalPoints G)) =
      (P.sharpFixer Ω : Set (rationalPoints G)) *
        (P.centralizerZero.map (rationalPoints.map P.centralizer.j) : Set (rationalPoints G)) := by
  rw [P.coe_parahoric_eq_mul Ω]
  exact Subgroup.set_mul_normalizer_comm _ _
    (P.map_centralizerZero_le_normalizer_sharpFixer Ω)

/-- Every full-parahoric element is the product of an actual centralizer-zero element
and an actual sharp-fixer element. -/
theorem mem_parahoric_iff {Ω : Set P.Apartment} {g : rationalPoints G} :
    g ∈ P.parahoric Ω ↔
      ∃ z ∈ P.centralizerZero, ∃ h ∈ P.sharpFixer Ω,
        rationalPoints.map P.centralizer.j z * h = g := by
  change g ∈ (P.parahoric Ω : Set (rationalPoints G)) ↔ _
  rw [P.coe_parahoric_eq_mul Ω]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, h, hh, rfl⟩
    exact ⟨z, hz, h, hh, rfl⟩
  · rintro ⟨z, hz, h, hh, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, h, hh, rfl⟩

/-- Multiplication of the two actual factors, with codomain the full parahoric. -/
def parahoricProductMap (Ω : Set P.Apartment) :
    P.centralizerZero × P.sharpFixer Ω → P.parahoric Ω :=
  fun zh => ⟨rationalPoints.map P.centralizer.j zh.1 * zh.2,
    (P.parahoric Ω).mul_mem
      (P.map_centralizerZero_le_parahoric Ω ⟨zh.1, zh.1.property, rfl⟩)
      (P.sharpFixer_le_parahoric Ω zh.2.property)⟩

@[simp] theorem parahoricProductMap_coe (Ω : Set P.Apartment)
    (z : P.centralizerZero) (h : P.sharpFixer Ω) :
    (P.parahoricProductMap Ω (z, h) : rationalPoints G) =
      rationalPoints.map P.centralizer.j z * h := rfl

/-- The product map onto the full parahoric is surjective. -/
theorem parahoricProductMap_surjective (Ω : Set P.Apartment) :
    Function.Surjective (P.parahoricProductMap Ω) := by
  intro g
  obtain ⟨z, hz, h, hh, heq⟩ := P.mem_parahoric_iff.mp g.property
  exact ⟨(⟨z, hz⟩, ⟨h, hh⟩), Subtype.ext heq⟩

/-- The actual sharp fixer is normal inside the full parahoric. -/
theorem sharpFixer_normal_subgroupOf_parahoric (Ω : Set P.Apartment) :
    ((P.sharpFixer Ω).subgroupOf (P.parahoric Ω)).Normal :=
  Subgroup.normal_subgroupOf_sup_of_le_normalizer
    (P.map_centralizerZero_le_normalizer_sharpFixer Ω)

end ParahoricBuildingData

end Langlands.Geometry.Building
