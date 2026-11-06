import Langlands.Geometry.Building.RootFreeParahorics
import Langlands.Geometry.Building.ValuationBuildingAxioms
import Langlands.GroupScheme.Rational.AnisotropicRootSystem
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Actual quotient geometry without relative roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}

/-- Every rational point normalizes a split subtorus of an anisotropic group. -/
theorem IsAnisotropic.normalizerPoints_eq_top_of_isSplitSubtorus
    (hG : IsAnisotropic G) (hi : IsSplitSubtorus i) :
    normalizerPoints i = ⊤ := by
  apply top_unique
  rw [← hG.centralizerPoints_eq_top hi]
  exact centralizerPoints_le_normalizerPoints i

end Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Off-root normalization makes every valuation in a root-free apartment equal. -/
theorem subsingleton_apartment_of_relativeRoots_eq_empty
    (hΦ : relativeRoots i = ∅) : Subsingleton D.Apartment := by
  refine ⟨fun x y => Apartment.ext ?_⟩
  apply RootFunctionFamily.ext
  intro a g
  have ha : a ∉ relativeRoots i := by simp [hΦ]
  exact (x.isValuation.eq_top_of_not_mem_roots a ha g).trans
    (y.isValuation.eq_top_of_not_mem_roots a ha g).symm

/-- The full fixer of the canonical point is the actual normalizer. -/
theorem reducedFixer_apartmentMap_of_relativeRoots_eq_empty
    (hΦ : relativeRoots i = ∅) (x : D.Apartment) :
    D.reducedFixer (D.apartmentMap x) = normalizerPoints i := by
  have := D.subsingleton_apartment_of_relativeRoots_eq_empty hΦ
  have hstab : MulAction.stabilizer (normalizerPoints i) x = ⊤ := by
    apply top_unique
    intro n _
    exact MulAction.mem_stabilizer_iff.2 (Subsingleton.elim _ _)
  rw [D.reducedFixer_apartmentMap,
    D.sharpFixer_eq_bot_of_relativeRoots_eq_empty hΦ, hstab, bot_sup_eq,
    Subgroup.map_top, Subgroup.range_subtype]

/-- The actual root-free quotient is the coset space by the actual normalizer. -/
def quotientNormalizerEquivOfRelativeRootsEqEmpty
    (hΦ : relativeRoots i = ∅) (x : D.Apartment) :
    (rationalPoints G ⧸ normalizerPoints i) ≃ D.ReducedBuilding :=
  (Subgroup.quotientEquivOfEq
    (D.reducedFixer_apartmentMap_of_relativeRoots_eq_empty hΦ x).symm).trans
      (Equiv.ofBijective
        (MulAction.ofQuotientStabilizer (rationalPoints G) (D.apartmentMap x))
        ⟨MulAction.injective_ofQuotientStabilizer _ _, fun y => by
          have := D.subsingleton_apartment_of_relativeRoots_eq_empty hΦ
          obtain ⟨g, z, hgz⟩ := D.exists_smul_apartmentMap y
          refine ⟨QuotientGroup.mk g, ?_⟩
          change g • D.apartmentMap x = y
          simpa only [Subsingleton.elim z x] using hgz⟩)

@[simp]
theorem quotientNormalizerEquivOfRelativeRootsEqEmpty_mk
    (hΦ : relativeRoots i = ∅) (x : D.Apartment) (g : rationalPoints G) :
    D.quotientNormalizerEquivOfRelativeRootsEqEmpty hΦ x (QuotientGroup.mk g) =
      g • D.apartmentMap x :=
  rfl

/-- The quotient equivalence respects the original rational-point actions. -/
theorem quotientNormalizerEquivOfRelativeRootsEqEmpty_smul
    (hΦ : relativeRoots i = ∅) (x : D.Apartment) (g : rationalPoints G)
    (q : rationalPoints G ⧸ normalizerPoints i) :
    D.quotientNormalizerEquivOfRelativeRootsEqEmpty hΦ x (g • q) =
      g • D.quotientNormalizerEquivOfRelativeRootsEqEmpty hΦ x q := by
  induction q using Quotient.inductionOn' with
  | h h =>
    change (g * h) • D.apartmentMap x = g • (h • D.apartmentMap x)
    exact mul_smul g h _

/-- Each facet of the root-free apartment is its single point. -/
theorem facet_eq_singleton_of_relativeRoots_eq_empty
    (hΦ : relativeRoots i = ∅) (x : D.Apartment) :
    AffineRootSystem.facet D.affineRoots x = {x} := by
  have := D.subsingleton_apartment_of_relativeRoots_eq_empty hΦ
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro _
    exact Subsingleton.elim _ _
  · rintro rfl
    exact AffineRootSystem.mem_facet_self _ _

/-- An anisotropic group's actual reduced quotient has a single point. -/
theorem subsingleton_reducedBuilding_of_isAnisotropic
    (hG : IsAnisotropic G) (hi : IsSplitSubtorus i) :
    Subsingleton D.ReducedBuilding := by
  have hΦ := hG.relativeRoots_eq_empty hi
  have := D.subsingleton_apartment_of_relativeRoots_eq_empty hΦ
  obtain ⟨x⟩ := (inferInstance : Nonempty D.Apartment)
  have hfix : D.reducedFixer (D.apartmentMap x) = ⊤ := by
    rw [D.reducedFixer_apartmentMap_of_relativeRoots_eq_empty hΦ,
      hG.normalizerPoints_eq_top_of_isSplitSubtorus hi]
  have hall : ∀ y : D.ReducedBuilding, y = D.apartmentMap x := by
    intro y
    obtain ⟨g, z, rfl⟩ := D.exists_smul_apartmentMap y
    rw [Subsingleton.elim z x]
    exact D.mem_reducedFixer.1 (hfix ▸ Subgroup.mem_top g)
  exact ⟨fun y z => (hall y).trans (hall z).symm⟩

end KPApartmentData

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- The apartment image is a singleton when the actual relative roots are empty. -/
theorem apartmentImage_eq_singleton_of_relativeRoots_eq_empty
    (hΦ : relativeRoots B.i = ∅) (x : B.Apartment) :
    B.apartmentImage = {B.apartmentMap x} := by
  have := B.apartment.subsingleton_apartment_of_relativeRoots_eq_empty hΦ
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact Set.mem_singleton_iff.2
      (congrArg B.apartmentMap (Subsingleton.elim z x))
  · rintro rfl
    exact ⟨x, rfl⟩

/-- The stabilizer of the root-free apartment image is exactly the actual normalizer. -/
theorem hasNormalizerApartmentStabilizer_of_relativeRoots_eq_empty
    (hΦ : relativeRoots B.i = ∅) : B.HasNormalizerApartmentStabilizer := by
  obtain ⟨x⟩ := (inferInstance : Nonempty B.Apartment)
  rw [HasNormalizerApartmentStabilizer,
    B.apartmentImage_eq_singleton_of_relativeRoots_eq_empty hΦ x]
  have hstab : MulAction.stabilizer (rationalPoints G) ({B.apartmentMap x} :
      Set B.ReducedBuilding) = B.fixer (B.apartmentMap x) := by
    ext g
    simp only [MulAction.mem_stabilizer_iff, Set.smul_set_singleton,
      Set.singleton_eq_singleton_iff, mem_fixer]
  rw [hstab]
  exact B.apartment.reducedFixer_apartmentMap_of_relativeRoots_eq_empty hΦ x

/-- Root-free building facets are exactly the singleton subsets of the actual quotient. -/
theorem isFacet_iff_exists_singleton_of_relativeRoots_eq_empty
    (hΦ : relativeRoots B.i = ∅) (Y : Set B.ReducedBuilding) :
    B.IsFacet Y ↔ ∃ y : B.ReducedBuilding, Y = {y} := by
  constructor
  · rintro ⟨g, Fa, ⟨x, rfl⟩, rfl⟩
    refine ⟨g • B.apartmentMap x, ?_⟩
    rw [B.apartment.facet_eq_singleton_of_relativeRoots_eq_empty hΦ,
      Set.image_singleton]
  · rintro ⟨y, rfl⟩
    obtain ⟨g, x, rfl⟩ := B.exists_smul_apartmentMap y
    exact ⟨g, {x},
      ⟨x, B.apartment.facet_eq_singleton_of_relativeRoots_eq_empty hΦ x⟩,
      by simp only [Set.image_singleton]⟩

/-- AS 6 holds for the actual root-free quotient, without a quotient-singleton premise. -/
theorem hasCompatibleApartmentFacets_of_relativeRoots_eq_empty
    (hΦ : relativeRoots B.i = ∅) : B.HasCompatibleApartmentFacets := by
  have := B.apartment.subsingleton_apartment_of_relativeRoots_eq_empty hΦ
  refine ⟨fun _ _ _ => Subsingleton.elim _ _, ?_⟩
  intro Y hY hmeet
  obtain ⟨y, rfl⟩ :=
    (B.isFacet_iff_exists_singleton_of_relativeRoots_eq_empty hΦ Y).1 hY
  obtain ⟨z, hz, hzA⟩ := hmeet
  have hzy : z = y := Set.mem_singleton_iff.1 hz
  subst z
  obtain ⟨x, hx⟩ := hzA
  refine ⟨{x},
    ⟨x, B.apartment.facet_eq_singleton_of_relativeRoots_eq_empty hΦ x⟩, ?_⟩
  rw [Set.image_singleton, hx]

end ValuationBuildingData

end Langlands.Geometry.Building
