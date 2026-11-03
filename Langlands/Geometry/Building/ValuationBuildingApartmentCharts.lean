import Langlands.Geometry.Building.ValuationBuildingAxioms
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Charts of the translated apartments

These constructions concern one supplied `ValuationBuildingData`. They do not identify
normalizer cosets with actual maximal split subtori, or prove the general existence of
building data. The affine chart transitions use the existing normalizer action.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- The chart of the translated apartment `g · A(S)` in the actual reduced building. -/
def translatedApartmentMap (g : rationalPoints G) (x : B.Apartment) :
    B.ReducedBuilding :=
  g • B.apartmentMap x

@[simp] theorem translatedApartmentMap_one (x : B.Apartment) :
    B.translatedApartmentMap 1 x = B.apartmentMap x :=
  one_smul _ _

theorem translatedApartmentMap_mul (g h : rationalPoints G) (x : B.Apartment) :
    B.translatedApartmentMap (g * h) x = g • B.translatedApartmentMap h x :=
  mul_smul _ _ _

theorem range_translatedApartmentMap (g : rationalPoints G) :
    Set.range (B.translatedApartmentMap g) = g • B.apartmentImage := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact Set.smul_mem_smul_set ⟨x, rfl⟩
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

theorem translatedApartmentMap_injective
    (hB : Function.Injective B.apartmentMap) (g : rationalPoints G) :
    Function.Injective (B.translatedApartmentMap g) := by
  intro x y hxy
  exact hB ((MulAction.injective g) hxy)

/-- Each translated chart parametrizes exactly its apartment, assuming the base chart
is injective. This is an equivalence of types; no affine structure on the subtype is
asserted here. -/
def translatedApartmentChart (hB : Function.Injective B.apartmentMap)
    (g : rationalPoints G) : B.Apartment ≃ (g • B.apartmentImage : Set B.ReducedBuilding) :=
  Equiv.ofBijective
    (fun x => ⟨B.translatedApartmentMap g x,
      (B.range_translatedApartmentMap g).le ⟨x, rfl⟩⟩)
    ⟨fun x y hxy => B.translatedApartmentMap_injective hB g (congrArg Subtype.val hxy),
      fun ⟨y, hy⟩ => by
        obtain ⟨x, hx⟩ := (B.range_translatedApartmentMap g).ge hy
        exact ⟨x, Subtype.ext hx⟩⟩

@[simp] theorem translatedApartmentChart_apply
    (hB : Function.Injective B.apartmentMap) (g : rationalPoints G) (x : B.Apartment) :
    (B.translatedApartmentChart hB g x : B.ReducedBuilding) =
      B.translatedApartmentMap g x :=
  rfl

/-- Two translated apartment images agree exactly when the corresponding representatives
are in the same left coset of the actual normalizer. -/
theorem smul_apartmentImage_eq_iff (hN : B.HasNormalizerApartmentStabilizer)
    (g h : rationalPoints G) :
    g • B.apartmentImage = h • B.apartmentImage ↔
      h⁻¹ * g ∈ normalizerPoints B.i := by
  rw [← hN.smul_apartmentImage_eq_iff]
  constructor
  · intro heq
    rw [mul_smul, heq, inv_smul_smul]
  · intro heq
    have := congrArg (h • ·) heq
    simpa only [mul_smul, smul_inv_smul] using this

/-- Actual normalizer cosets index exactly the translated apartment subsets.
This uses the specified apartment stabilizer and does not identify the cosets
with actual maximal split subtori. -/
def normalizerCosetApartmentEquiv (hN : B.HasNormalizerApartmentStabilizer) :
    (rationalPoints G ⧸ normalizerPoints B.i) ≃
      {Y : Set B.ReducedBuilding // B.IsApartment Y} :=
  ((Subgroup.quotientEquivOfEq hN.symm).trans
    (MulAction.orbitEquivQuotientStabilizer
      (rationalPoints G) B.apartmentImage).symm).trans
    { toFun := fun Y => ⟨Y, by
        obtain ⟨g, hg⟩ := Y.property
        exact ⟨g, hg.symm⟩⟩
      invFun := fun Y => ⟨Y, by
        obtain ⟨g, hg⟩ := Y.property
        exact ⟨g, hg.symm⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[simp] theorem normalizerCosetApartmentEquiv_mk
    (hN : B.HasNormalizerApartmentStabilizer) (g : rationalPoints G) :
    (B.normalizerCosetApartmentEquiv hN
      (QuotientGroup.mk g) : Set B.ReducedBuilding) = g • B.apartmentImage :=
  rfl

theorem normalizerCosetApartmentEquiv_smul
    (hN : B.HasNormalizerApartmentStabilizer) (g : rationalPoints G)
    (q : rationalPoints G ⧸ normalizerPoints B.i) :
    (B.normalizerCosetApartmentEquiv hN (g • q) : Set B.ReducedBuilding) =
      g • (B.normalizerCosetApartmentEquiv hN q : Set B.ReducedBuilding) := by
  refine Quotient.inductionOn' q ?_
  intro h
  change (g * h) • B.apartmentImage = g • h • B.apartmentImage
  exact mul_smul _ _ _

/-- The affine transition from the chart labelled `g` to that labelled `h`.
Its input records the exact normalizer-coset condition. -/
def apartmentChartTransition (g h : rationalPoints G)
    (hgh : h⁻¹ * g ∈ normalizerPoints B.i) : B.Apartment ≃ᵃ[ℝ] B.Apartment :=
  B.normalizerAction ⟨h⁻¹ * g, hgh⟩

theorem translatedApartmentMap_transition (g h : rationalPoints G)
    (hgh : h⁻¹ * g ∈ normalizerPoints B.i) (x : B.Apartment) :
    B.translatedApartmentMap h (B.apartmentChartTransition g h hgh x) =
      B.translatedApartmentMap g x := by
  change h • B.apartmentMap ((⟨h⁻¹ * g, hgh⟩ : normalizerPoints B.i) • x) =
    g • B.apartmentMap x
  rw [← B.normalizer_smul_apartmentMap, ← mul_smul, mul_inv_cancel_left]

/-- The transition's linear part is the actual normalizer action on the root-kernel
quotient of real cocharacters. -/
theorem apartmentChartTransition_linear (g h : rationalPoints G)
    (hgh : h⁻¹ * g ∈ normalizerPoints B.i) :
    (B.apartmentChartTransition g h hgh).linear =
      translationAction B.i ⟨h⁻¹ * g, hgh⟩ :=
  rfl

theorem apartmentChartTransition_self (g : rationalPoints G)
    (hgg : g⁻¹ * g ∈ normalizerPoints B.i) :
    B.apartmentChartTransition g g hgg = 1 := by
  change B.normalizerAction ⟨g⁻¹ * g, hgg⟩ = 1
  have heq : (⟨g⁻¹ * g, hgg⟩ : normalizerPoints B.i) = 1 :=
    Subtype.ext (inv_mul_cancel g)
  rw [heq, map_one]

/-- Successive chart transitions compose in the order of the coordinate changes. -/
theorem apartmentChartTransition_trans (g h k : rationalPoints G)
    (hgh : h⁻¹ * g ∈ normalizerPoints B.i)
    (hhk : k⁻¹ * h ∈ normalizerPoints B.i)
    (hgk : k⁻¹ * g ∈ normalizerPoints B.i) :
    (B.apartmentChartTransition g h hgh).trans
        (B.apartmentChartTransition h k hhk) =
      B.apartmentChartTransition g k hgk := by
  change B.normalizerAction ⟨k⁻¹ * h, hhk⟩ *
      B.normalizerAction ⟨h⁻¹ * g, hgh⟩ =
    B.normalizerAction ⟨k⁻¹ * g, hgk⟩
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  change (k⁻¹ * h) * (h⁻¹ * g) = k⁻¹ * g
  simp only [mul_assoc, mul_inv_cancel_left]

end Langlands.Geometry.Building.ValuationBuildingData
