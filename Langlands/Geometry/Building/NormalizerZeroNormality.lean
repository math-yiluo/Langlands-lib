import Langlands.Geometry.Building.IwahoriWeylExactSequenceReduction
import Langlands.Geometry.Building.NormalizerApartmentActionKernel

/-! # Full-normalizer normality from the actual apartment action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- Every centralizer-zero normalizer point acts trivially on the apartment. -/
theorem normalizerZero_le_ker_normalizerAffineEquiv :
    P.normalizerZero ≤ P.apartment.normalizerAffineEquiv.ker :=
  fun _ hn => P.normalizerAffineEquiv_eq_one_of_mem_normalizerZero hn

/-- The exact kernel inside the zero-component normalizer, viewed as an
intersection in the full normalizer. -/
theorem normalizerZero_eq_normalizerZeroComponent_inf_ker
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement) :
    P.normalizerZero =
      P.normalizerZeroComponent ⊓ P.apartment.normalizerAffineEquiv.ker := by
  ext n
  constructor
  · intro hn
    exact ⟨P.normalizerZero_le_normalizerZeroComponent hn,
      P.normalizerZero_le_ker_normalizerAffineEquiv hn⟩
  · rintro ⟨hn, hk⟩
    exact (P.normalizerAffineEquiv_eq_one_iff_of_mem_normalizerZeroComponent
      hZ n hn).mp hk

/-- Under the cover comparison, normality of the ambient zero subgroup gives
normality of the original centralizer-zero subgroup in the full normalizer. -/
theorem normalizerZero_normal_of_zeroSubgroup_normal
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    [P.zeroSubgroup.Normal] : P.normalizerZero.Normal := by
  rw [P.normalizerZero_eq_normalizerZeroComponent_inf_ker hZ]
  change (P.zeroSubgroup.subgroupOf (normalizerPoints P.i) ⊓
    P.apartment.normalizerAffineEquiv.ker).Normal
  infer_instance

/-- The actual apartment action descends to the original Iwahori–Weyl quotient
whenever that quotient has its group structure. -/
def iwahoriWeylApartmentAction [P.normalizerZero.Normal] :
    P.IwahoriWeylGroup →* (P.Apartment ≃ᵃ[ℝ] P.Apartment) :=
  QuotientGroup.lift P.normalizerZero P.apartment.normalizerAffineEquiv
    P.normalizerZero_le_ker_normalizerAffineEquiv

@[simp]
theorem iwahoriWeylApartmentAction_mk [P.normalizerZero.Normal]
    (n : normalizerPoints P.i) :
    P.iwahoriWeylApartmentAction (QuotientGroup.mk n) =
      P.apartment.normalizerAffineEquiv n :=
  rfl

/-- The descended actual action restricted to the original affine part. -/
def affinePartApartmentAction [P.normalizerZero.Normal] :
    P.affinePart →* (P.Apartment ≃ᵃ[ℝ] P.Apartment) :=
  P.iwahoriWeylApartmentAction.comp P.affinePart.subtype

@[simp]
theorem affinePartApartmentAction_mk [P.normalizerZero.Normal]
    (n : P.normalizerZeroComponent) :
    P.affinePartApartmentAction (P.affinePartMk n) =
      P.apartment.normalizerAffineEquiv (n : normalizerPoints P.i) :=
  rfl

/-- The exact restricted kernel makes the descended action faithful on the
original affine part. -/
theorem affinePartApartmentAction_injective [P.normalizerZero.Normal]
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement) :
    Function.Injective P.affinePartApartmentAction := by
  apply (injective_iff_map_eq_one P.affinePartApartmentAction).mpr
  intro w hw
  obtain ⟨n, hn, heq⟩ := w.property
  have hact : P.apartment.normalizerAffineEquiv n = 1 := by
    change P.iwahoriWeylApartmentAction (w : P.IwahoriWeylGroup) = 1 at hw
    rw [← heq] at hw
    exact hw
  have hnz := (P.normalizerAffineEquiv_eq_one_iff_of_mem_normalizerZeroComponent
    hZ n hn).mp hact
  apply Subtype.ext
  change (w : P.IwahoriWeylGroup) = 1
  rw [← heq]
  exact (QuotientGroup.eq_one_iff n).mpr hnz

end Langlands.Geometry.Building.ParahoricBuildingData
