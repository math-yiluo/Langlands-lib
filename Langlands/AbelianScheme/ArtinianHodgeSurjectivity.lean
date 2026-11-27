import Langlands.AbelianScheme.ArtinianHodgeFormParity
import Langlands.AbelianScheme.ArtinianHodgeFunctionFree

/-! # Lifting first function cohomology classes to de Rham cohomology -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.Scheme Langlands.Algebra
open Langlands.AlgebraicGeometry.AffineCechDeRham
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
  (inter unitCohomologyPullback_id)

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R] [Algebra ℚ R]
  (B : AbelianScheme (Spec (CommRingCat.of R))) (U : Scheme.AffineOpenCover.{u} B.X.left)
  [Finite U.I₀]

section InversionCover

variable (β : U.I₀ → U.I₀) (hβ : ∀ i, coverOpens U i ≤ ι[B.X].left ⁻¹ᵁ coverOpens U (β i))
  (hInv : Function.Involutive β) {κ : Type u} [Fintype κ] [LinearOrder κ]
  (E : SheafOfModules.free (R := B.X.left.ringCatSheaf) κ ≅ relativeDifferentials B.X.hom)

include hInv E in
private lemma exists_closed_form_primitive (a : structureCocycles B.X.hom U)
    (ha : functionInversion B U β hβ 1 a.val = -a.val) :
    ∃ b : Cochains U (oneForms B.X.hom) 0,
      cechD U (oneForms B.X.hom) 0 b = cochainMap U (exteriorD0 B.X.hom) 1 a.val ∧
      cochainMap U (exteriorD1 B.X.hom) 0 b = 0 := by
  let da := cochainMap U (exteriorD0 B.X.hom) 1 a.val
  have hda : oneFormInversion B U β hβ 1 da = -da := by
    change oneFormInversion B U β hβ 1 (cochainMap U (exteriorD0 B.X.hom) 1 a.val) = -da
    rw [pullOneForms_exteriorD0, ha, map_neg]
  have hδ : cechD U (oneForms B.X.hom) 1 da = 0 := by
    change cechD U (oneForms B.X.hom) 1 (cochainMap U (exteriorD0 B.X.hom) 1 a.val) = 0
    rw [cechD_cochainMap, a.property, map_zero]
  let c := oneCochainCoordinates B.X.hom U E 1 da
  have hex (i : κ) : ∃ w : C0 B.X.hom U, cechD U (functions B.X.hom) 0 w = c i := by
    have h := oneCochainCoordinates_inversion B U β hβ E 1 da i
    rw [hda, map_neg, Pi.neg_apply] at h
    have he : functionInversion B U β hβ 1 (c i) = c i := (neg_injective h).symm
    let z : signedFunctions B U β hβ 1 1 := ⟨c i, mem_involutionPart.mpr (by rw [he, one_smul])⟩
    have hz : signedFunctionD B U β hβ 1 1 z = 0 := by
      apply Subtype.ext
      change cechD U (functions B.X.hom) 1 (c i) = 0
      change cechD U (functions B.X.hom) 1 (oneCochainCoordinates B.X.hom U E 1 da i) = 0
      rw [← oneCochainCoordinates_cechD, hδ, map_zero]
      rfl
    obtain ⟨w, hw⟩ := (signedFunction_even_exact_artinian B U β hβ hInv z).mp hz
    exact ⟨w.val, congrArg Subtype.val hw⟩
  choose w hw using hex
  let b₀ := (oneCochainCoordinates B.X.hom U E 0).symm w
  have hb₀ : cechD U (oneForms B.X.hom) 0 b₀ = da := by
    apply (oneCochainCoordinates B.X.hom U E 1).injective
    funext i
    rw [oneCochainCoordinates_cechD,
      show oneCochainCoordinates B.X.hom U E 0 b₀ = w from LinearEquiv.apply_symm_apply _ _]
    exact hw i
  let T := oneFormInversion B U β hβ 0
  let b := half R • (b₀ - T b₀)
  have hb : oneFormInversion B U β hβ 0 b = -b := by
    change T (half R • (b₀ - T b₀)) = -(half R • (b₀ - T b₀))
    rw [map_smul, map_sub, oneFormInversion_involutive B U β hβ E hInv 0 b₀,
      ← smul_neg, neg_sub]
  have hc : cechD U (oneForms B.X.hom) 0 b = da := by
    change cechD U (oneForms B.X.hom) 0 (half R • (b₀ - T b₀)) = da
    rw [map_smul, map_sub, show cechD U (oneForms B.X.hom) 0 (T b₀) =
      oneFormInversion B U β hβ 1 (cechD U (oneForms B.X.hom) 0 b₀) from
        cechD_pullOneForms ι[B.X].left (Over.w ι[B.X]) β hβ 0 b₀, hb₀, hda,
      sub_neg_eq_add, smul_add]
    exact half_smul_add_half_smul (R := R) da
  refine ⟨b, hc, exteriorD1_eq_zero_of_odd_of_cechD_zero B U β hβ E b hb ?_⟩
  rw [cechD_cochainMap, hc]
  funext σ
  exact RelativeForms.dOne_dZero (R := R) (A := sectionRing B.X.hom (inter (coverOpens U) σ)) (a.val σ)

end InversionCover

/-- Every first function class on the supplied cover lifts to a degree-one
relative de Rham class. -/
theorem toStructureH1_surjective_artinian : Function.Surjective (toStructureH1 B.X.hom U) := by
  intro z
  obtain ⟨κ, hκ, ⟨E⟩⟩ := exists_finiteFreeRelativeDifferentials B
  let := Fintype.ofFinite κ
  let e := Fintype.equivFin κ
  let : LinearOrder κ := LinearOrder.lift' e e.injective
  let V := inversionCover B U
  let β := swapChart U ι[B.X].left
  let hβ := doubledCover_le_preimage U ι[B.X].left (inversion_left_sq B)
  let hInv : Function.Involutive β := swapChart_swapChart U ι[B.X].left
  let zv := (structureH1Equiv B.X.hom V).symm (structureH1Equiv B.X.hom U z)
  obtain ⟨a, ha, hclass⟩ := exists_odd_function_cocycle B V β hβ hInv zv
  obtain ⟨b, hb, hd⟩ := exists_closed_form_primitive B V β hβ hInv E a ha
  let α := inversionOriginalChart B U
  let hα := inversionOriginalChart_le B U
  let a' := pullFunctionCocycles (𝟙 B.X) V U α hα 0 a
  let b' := pullOneForms (𝟙 B.X.left) (Category.id_comp B.X.hom) α hα 0 b
  have h₁ : cechD U (oneForms B.X.hom) 0 b' = cochainMap U (exteriorD0 B.X.hom) 1 a'.val := by
    change cechD U (oneForms B.X.hom) 0
        (pullOneForms (𝟙 B.X.left) (Category.id_comp B.X.hom) α hα 0 b) =
      cochainMap U (exteriorD0 B.X.hom) 1
        (pullFunctions (𝟙 B.X.left) (Category.id_comp B.X.hom) α hα 1 a.val)
    rw [cechD_pullOneForms, hb, pullOneForms_exteriorD0]
  have h₂ : cochainMap U (exteriorD1 B.X.hom) 0 b' = 0 := by
    change cochainMap U (exteriorD1 B.X.hom) 0
      (pullOneForms (𝟙 B.X.left) (Category.id_comp B.X.hom) α hα 0 b) = 0
    rw [← pullTwoForms_exteriorD1, hd, map_zero]
  let x : cocycles B.X.hom U := ⟨(a'.val, b'), by
    change D1 B.X.hom U (a'.val, b') = 0
    rw [D1_apply, a'.property, h₁, sub_self, h₂]
    rfl⟩
  refine ⟨(boundaries B.X.hom U).mkQ x, ?_⟩
  rw [toStructureH1_class]
  change (structureBoundaries B.X.hom U).mkQ a' = z
  apply (structureH1Equiv B.X.hom U).injective
  rw [structureH1Equiv_mkQ]
  change functionCocycleClass B.X.hom U 0 (pullFunctionCocycles (𝟙 B.X) V U α hα 0 a) = _
  rw [functionCocycleClass_pull, unitCohomologyPullback_id, LinearMap.id_apply,
    ← structureH1Equiv_mkQ, hclass]
  exact (structureH1Equiv B.X.hom V).apply_symm_apply _

end Langlands.AbelianScheme
