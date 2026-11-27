import Langlands.AbelianScheme.ArtinianHodgeInversionCover

/-! # Actual cohomology classes of fixed-cover function cocycles -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

open DerivedSections CechResolution.AllSeq

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (U : Scheme.AffineOpenCover.{u} X)
  [IsSeparated f] [Finite U.I₀]

/-- The actual structure-sheaf cohomology class of a function cocycle on the supplied cover. -/
def functionCocycleClass (n : ℕ) : (cechD U (functions f) (n + 1)).ker →ₗ[R]
    (relativeCohomology f (n + 1)).obj (unitModule X) := by
  letI := Fintype.ofFinite U.I₀
  exact (canonicalClass f (coverOpens U) U.openCover.iSup_opensRange
    (fun i => isAffineOpen_opensRange (U.f i)) n).comp (structureCocycleEquiv f U n).toLinearMap

lemma functionCocycleClass_eq_zero_iff (n : ℕ) (z : (cechD U (functions f) (n + 1)).ker) :
    functionCocycleClass f U n z = 0 ↔ ∃ w, cechD U (functions f) n w = z.val := by
  let := Fintype.ofFinite U.I₀
  unfold functionCocycleClass
  rw [LinearMap.comp_apply, canonicalClass_eq_zero_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨(structureCochainEquiv f U n).symm w, ?_⟩
    apply (structureCochainEquiv f U (n + 1)).injective
    rw [structureCochainEquiv_cechD, LinearEquiv.apply_symm_apply]
    exact hw
  · rintro ⟨w, hw⟩
    refine ⟨structureCochainEquiv f U n w, ?_⟩
    rw [← structureCochainEquiv_cechD, hw]
    rfl

@[simp]
lemma structureH1Equiv_mkQ (z : structureCocycles f U) :
    structureH1Equiv f U ((structureBoundaries f U).mkQ z) = functionCocycleClass f U 0 z := by
  unfold structureH1Equiv functionCocycleClass
  simp only [LinearEquiv.trans_apply]
  rfl

section Pullback

variable {P Q : Over (Spec (CommRingCat.of R))} (a : P ⟶ Q)
  (V : Scheme.AffineOpenCover.{u} Q.left) (W : Scheme.AffineOpenCover.{u} P.left)
  [IsSeparated P.hom] [IsSeparated Q.hom] [Finite V.I₀] [Finite W.I₀]
  (β : W.I₀ → V.I₀) (hβ : ∀ i, coverOpens W i ≤ a.left ⁻¹ᵁ coverOpens V (β i))

/-- Pullback of function cochains restricts to cocycles in every positive degree. -/
def pullFunctionCocycles (n : ℕ) : (cechD V (functions Q.hom) (n + 1)).ker →ₗ[R]
    (cechD W (functions P.hom) (n + 1)).ker :=
  ((pullFunctions a.left (Over.w a) β hβ (n + 1)).comp
    (cechD V (functions Q.hom) (n + 1)).ker.subtype).codRestrict _ fun z => by
      change cechD W (functions P.hom) (n + 1)
        (pullFunctions a.left (Over.w a) β hβ (n + 1) z.val) = 0
      rw [cechD_pullFunctions, z.property, map_zero]

/-- The actual pullback in structure-sheaf cohomology carries the class of a
function cocycle to the class of its Čech pullback. -/
lemma functionCocycleClass_pull (n : ℕ) (z : (cechD V (functions Q.hom) (n + 1)).ker) :
    functionCocycleClass P.hom W n (pullFunctionCocycles a V W β hβ n z) =
      unitCohomologyPullbackLinear a (n + 1) (functionCocycleClass Q.hom V n z) := by
  let := Fintype.ofFinite V.I₀
  let := Fintype.ofFinite W.I₀
  have h := pull_canonicalClass a (coverOpens V) (coverOpens W) β hβ
    V.openCover.iSup_opensRange W.openCover.iSup_opensRange
    (fun i => isAffineOpen_opensRange (V.f i)) (fun i => isAffineOpen_opensRange (W.f i))
    n (structureCocycleEquiv Q.hom V n z)
  refine Eq.trans (congrArg (canonicalClass P.hom (coverOpens W) W.openCover.iSup_opensRange
    (fun i => isAffineOpen_opensRange (W.f i)) n) ?_) h.symm
  apply Subtype.ext
  exact (unitCochainMap_eq_pull a (coverOpens V) (coverOpens W) β hβ (n + 1)
    (structureCocycleEquiv Q.hom V n z)).symm

end Pullback

end Langlands.AlgebraicGeometry.AffineCechDeRham
