import Langlands.AbelianScheme.ArtinianHodgeFormParity

/-! # Closed forms on an Artinian abelian scheme -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.Scheme
open Langlands.AlgebraicGeometry.AffineCechDeRham
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter)

variable {R : Type u} [CommRing R] (B : AbelianScheme (Spec (CommRingCat.of R)))
  (U : Scheme.AffineOpenCover.{u} B.X.left) {κ : Type u} [Fintype κ]
  (E : SheafOfModules.free (R := B.X.left.ringCatSheaf) κ ≅ relativeDifferentials B.X.hom)

private def scalarFunction : R →ₗ[R] C0 B.X.hom U :=
  LinearMap.pi fun σ => Algebra.linearMap R (sectionRing B.X.hom (inter (coverOpens U) σ))

private lemma cechD_scalarFunction (r : R) : cechD U (functions B.X.hom) 0 (scalarFunction B U r) = 0 := by
  let s := algebraMap R (sectionRing B.X.hom ⊤) r
  have h : globalCochain U (functions B.X.hom) s = scalarFunction B U r := by
    funext σ
    let hV : inter (coverOpens U) σ ≤ ⊤ := le_top
    exact ((sectionAlgebras B.X.hom).map (homOfLE hV).op).hom.commutes r
  rw [← h]
  exact cechD_globalCochain U (functions B.X.hom) s

private def scalarForms : (κ → R) →ₗ[R] Cochains U (oneForms B.X.hom) 0 :=
  (oneCochainCoordinates B.X.hom U E 0).symm.toLinearMap.comp
    (LinearMap.pi fun i => (scalarFunction B U).comp (LinearMap.proj i))

private lemma scalarForms_coordinates (r : κ → R) (i : κ) :
    oneCochainCoordinates B.X.hom U E 0 (scalarForms B U E r) i = scalarFunction B U (r i) :=
  congrFun ((oneCochainCoordinates B.X.hom U E 0).apply_symm_apply _) i

private lemma cechD_scalarForms (r : κ → R) :
    cechD U (oneForms B.X.hom) 0 (scalarForms B U E r) = 0 := by
  apply (oneCochainCoordinates B.X.hom U E 1).injective
  funext i
  rw [oneCochainCoordinates_cechD, scalarForms_coordinates, cechD_scalarFunction, map_zero]
  rfl

private def compatibleFormsFromScalars : (κ → R) ≃ₗ[R] (cechD U (oneForms B.X.hom) 0).ker := by
  let F := (scalarForms B U E).codRestrict (cechD U (oneForms B.X.hom) 0).ker (cechD_scalarForms B U E)
  have hIso : IsIso B.X.hom.appTop := Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions
    _ _ _ inferInstance inferInstance inferInstance ⊤
  refine LinearEquiv.ofBijective F ⟨?_, ?_⟩
  · intro r s hrs
    funext i
    have h : scalarFunction B U (r i) = scalarFunction B U (s i) := by
      rw [← scalarForms_coordinates B U E r i, ← scalarForms_coordinates B U E s i,
        show scalarForms B U E r = scalarForms B U E s from congrArg Subtype.val hrs]
    obtain ⟨t, _, hu⟩ := existsUnique_scalar_of_cechD_zero U B.X.hom _ (cechD_scalarFunction B U (r i))
    exact (hu (r i) (fun _ => rfl)).trans ((hu (s i) (congrFun h)).symm)
  · intro b
    have h (i : κ) : cechD U (functions B.X.hom) 0 (oneCochainCoordinates B.X.hom U E 0 b.val i) = 0 := by
      rw [← oneCochainCoordinates_cechD, b.property, map_zero]
      rfl
    have he (i : κ) : ∃ r : R,
        oneCochainCoordinates B.X.hom U E 0 b.val i = scalarFunction B U r := by
      obtain ⟨r, hr, _⟩ := existsUnique_scalar_of_cechD_zero U B.X.hom _ (h i)
      exact ⟨r, funext hr⟩
    choose r hr using he
    refine ⟨r, Subtype.ext ((oneCochainCoordinates B.X.hom U E 0).injective ?_)⟩
    exact funext fun i => (scalarForms_coordinates B U E r i).trans (hr i).symm

private lemma scalarForms_odd (β : U.I₀ → U.I₀)
    (hβ : ∀ i, coverOpens U i ≤ ι[B.X].left ⁻¹ᵁ coverOpens U (β i)) (r : κ → R) :
    oneFormInversion B U β hβ 0 (scalarForms B U E r) = -scalarForms B U E r := by
  apply (oneCochainCoordinates B.X.hom U E 0).injective
  funext i
  rw [oneCochainCoordinates_inversion, map_neg, Pi.neg_apply, scalarForms_coordinates]
  apply congrArg Neg.neg
  funext σ
  exact (tupleAlgHomOver ι[B.X].left (Over.w ι[B.X]) β hβ σ).commutes (r i)

private lemma pullScalarForms_original (r : κ → R) :
    pullOneForms (𝟙 B.X.left) (Category.id_comp B.X.hom) (inversionOriginalChart B U)
      (inversionOriginalChart_le B U) 0 (scalarForms B (inversionCover B U) E r) = scalarForms B U E r := by
  let α := inversionOriginalChart B U
  funext σ
  rw [pullOneForms_apply]
  have h : tupleAlgHomOver (𝟙 B.X.left) (Category.id_comp B.X.hom) α (inversionOriginalChart_le B U) σ =
      AlgHom.id R (sectionRing B.X.hom (inter (coverOpens U) σ)) :=
    sectionAlgHomOver_id (inter (coverOpens U) σ)
  rw [h]
  let A := sectionRing B.X.hom (inter (coverOpens U) σ)
  let b : Ω[A⁄R] := scalarForms B (inversionCover B U) E r (α ∘ σ)
  change RelativeForms.mapOne (AlgHom.id R A) b = scalarForms B U E r σ
  rw [RelativeForms.mapOne_id]
  apply (hodgeOneBasis B.X.hom E _ (isAffineOpen_inter B.X.hom U σ)).equivFun.injective
  funext i
  exact (congrFun (scalarForms_coordinates B (inversionCover B U) E r i) (α ∘ σ)).trans
    ((congrFun (scalarForms_coordinates B U E r i) σ).symm)

variable [Algebra ℚ R] [LinearOrder κ]

private lemma exteriorD1_scalarForms (r : κ → R) :
    cochainMap U (exteriorD1 B.X.hom) 0 (scalarForms B U E r) = 0 := by
  let V := inversionCover B U
  let β := swapChart U ι[B.X].left
  let hβ := doubledCover_le_preimage U ι[B.X].left (inversion_left_sq B)
  let b := scalarForms B V E r
  have hd : cochainMap V (exteriorD1 B.X.hom) 0 b = 0 := by
    apply exteriorD1_eq_zero_of_odd_of_cechD_zero B V β hβ E b (scalarForms_odd B V E β hβ r)
    rw [cechD_cochainMap, cechD_scalarForms, map_zero]
  rw [← pullScalarForms_original B U E r, ← pullTwoForms_exteriorD1, hd, map_zero]

private def closedFormsFromScalars : (κ → R) ≃ₗ[R] closedForms B.X.hom U :=
  (compatibleFormsFromScalars B U E).trans (LinearEquiv.ofEq _ _ (by
    refine (inf_eq_left.mpr ?_).symm
    intro b hb
    obtain ⟨r, hr⟩ := (compatibleFormsFromScalars B U E).surjective ⟨b, hb⟩
    change cochainMap U (exteriorD1 B.X.hom) 0 b = 0
    rw [← show scalarForms B U E r = b from congrArg Subtype.val hr]
    exact exteriorD1_scalarForms B U E r))

/-- The closed-form term on the supplied cover is finite free over the local base. -/
theorem closedForms_finite_free {R : Type u} [CommRing R] [IsLocalRing R] [Algebra ℚ R]
    (B : AbelianScheme (Spec (CommRingCat.of R))) (U : Scheme.AffineOpenCover.{u} B.X.left) :
    Module.Finite R (closedForms B.X.hom U) ∧ Module.Free R (closedForms B.X.hom U) := by
  obtain ⟨κ, hκ, ⟨E⟩⟩ := exists_finiteFreeRelativeDifferentials B
  let := Fintype.ofFinite κ
  let e := Fintype.equivFin κ
  let : LinearOrder κ := LinearOrder.lift' e e.injective
  let c := closedFormsFromScalars B U E
  exact ⟨Module.Finite.equiv c, Module.Free.of_equiv c⟩

end Langlands.AbelianScheme
