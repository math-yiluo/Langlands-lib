/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Sections on an affine open of a scheme-theoretic fibre

Source: Stacks Project, Tags 01I4 and 01JQ, affine fibre-product formula.
-/

@[expose] public section

universe u
open scoped TensorProduct
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Sections on the inverse image of an affine open in a fibre are its residue-field tensor.

Source: Stacks Project, Tags 01I4 and 01JQ; Tag 055J, affine fibre identifications.
Proof: Restrict the defining pullback square of the fibre to U. Pasting pullback squares
identifies this restriction with the pullback of U.toScheme and Spec κ(p) over Spec R.
The affine-open spectrum isomorphism identifies U.toScheme with Spec Γ(X,U), and the
spectrum residue-field isomorphism identifies the second map with Spec of R → κ(p).
The affine pullback isomorphism therefore identifies the restricted fibre with
Spec(Γ(X,U) ⊗[R] κ(p)). Apply global sections and the spectrum global-sections
isomorphism. The first-projection equation for the affine pullback isomorphism gives
that restriction of a maps to a ⊗ 1. This also applies to the empty affine open:
its section ring and its tensor product are zero rings.
(blueprint: lem-sbc-affine-fibre-sections-tensor) -/
theorem affine_fibre_sections_tensor {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (U : X.affineOpens) (p : PrimeSpectrum R) :
    let ρ := (Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U.1 le_top
    let _ : Algebra R Γ(X, U.1) := ρ.hom.toAlgebra
    ∃ e : Γ(f.fiber p, (f.fiberι p) ⁻¹ᵁ U.1) ≃+*
        (Γ(X, U.1) ⊗[R] p.asIdeal.ResidueField),
      ∀ a : Γ(X, U.1), e ((f.fiberι p).app U.1 a) =
        TensorProduct.tmul R a 1 := by
  classical
  dsimp only
  let A := Γ(X, U.1)
  let ρ := (Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U.1 le_top
  let : Algebra R A := ρ.hom.toAlgebra
  let V := (f.fiberι p) ⁻¹ᵁ U.1
  let κ := (Spec (.of R)).residueField p
  let K := p.asIdeal.ResidueField
  let g := (Spec (.of R)).fromSpecResidueField p
  let j := V.ι ≫ f.fiberToSpecResidueField p
  have h := ((isPullback_morphismRestrict (f.fiberι p) U.1).flip.paste_horiz
    (IsPullback.of_hasPullback f g).flip).flip
  have : IsAffine U.1.toScheme := U.2
  have H := isPushout_appTop_of_isPullback h
  let eK : Γ(Spec κ, ⊤) ≅ CommRingCat.of K :=
    (Scheme.ΓSpecIso κ) ≪≫ Scheme.Spec.residueFieldIso (.of R) p
  let b := eK.inv ≫ j.appTop ≫ V.topIso.hom
  have H' : IsPushout ρ (CommRingCat.ofHom (algebraMap R K))
      ((f.fiberι p).app U.1) b := by
    refine H.of_iso (Scheme.ΓSpecIso (.of R)) U.1.topIso eK V.topIso ?_ ?_ ?_ ?_
    · simp [ρ, Scheme.Hom.appLE, ← Functor.map_comp]
    · dsimp [g, eK, κ, K]
      rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
      simp [Scheme.ΓSpecIso_naturality, Scheme.ΓSpecIso_naturality_assoc]
    · rw [← Scheme.Hom.resLE_eq_morphismRestrict]
      simp only [Scheme.Hom.appTop]
      rw [Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app]
      simp only [V, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · change j.appTop ≫ V.topIso.hom = eK.hom ≫ b
      simp only [b, Iso.hom_inv_id_assoc]
  let e :=
    (H'.isoIsPushout _ _ (CommRingCat.isPushout_tensorProduct R A K)).commRingCatIsoToRingEquiv
  refine ⟨e, ?_⟩
  intro a
  exact congr($(H'.inl_isoIsPushout_hom _ _
    (CommRingCat.isPushout_tensorProduct R A K)).hom a)

end AlgebraicGeometry
