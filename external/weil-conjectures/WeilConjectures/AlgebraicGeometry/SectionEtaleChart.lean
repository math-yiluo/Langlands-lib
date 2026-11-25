/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import WeilConjectures.Mathlib.RingTheory.Regular.RegularSequence

/-!
# Étale charts adapted to a closed section of a smooth morphism

Let `g : V ⟶ B` be smooth of relative dimension `c` with a closed section `s : B ⟶ V`. Near
every point `s(b)` there are étale coordinates `x₁, …, x_c` on `V` over `B` in which `s` is the
origin: an affine open `W ∋ b` of `B`, an affine open `U ∋ s(b)` of `V` over `W`, and functions
`f₁, …, f_c` on `U` generating the ideal of `s(B) ∩ U` and forming a weakly regular sequence,
such that `v = (g, f) : U ⟶ 𝔸^c_W` is étale.

## Main statements

- `AlgebraicGeometry.exists_etale_affineSpace_of_section`: the étale chart along the section.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Blueprint `prose-09-12` (2), the coordinates.

**Étale charts along a closed section.** Let `g : V ⟶ B` be smooth of relative dimension `c`
with a closed section `s`. Every point `b` of `B` has an affine open neighbourhood `W`, and
`s(b)` an affine open neighbourhood `U ⊆ g⁻¹ W` with `s⁻¹ U = W`, together with functions
`f₁, …, f_c` on `U` generating the ideal of `s(B) ∩ U` and forming a weakly regular sequence,
and an étale morphism `v : U ⟶ 𝔸^c_W` over `W` whose fibre coordinates pull back to the `fᵢ`. -/
theorem exists_etale_affineSpace_of_section {V B : Scheme.{u}} (c : ℕ) (g : V ⟶ B)
    [SmoothOfRelativeDimension c g] (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B)
    (b : B) :
    ∃ (W : B.Opens) (_ : IsAffineOpen W) (U : V.affineOpens) (_ : s.base b ∈ U.1)
      (f : Fin c → Γ(V, U.1)) (v : U.1.toScheme ⟶ 𝔸(ULift.{u} (Fin c); W.toScheme)),
      Ideal.span (Set.range f) = (Scheme.Hom.ker s).ideal U ∧
      RingTheory.Sequence.IsWeaklyRegular Γ(V, U.1) (List.ofFn f) ∧ Etale v ∧
      (∀ a, v.appTop (AffineSpace.coord _ (ULift.up a)) = U.1.topIso.inv (f a)) ∧
      U.1 ≤ g ⁻¹ᵁ W ∧ b ∈ W ∧ s ⁻¹ᵁ U.1 = W ∧
      v ≫ 𝔸(ULift.{u} (Fin c); W.toScheme) ↘ W.toScheme ≫ W.ι = U.1.ι ≫ g := by
  obtain ⟨W, hW, U, hUW, hbW, hsU, ψ, hψ, hψf, hI⟩ :=
    Scheme.Hom.exists_etale_coordinates_of_mem_range g s c hs b
  let U' : V.affineOpens := ⟨U.1, U.2⟩
  have hbU : s.base b ∈ U'.1 := by
    change b ∈ s ⁻¹ᵁ U.1
    rwa [hsU]
  let f : Fin c → Γ(V, U'.1) := fun a ↦ ψ (MvPolynomial.X a)
  have hf : Ideal.span (Set.range f) = (Scheme.Hom.ker s).ideal U' := by
    change _ = s.ker.siteIdeal U
    rw [hI, Ideal.mvPolynomialOrigin, Ideal.map_span, ← Set.range_comp]
    rfl
  have hreg : RingTheory.Sequence.IsWeaklyRegular Γ(V, U'.1) (List.ofFn f) := by
    have h := (MvPolynomial.isWeaklyRegular_ofFn_X_sub_C (A := Γ(B, W)) (n := c) 0).map_of_flat
      (RingHom.Etale.iff_flat_and_formallyUnramified.mp hψ).1
    simpa [List.map_ofFn, f, Function.comp_def] using h
  -- the étale ring map
  let ε : MvPolynomial (ULift.{u} (Fin c)) Γ(W.toScheme, ⊤) ≃+* MvPolynomial (Fin c) Γ(B, W) :=
    (MvPolynomial.renameEquiv _ Equiv.ulift).toRingEquiv.trans
      (MvPolynomial.mapEquiv (Fin c) W.topIso.commRingCatIsoToRingEquiv)
  let e₁ := U'.1.topIso.symm.commRingCatIsoToRingEquiv
  let φ := e₁.toRingHom.comp (ψ.comp ε.toRingHom)
  have hφ : φ.Etale := RingHom.Etale.respectsIso.1 _ e₁ (RingHom.Etale.respectsIso.2 ψ ε hψ)
  have hε : ∀ a, ε (MvPolynomial.X (ULift.up a)) = MvPolynomial.X a := fun a ↦ by
    simp [ε]
  have hφX : ∀ a, φ (MvPolynomial.X (ULift.up a)) = U'.1.topIso.inv (f a) := by
    intro a
    change e₁ (ψ (ε (MvPolynomial.X (ULift.up a)))) = _
    rw [hε]
    rfl
  -- the étale morphism
  have : IsAffine U'.1.toScheme := U'.2
  have : IsAffine W.toScheme := hW
  let eW := W.toScheme.isoSpec
  have : IsIso (AffineSpace.map (ULift.{u} (Fin c)) eW.inv) :=
    ⟨⟨AffineSpace.map _ eW.hom, by rw [← AffineSpace.map_comp, eW.inv_hom_id, AffineSpace.map_id],
      by rw [← AffineSpace.map_comp, eW.hom_inv_id, AffineSpace.map_id]⟩⟩
  let E := (AffineSpace.SpecIso (ULift.{u} (Fin c)) Γ(W.toScheme, ⊤)).inv ≫
    AffineSpace.map (ULift.{u} (Fin c)) eW.inv
  let v := U'.1.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ E
  have hring : CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom φ =
      (g.resLE W U.1 hUW).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    ext x
    change e₁ (ψ (ε (MvPolynomial.C x))) = _
    have hC : ε (MvPolynomial.C x) = MvPolynomial.C (W.topIso.hom x) := by simp [ε]
    rw [hC, ← RingHom.comp_apply ψ MvPolynomial.C, hψf]
    rfl
  have hover : v ≫ 𝔸(ULift.{u} (Fin c); W.toScheme) ↘ W.toScheme = g.resLE W U.1 hUW := by
    simp only [v, E, Category.assoc, AffineSpace.map_over, AffineSpace.SpecIso_inv_over_assoc]
    rw [← Spec.map_comp_assoc, hring, Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id,
      Category.comp_id]
  refine ⟨W, hW, U', hbU, f, v, hf, hreg, ?_, fun a ↦ ?_, hUW, hbW, hsU, ?_⟩
  rotate_right
  · rw [← Category.assoc, hover]
    exact Scheme.Hom.resLE_comp_ι g hUW
  · have : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.mpr hφ
    infer_instance
  · simp only [v, E, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord]
    rw [AffineSpace.SpecIso_inv_appTop_coord]
    have key : (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso _).inv
        (MvPolynomial.X (ULift.up a))) =
        (Scheme.ΓSpecIso Γ(U'.1.toScheme, ⊤)).inv (φ (MvPolynomial.X (ULift.up a))) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    erw [key]
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop, Iso.inv_hom_id_apply, hφX]

end AlgebraicGeometry
