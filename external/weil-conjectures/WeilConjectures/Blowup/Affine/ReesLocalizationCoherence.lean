/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Affine.Functoriality
public import Mathlib.RingTheory.Localization.Away.Basic

/-!

# Coherence of the Rees-algebra localization maps

For a localization `φ : A → B = A[1/s]` and `J = I·B`, the Rees-algebra localization map is
the graded ring homomorphism `reesGrading.hom (algebraMap A B) h` given by coefficientwise
application of `φ` (see `WeilConjectures.Blowup.Affine.Localization`). In this file we show
that these maps are coherent with the canonical identifications of iterated localizations:

- localizing at `s` and then at `t` agrees with localizing at `s * t`, after the canonical
  isomorphism `(A_s)_t ≅ A_{st}`;
- localizing at `1` is the identity, after the canonical isomorphism `A_1 ≅ A`.

## Main definitions

- `IsLocalization.Away.mulAlgEquiv` — the canonical `A`-algebra isomorphism `(A_s)_t ≅ A_{st}`.

## Main results

- `AlgebraicGeometry.reesGrading.hom_comp_of_comp_eq` — the Rees maps compose like the
  underlying ring maps.
- `AlgebraicGeometry.reesGrading.hom_localization_mul` /
  `AlgebraicGeometry.AffineBlowup.hom_localization_mul` — iterated localization coherence
  (blueprint: `definition-admissible-blow-up--1`).
- `AlgebraicGeometry.reesGrading.hom_localization_one` /
  `AlgebraicGeometry.AffineBlowup.hom_localization_one` — localization at one
  (blueprint: `definition-admissible-blow-up--1`).

-/

@[expose] public section

universe u

open CategoryTheory

/-- The canonical `A`-algebra isomorphism `(A_s)_t ≅ A_{st}` between a localization `C` of
`B = A_s` away from the image of `t` and a localization `D` of `A` away from `s * t`. -/
noncomputable def IsLocalization.Away.mulAlgEquiv {A : Type*} (B C D : Type*) [CommRing A]
    [CommRing B] [CommRing C] [CommRing D] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [Algebra A D] (s t : A) [IsLocalization.Away s B]
    [IsLocalization.Away (algebraMap A B t) C] [IsLocalization.Away (s * t) D] :
    C ≃ₐ[A] D :=
  letI := IsLocalization.Away.mul' B C s t
  IsLocalization.algEquiv (Submonoid.powers (s * t)) C D

namespace AlgebraicGeometry

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable {I : Ideal A} {J : Ideal B} {K : Ideal C} {L : Ideal D}

/-- The Rees maps compose like the underlying ring maps: if `ψ ∘ φ = χ`, then
`reesGrading.hom ψ ∘ reesGrading.hom φ = reesGrading.hom χ`. -/
lemma reesGrading.hom_comp_of_comp_eq (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C)
    (hχ : ψ.comp φ = χ) (h : I.map φ = J) (h' : J.map ψ = K) (h'' : I.map χ = K) :
    (reesGrading.hom ψ h').comp (reesGrading.hom φ h) = reesGrading.hom χ h'' := by
  subst hχ
  exact reesGrading.hom_comp φ ψ h h'

/-- Scheme-level version of `reesGrading.hom_comp_of_comp_eq`. -/
lemma AffineBlowup.hom_comp_of_comp_eq (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C)
    (hχ : ψ.comp φ = χ) (h : I.map φ = J) (h' : J.map ψ = K) (h'' : I.map χ = K) :
    AffineBlowup.hom ψ h' ≫ AffineBlowup.hom φ h = AffineBlowup.hom χ h'' := by
  subst hχ
  exact (AffineBlowup.hom_comp φ ψ h h').symm

section Mul

variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] [Algebra A D]
  (s t : A) [IsLocalization.Away s B] [IsLocalization.Away (algebraMap A B t) C]
  [IsLocalization.Away (s * t) D]

variable (B C D) in
lemma _root_.IsLocalization.Away.mulAlgEquiv_comp_algebraMap :
    (IsLocalization.Away.mulAlgEquiv B C D s t : C →+* D).comp
      ((algebraMap B C).comp (algebraMap A B)) = algebraMap A D :=
  RingHom.ext fun a => by
    rw [RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact (IsLocalization.Away.mulAlgEquiv B C D s t).commutes a

/-- Blueprint `definition-admissible-blow-up--1`: Iterated localization coherence.

Localizing the Rees algebra first at `s` (`A → B = A_s`) and then at `t` (`B → C = (A_s)_t`)
gives the same graded map as localizing at `s * t` (`A → D = A_{st}`), after the canonical
isomorphism `(A_s)_t ≅ A_{st}` of `IsLocalization.Away.mulAlgEquiv`. -/
theorem reesGrading.hom_localization_mul (h₁ : I.map (algebraMap A B) = J)
    (h₂ : J.map (algebraMap B C) = K)
    (h₃ : K.map (IsLocalization.Away.mulAlgEquiv B C D s t : C →+* D) = L)
    (h : I.map (algebraMap A D) = L) :
    (reesGrading.hom (IsLocalization.Away.mulAlgEquiv B C D s t : C →+* D) h₃).comp
        ((reesGrading.hom (algebraMap B C) h₂).comp (reesGrading.hom (algebraMap A B) h₁)) =
      reesGrading.hom (algebraMap A D) h := by
  rw [reesGrading.hom_comp_of_comp_eq _ _ _ rfl h₁ h₂ (by rw [← Ideal.map_map, h₁, h₂])]
  exact reesGrading.hom_comp_of_comp_eq _ _ _
    (IsLocalization.Away.mulAlgEquiv_comp_algebraMap B C D s t) _ _ _

/-- Blueprint `definition-admissible-blow-up--1`: Iterated localization coherence, for the
induced morphisms of affine blow-ups. -/
theorem AffineBlowup.hom_localization_mul (h₁ : I.map (algebraMap A B) = J)
    (h₂ : J.map (algebraMap B C) = K)
    (h₃ : K.map (IsLocalization.Away.mulAlgEquiv B C D s t : C →+* D) = L)
    (h : I.map (algebraMap A D) = L) :
    AffineBlowup.hom (IsLocalization.Away.mulAlgEquiv B C D s t : C →+* D) h₃ ≫
        AffineBlowup.hom (algebraMap B C) h₂ ≫ AffineBlowup.hom (algebraMap A B) h₁ =
      AffineBlowup.hom (algebraMap A D) h := by
  rw [AffineBlowup.hom_comp_of_comp_eq _ _ _ rfl h₁ h₂ (by rw [← Ideal.map_map, h₁, h₂])]
  exact AffineBlowup.hom_comp_of_comp_eq _ _ _
    (IsLocalization.Away.mulAlgEquiv_comp_algebraMap B C D s t) _ _ _

end Mul

section One

variable [Algebra A B] [IsLocalization.Away (1 : A) B]

/-- Blueprint `definition-admissible-blow-up--1`: Localization at one.

After the canonical identification `A_1 ≅ A` (`IsLocalization.atOne`), the Rees localization
map at `1` is the identity of the Rees algebra. -/
theorem reesGrading.hom_localization_one (h₁ : I.map (algebraMap A B) = J)
    (h₂ : J.map ((IsLocalization.atOne A B).symm : B →+* A) = I) :
    (reesGrading.hom ((IsLocalization.atOne A B).symm : B →+* A) h₂).comp
        (reesGrading.hom (algebraMap A B) h₁) = .id (reesGrading I) := by
  rw [reesGrading.hom_comp_of_comp_eq _ _ (RingHom.id A)
    (RingHom.ext fun a => (IsLocalization.atOne A B).symm.commutes a) h₁ h₂ (Ideal.map_id I)]
  exact reesGrading.hom_id

/-- Blueprint `definition-admissible-blow-up--1`: Localization at one, for the induced
morphisms of affine blow-ups. -/
theorem AffineBlowup.hom_localization_one (h₁ : I.map (algebraMap A B) = J)
    (h₂ : J.map ((IsLocalization.atOne A B).symm : B →+* A) = I) :
    AffineBlowup.hom ((IsLocalization.atOne A B).symm : B →+* A) h₂ ≫
        AffineBlowup.hom (algebraMap A B) h₁ = 𝟙 (AffineBlowup I) := by
  rw [AffineBlowup.hom_comp_of_comp_eq _ _ (RingHom.id A)
    (RingHom.ext fun a => (IsLocalization.atOne A B).symm.commutes a) h₁ h₂ (Ideal.map_id I)]
  exact AffineBlowup.hom_id

end One

end AlgebraicGeometry
