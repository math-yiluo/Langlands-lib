/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import WeilConjectures.AlgebraicGeometry.ThickeningAffineScheme

/-!
# Integrality is insensitive to thickenings

Source: Stacks Project, More on Morphisms, Lemma 37.3.1 (Tag 09ZV), part (5)
(blueprint: lem-weil-pbc-thickening-integral).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Integrality is invariant under a morphism of arbitrary thickenings. No cartesian
or finite order assumption is needed.

Source: Stacks Project, More on Morphisms, Tag 09ZV, part (5).
(blueprint: lem-weil-pbc-thickening-integral).

Proof:
1. Both thickening maps are closed immersions surjective on points, hence universal
   homeomorphisms, separated, affine, integral and universally closed
   (def-sbc-first-order-thickening; lem-weil-pbc-closed-immersion-integral-separated-uc).
   The square identifies the composites `i_X ≫ f'` and `f ≫ i_S`.
2. If `f'` is integral, its composite with `i_X` is integral. Since `i_S` is separated,
   integrality of `f ≫ i_S` implies integrality of `f` by Morphisms Tag 035D (2)
   (lem-weil-pbc-integral-of-comp-separated).
3. Conversely, if `f` is integral, it is affine and universally closed by Morphisms
   Tag 01WM (pqf-lem-integral-univclosed).
4. The composite `f ≫ i_S` is universally closed. It equals `i_X ≫ f'`, and `i_X`
   is surjective, so `f'` is universally closed
   (lem-weil-pbc-image-universally-closed; Mathlib UniversallyClosed.of_comp_surjective).
5. For an affine open `V'` of `S'`, its inverse image `V` under `i_S` is affine since
   `i_S` is affine. Then `f` inverse image of `V` is affine. By the square this is
   the inverse image under `i_X` of `f'` inverse image of `V'`. Restricting `i_X`
   gives a thickening of that affine scheme. Tag 06AD makes `f'` inverse image
   of `V'` affine (lem-weil-pbc-thickening-affine-scheme), proving `f'` affine.
6. An affine universally closed morphism is integral by Tag 01WM. Together with
   step 2 this proves the equivalence. -/
theorem isIntegralHom_iff_of_thickenings {S S' X X' : Scheme.{u}}
    (i_S : S ⟶ S') (i_X : X ⟶ X') (f' : X' ⟶ S') (f : X ⟶ S)
    (hS : IsThickening i_S) (hX : IsThickening i_X)
    (hcomm : i_X ≫ f' = f ≫ i_S) : IsIntegralHom f ↔ IsIntegralHom f' := by
  have : IsClosedImmersion i_S := hS.1
  have : IsClosedImmersion i_X := hX.1
  have : Surjective i_X := hX.2
  constructor
  · intro hf
    have : IsIntegralHom f := hf
    have : UniversallyClosed (i_X ≫ f') := by
      rw [hcomm]
      infer_instance
    have : UniversallyClosed f' := UniversallyClosed.of_comp_surjective i_X f'
    have : IsAffineHom f' := by
      constructor
      intro U hU
      have hpre : IsAffineOpen (i_X ⁻¹ᵁ (f' ⁻¹ᵁ U)) := by
        rw [← Scheme.Hom.comp_preimage, hcomm, Scheme.Hom.comp_preimage]
        exact (hU.preimage i_S).preimage f
      have : IsAffine (i_X ⁻¹ᵁ (f' ⁻¹ᵁ U)).toScheme := hpre
      have : Surjective (i_X ∣_ (f' ⁻¹ᵁ U)) := by
        constructor
        intro x
        obtain ⟨y, hy⟩ := i_X.surjective x.1
        refine ⟨⟨y, ?_⟩, ?_⟩
        · change i_X y ∈ f' ⁻¹ᵁ U
          rw [hy]
          exact x.2
        · apply Subtype.ext
          simpa only [morphismRestrict_base_coe] using hy
      exact isAffine_of_isThickening (i_X ∣_ (f' ⁻¹ᵁ U))
        ⟨inferInstance, inferInstance⟩
    exact IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  · intro hf'
    have : IsIntegralHom f' := hf'
    have : IsIntegralHom (f ≫ i_S) := by
      rw [← hcomm]
      infer_instance
    exact IsIntegralHom.of_comp f i_S

end AlgebraicGeometry
