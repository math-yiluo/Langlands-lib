/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# A conditional cancellation lemma for local ring hom properties

`AlgebraicGeometry.HasRingHomProperty.of_comp` deduces `P f` from `P (f ≫ g)` whenever the
underlying ring hom property `Q` cancels unconditionally on the left. Many cancellation
statements in commutative algebra are not of this shape: they need an extra hypothesis on the
first ring map. The prototype is Stacks Tag 02FV, where `g ∘ f` of finite presentation and `f`
of finite type give `g` of finite presentation.

`AlgebraicGeometry.HasRingHomProperty.of_comp'` is the corresponding variant, taking a second
morphism property `P'` (also given by a local ring hom property `Q'`) as the extra hypothesis
on `g`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.HasRingHomProperty

variable {P P' : MorphismProperty Scheme.{u}}
  {Q Q' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
  [HasRingHomProperty P Q] [HasRingHomProperty P' Q']

/-- A conditional version of `AlgebraicGeometry.HasRingHomProperty.of_comp`: if the ring hom
property `Q` cancels on the left in the presence of `Q'`, then `P` cancels on the left in the
presence of `P'`.

Note that the roles of the two morphisms are swapped when passing between schemes and rings:
the hypothesis `Q' f` on the *first* ring map corresponds to the hypothesis `P' g` on the
*second* morphism of schemes. -/
theorem of_comp'
    (H : ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      ∀ (f : R →+* S) (g : S →+* T), Q' f → Q (g.comp f) → Q g)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (h : P (f ≫ g)) (hg : P' g) : P f := by
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H' := IsZariskiLocalAtTarget.restrict h U.1
    rw [morphismRestrict_comp] at H'
    exact this H' (IsZariskiLocalAtTarget.restrict hg U.1) inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top Y)]
    intro U
    have H' := comp_of_isOpenImmersion P (f ⁻¹ᵁ U.1).ι (f ≫ g) h
    rw [← morphismRestrict_ι_assoc] at H'
    exact this H' (comp_of_isOpenImmersion P' U.1.ι g hg) inferInstance
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top X)]
    intro U
    have H' := comp_of_isOpenImmersion P U.1.ι (f ≫ g) h
    rw [← Category.assoc] at H'
    exact this H' inferInstance
  rw [iff_of_isAffine (P := P)] at h ⊢
  exact H _ _ (appTop P' g hg) h

end AlgebraicGeometry.HasRingHomProperty
