import Langlands.AlgebraicGeometry.PointTopology.SchemeClosedPointProofs

/-! # Transport and composition of actual quotient sections

Sections transfer across a compatible isomorphism of quotient targets. Affine
refinement also permits lifting sections through a preceding morphism that
lifts every actual map from an affine relative scheme.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.HomogeneousQuotientSectionTransport

variable (R : Type u) [CommRing R]
variable {X Y Q Q' : Over (Spec (CommRingCat.of R))}

/-- Transport an actual section to an isomorphic quotient target. -/
def sectionAlongIso (e : Q ≅ Q') (U : Q.left.Opens)
    (s : openOver R Q U ⟶ X) :
    openOver R Q' (e.inv.left ⁻¹ᵁ U) ⟶ X :=
  restrictedOver R e.inv U ≫ s

/-- The transported map is a section of the compatible target projection. -/
theorem sectionAlongIso_comp (q : X ⟶ Q) (q' : X ⟶ Q')
    (e : Q ≅ Q') (he : q ≫ e.hom = q') (U : Q.left.Opens)
    (s : openOver R Q U ⟶ X) (hs : s ≫ q = openOverι R Q U) :
    sectionAlongIso R e U s ≫ q' =
      openOverι R Q' (e.inv.left ⁻¹ᵁ U) := by
  rw [sectionAlongIso, ← he, Category.assoc, ← Category.assoc s, hs,
    ← Category.assoc, restrictedOver_fac, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- Sections on neighborhoods of all topological points transfer to any
compatible isomorphic quotient target. -/
theorem localSections_of_iso (q : X ⟶ Q) (q' : X ⟶ Q')
    (e : Q ≅ Q') (he : q ≫ e.hom = q')
    (hq : ∀ x : Q.left, ∃ (U : Q.left.Opens) (s : openOver R Q U ⟶ X),
      x ∈ U ∧ s ≫ q = openOverι R Q U) :
    ∀ x : Q'.left, ∃ (U : Q'.left.Opens) (s : openOver R Q' U ⟶ X),
      x ∈ U ∧ s ≫ q' = openOverι R Q' U := by
  intro x
  obtain ⟨U, s, hx, hs⟩ := hq (e.inv.left x)
  exact ⟨e.inv.left ⁻¹ᵁ U, sectionAlongIso R e U s, hx,
    sectionAlongIso_comp R q q' e he U s hs⟩

/-- Existence of algebraic sections at every topological point is independent
of a compatible isomorphic quotient model. -/
theorem localSections_iff_of_iso (q : X ⟶ Q) (q' : X ⟶ Q')
    (e : Q ≅ Q') (he : q ≫ e.hom = q') :
    (∀ x : Q.left, ∃ (U : Q.left.Opens) (s : openOver R Q U ⟶ X),
      x ∈ U ∧ s ≫ q = openOverι R Q U) ↔
    (∀ x : Q'.left, ∃ (U : Q'.left.Opens) (s : openOver R Q' U ⟶ X),
      x ∈ U ∧ s ≫ q' = openOverι R Q' U) := by
  refine ⟨localSections_of_iso R q q' e he, ?_⟩
  apply localSections_of_iso R q' q e.symm
  change q' ≫ e.inv = q
  rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A section can be restricted to an affine neighborhood of any point in its
domain, retaining its equation with the original projection. -/
theorem exists_affine_section (q : X ⟶ Q) (U : Q.left.Opens)
    (s : openOver R Q U ⟶ X) (hs : s ≫ q = openOverι R Q U)
    (x : Q.left) (hx : x ∈ U) :
    ∃ (V : Q.left.Opens) (_ : IsAffine V) (t : openOver R Q V ⟶ X),
      x ∈ V ∧ V ≤ U ∧ t ≫ q = openOverι R Q V := by
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle : V ≤ U := hVU
  refine ⟨V, hV, openOverHomOfLE R Q hle ≫ s, hxV, hle, ?_⟩
  rw [Category.assoc, hs, openOverHomOfLE_ι]

/-- Lift a local section through a preceding morphism after affine shrinking.
The lifting hypothesis quantifies over actual maps from affine relative schemes. -/
theorem exists_section_comp_of_affine_lifts (f : X ⟶ Y) (q : Y ⟶ Q)
    (hf : ∀ (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left]
      (a : T ⟶ Y), ∃ b : T ⟶ X, b ≫ f = a)
    (U : Q.left.Opens) (s : openOver R Q U ⟶ Y)
    (hs : s ≫ q = openOverι R Q U) (x : Q.left) (hx : x ∈ U) :
    ∃ (V : Q.left.Opens) (_ : IsAffine V) (t : openOver R Q V ⟶ X),
      x ∈ V ∧ V ≤ U ∧ t ≫ (f ≫ q) = openOverι R Q V := by
  obtain ⟨V, hV, a, hxV, hVU, ha⟩ := exists_affine_section R q U s hs x hx
  let : IsAffine V := hV
  obtain ⟨b, hb⟩ := hf (openOver R Q V) a
  exact ⟨V, hV, b, hxV, hVU, by rw [← Category.assoc, hb, ha]⟩

/-- If the first morphism lifts all affine tests and the second has Zariski
local sections, their composite has local sections at all topological points. -/
theorem localSections_comp_of_affine_lifts (f : X ⟶ Y) (q : Y ⟶ Q)
    (hf : ∀ (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left]
      (a : T ⟶ Y), ∃ b : T ⟶ X, b ≫ f = a)
    (hq : ∀ x : Q.left, ∃ (U : Q.left.Opens) (s : openOver R Q U ⟶ Y),
      x ∈ U ∧ s ≫ q = openOverι R Q U) :
    ∀ x : Q.left, ∃ (U : Q.left.Opens) (s : openOver R Q U ⟶ X),
      x ∈ U ∧ s ≫ (f ≫ q) = openOverι R Q U := by
  intro x
  obtain ⟨U, s, hx, hs⟩ := hq x
  obtain ⟨V, _, t, hxV, _, ht⟩ :=
    exists_section_comp_of_affine_lifts R f q hf U s hs x hx
  exact ⟨V, t, hxV, ht⟩

/-- Local sections of a composite give local sections of its second morphism. -/
theorem localSections_of_comp (f : X ⟶ Y) (q : Y ⟶ Q)
    (h : ∀ x : Q.left, ∃ (U : Q.left.Opens) (s : openOver R Q U ⟶ X),
      x ∈ U ∧ s ≫ (f ≫ q) = openOverι R Q U) :
    ∀ x : Q.left, ∃ (U : Q.left.Opens) (s : openOver R Q U ⟶ Y),
      x ∈ U ∧ s ≫ q = openOverι R Q U := by
  intro x
  obtain ⟨U, s, hx, hs⟩ := h x
  exact ⟨U, s ≫ f, hx, by rw [Category.assoc, hs]⟩

end Langlands.GroupScheme.HomogeneousQuotientSectionTransport
