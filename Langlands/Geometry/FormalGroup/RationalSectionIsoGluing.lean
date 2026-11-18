import Langlands.Geometry.FormalGroup.RationalSectionIso

/-! # Gluing actual rational-section inverses -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {U : Opens (PrimeSpectrum R)}

namespace RationalSectionIso

/-- Local actual inverses to the restrictions of one forward section glue
uniquely. Their restrictions agree automatically by inverse uniqueness. -/
theorem existsUnique_of_cover {ι : Type*} (V : ι → Opens (PrimeSpectrum R))
    (i : ∀ a, V a ⟶ U) (hcover : ∀ x ∈ U, ∃ a, x ∈ V a)
    (z : RationalSection F M N U) (e : ∀ a, RationalSectionIso F M N (V a))
    (he : ∀ a, (e a).hom = RationalSection.restrict (i a) z) :
    ∃! g : RationalSectionIso F M N U,
      g.hom = z ∧ ∀ a, g.restrict (i a) = e a := by
  have hc : U ≤ iSup V := by
    intro x hx
    obtain ⟨a, ha⟩ := hcover x hx
    exact (le_iSup V a) ha
  have hinv : TopCat.Presheaf.IsCompatible (rationalHomTypeSheaf F N M).obj V
      (fun a => (e a).inv) := by
    intro a b
    have hab : (e a).restrict (homOfLE inf_le_left) =
        (e b).restrict (homOfLE inf_le_right) := by
      apply ext
      change RationalSection.restrict (homOfLE inf_le_left) (e a).hom =
        RationalSection.restrict (homOfLE inf_le_right) (e b).hom
      rw [he a, he b, ← RationalSection.restrict_comp,
        ← RationalSection.restrict_comp]
      rfl
    exact congrArg RationalSectionIso.inv hab
  obtain ⟨w, hw, -⟩ :=
    (rationalHomTypeSheaf F N M).existsUnique_gluing' V U i hc
      (fun a => (e a).inv) hinv
  change RationalSection F N M U at w
  change ∀ a, RationalSection.restrict (i a) w = (e a).inv at hw
  have hleft : RationalSection.comp w z = RationalSection.id M U := by
    apply (rationalHomTypeSheaf F M M).eq_of_locally_eq' V U i hc
    intro a
    change RationalSection.restrict (i a) (RationalSection.comp w z) =
      RationalSection.restrict (i a) (RationalSection.id M U)
    rw [RationalSection.restrict_comp_hom, RationalSection.restrict_id_section]
    rw [hw a, ← he a]
    exact (e a).inv_hom
  have hright : RationalSection.comp z w = RationalSection.id N U := by
    apply (rationalHomTypeSheaf F N N).eq_of_locally_eq' V U i hc
    intro a
    change RationalSection.restrict (i a) (RationalSection.comp z w) =
      RationalSection.restrict (i a) (RationalSection.id N U)
    rw [RationalSection.restrict_comp_hom, RationalSection.restrict_id_section]
    rw [hw a, ← he a]
    exact (e a).hom_inv
  let g : RationalSectionIso F M N U := ⟨z, w, hleft, hright⟩
  refine ⟨g, ⟨rfl, ?_⟩, ?_⟩
  · intro a
    apply ext
    exact (he a).symm
  · intro g' hg'
    exact ext hg'.1

/-- Invertibility together with the reverse local scalar-isogeny condition
descends from an arbitrary open cover. -/
theorem existsUnique_locallyScalar_of_cover {ι : Type*}
    (π : O) (V : ι → Opens (PrimeSpectrum R))
    (i : ∀ a, V a ⟶ U) (hcover : ∀ x ∈ U, ∃ a, x ∈ V a)
    (z : RationalSection F M N U) (e : ∀ a, RationalSectionIso F M N (V a))
    (he : ∀ a, (e a).hom = RationalSection.restrict (i a) z)
    (hl : ∀ a, RationalSection.IsLocallyScalarIsogeny π (e a).inv) :
    ∃! g : RationalSectionIso F M N U,
      g.hom = z ∧ RationalSection.IsLocallyScalarIsogeny π g.inv := by
  obtain ⟨g, ⟨hg, hge⟩, -⟩ := existsUnique_of_cover V i hcover z e he
  refine ⟨g, ⟨hg, ?_⟩, ?_⟩
  · apply RationalSection.IsLocallyScalarIsogeny.of_cover V i hcover
    intro a
    have h := congrArg RationalSectionIso.inv (hge a)
    change RationalSection.restrict (i a) g.inv = (e a).inv at h
    rw [h]
    exact hl a
  · intro g' hg'
    exact ext (hg'.1.trans hg.symm)

/-- Pointwise local actual inverse witnesses suffice for the complete
unique inverse-section conclusion, with no uniform denominator. -/
theorem existsUnique_locallyScalar_of_locally (π : O)
    (z : RationalSection F M N U)
    (h : ∀ x ∈ U, ∃ (V : Opens (PrimeSpectrum R)) (_hx : x ∈ V)
      (i : V ⟶ U) (e : RationalSectionIso F M N V),
        e.hom = RationalSection.restrict i z ∧
          RationalSection.IsLocallyScalarIsogeny π e.inv) :
    ∃! g : RationalSectionIso F M N U,
      g.hom = z ∧ RationalSection.IsLocallyScalarIsogeny π g.inv := by
  choose V hx i e he hl using fun x : U => h x.val x.property
  exact existsUnique_locallyScalar_of_cover π V i
    (fun x hxU => ⟨⟨x, hxU⟩, hx ⟨x, hxU⟩⟩) z e he hl

end RationalSectionIso
end Langlands.FormalGroup.ModuleLaw
