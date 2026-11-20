import Langlands.Geometry.FormalGroup.FormalIdempotentImage
import Langlands.Geometry.FormalGroup.RationalSectionBaseChangeCalculus

/-! # Restriction of rational sections to images of formal idempotents -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.Hom.IdempotentImage

open CategoryTheory TopologicalSpace RationalSection

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ υ σ' τ' υ' : Type}
variable [Finite σ] [Finite τ] [Finite υ] [Finite σ'] [Finite τ'] [Finite υ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'} {P' : ModuleLaw O R υ'}
variable {e : Hom M M} {d : Hom N N} {c : Hom P P}
variable {U V : Opens (PrimeSpectrum R)}

/-- Restrict a rational section by composing with the source inclusion and target projection. -/
def restrictSection (A : IdempotentImage e M') (B : IdempotentImage d N')
    (f : RationalSection F M N U) : RationalSection F M' N' U :=
  RationalSection.comp (ofHom B.projection U) (RationalSection.comp f (ofHom A.inclusion U))

@[simp]
theorem restrictSection_ofHom (A : IdempotentImage e M') (B : IdempotentImage d N')
    (f : Hom M N) (U : Opens (PrimeSpectrum R)) :
    A.restrictSection B (ofHom (F := F) f U) = ofHom (A.restrictHom B f) U := by
  rw [restrictSection, comp_ofHom, comp_ofHom, restrictHom]

theorem inclusion_restrictSection (A : IdempotentImage e M') (B : IdempotentImage d N')
    (f : RationalSection F M N U)
    (hf : RationalSection.comp f (ofHom e U) = RationalSection.comp (ofHom d U) f) :
    RationalSection.comp (ofHom B.inclusion U) (A.restrictSection B f) =
      RationalSection.comp f (ofHom A.inclusion U) := by
  rw [restrictSection, ← RationalSection.comp_assoc (ofHom B.inclusion U), comp_ofHom,
    B.inclusion_projection, ← RationalSection.comp_assoc (ofHom d U), ← hf,
    RationalSection.comp_assoc, comp_ofHom, A.projector_inclusion]

@[simp]
theorem restrictSection_id (A : IdempotentImage e M') (U : Opens (PrimeSpectrum R)) :
    A.restrictSection A (RationalSection.id (F := F) M U) = RationalSection.id M' U := by
  rw [← ofHom_id, restrictSection_ofHom, A.restrictHom_id, ofHom_id]

theorem restrictSection_comp (A : IdempotentImage e M') (B : IdempotentImage d N')
    (C : IdempotentImage c P') (g : RationalSection F N P U) (f : RationalSection F M N U)
    (hf : RationalSection.comp f (ofHom e U) = RationalSection.comp (ofHom d U) f) :
    A.restrictSection C (RationalSection.comp g f) =
      RationalSection.comp (B.restrictSection C g) (A.restrictSection B f) := by
  change RationalSection.comp (ofHom C.projection U)
      (RationalSection.comp (RationalSection.comp g f) (ofHom A.inclusion U)) =
    RationalSection.comp
      (RationalSection.comp (ofHom C.projection U) (RationalSection.comp g (ofHom B.inclusion U)))
      (A.restrictSection B f)
  rw [RationalSection.comp_assoc (ofHom C.projection U), RationalSection.comp_assoc g,
    RationalSection.comp_assoc g (ofHom B.inclusion U), A.inclusion_restrictSection B f hf]

private theorem sectionInv_intertwines (f : RationalSectionIso F M N U)
    (hf : RationalSection.comp f.hom (ofHom e U) = RationalSection.comp (ofHom d U) f.hom) :
    RationalSection.comp f.inv (ofHom d U) = RationalSection.comp (ofHom e U) f.inv := by
  calc
    RationalSection.comp f.inv (ofHom d U) = RationalSection.comp f.inv
        (RationalSection.comp (RationalSection.comp (ofHom d U) f.hom) f.inv) := by
      rw [RationalSection.comp_assoc (ofHom d U), f.hom_inv, RationalSection.comp_id]
    _ = RationalSection.comp (ofHom e U) f.inv := by
      rw [← hf, ← RationalSection.comp_assoc f.inv (RationalSection.comp f.hom (ofHom e U)),
        ← RationalSection.comp_assoc f.inv f.hom (ofHom e U), f.inv_hom, RationalSection.id_comp]

/-- An invertible section intertwining the projectors restricts in both directions. -/
def restrictSectionIso (A : IdempotentImage e M') (B : IdempotentImage d N')
    (f : RationalSectionIso F M N U)
    (hf : RationalSection.comp f.hom (ofHom e U) = RationalSection.comp (ofHom d U) f.hom) :
    RationalSectionIso F M' N' U where
  hom := A.restrictSection B f.hom
  inv := B.restrictSection A f.inv
  inv_hom := by rw [← A.restrictSection_comp B A _ _ hf, f.inv_hom, A.restrictSection_id]
  hom_inv := by
    rw [← B.restrictSection_comp A B _ _ (sectionInv_intertwines f hf), f.hom_inv,
      B.restrictSection_id]

theorem restrict_restrictSection (A : IdempotentImage e M') (B : IdempotentImage d N')
    (i : V ⟶ U) (f : RationalSection F M N U) :
    restrict i (A.restrictSection B f) = A.restrictSection B (restrict i f) := by
  simp only [restrictSection, restrict_comp_hom, restrict_ofHom]

theorem baseChange_restrictSection (A : IdempotentImage e M') (B : IdempotentImage d N')
    (φ : R →ₐ[O] S) (f : RationalSection F M N U) :
    baseChange φ U (A.restrictSection B f) =
      (A.map φ).restrictSection (B.map φ) (baseChange φ U f) := by
  simp only [restrictSection, baseChange_comp, baseChange_ofHom]
  rfl

end Langlands.FormalGroup.ModuleLaw.Hom.IdempotentImage
