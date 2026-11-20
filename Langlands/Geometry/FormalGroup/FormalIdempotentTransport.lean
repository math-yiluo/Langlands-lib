import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyIsoTransport
import Langlands.Geometry.FormalGroup.RationalIdempotentImage
import Langlands.Geometry.FormalGroup.RelativeFrobenius

/-! # Transport of formal idempotent images through coordinates and Frobenius -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open TopologicalSpace

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ σ' τ' υ υ' : Type}
variable [Finite σ] [Finite τ] [Finite σ'] [Finite τ'] [Finite υ] [Finite υ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}
variable {L : ModuleLaw O R υ} {L' : ModuleLaw O R υ'}

namespace Hom

/-- Relative Frobenius commutes with actual formal module homomorphisms. -/
theorem frobeniusHom_natural (f : Hom M N) (p m : ℕ) [ExpChar R p] (θ : R →ₐ[O] R)
    (hθ : θ.toRingHom = iterateFrobenius R p m) :
    (N.frobeniusHom p m θ hθ).comp f = (f.map θ).comp (M.frobeniusHom p m θ hθ) := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  change (CoordinateMap.frobeniusPow p m).comp f.toHom.toCoordinateMap =
    (f.toHom.toCoordinateMap.map θ.toRingHom).comp (CoordinateMap.frobeniusPow p m)
  rw [hθ]
  exact CoordinateMap.frobeniusPow_natural p m _

namespace IdempotentImage

variable {e : Hom M M} {d : Hom N N} {e' : Hom M' M'} {d' : Hom N' N'}

/-- Transport the coordinate presentation when the ambient projector is conjugated. -/
def transport (A : IdempotentImage e L) (a : Iso M M')
    (ha : a.hom.comp e = e'.comp a.hom) : IdempotentImage e' L where
  inclusion := a.hom.comp A.inclusion
  projection := A.projection.comp a.inv
  projection_inclusion := by
    rw [comp_assoc, ← comp_assoc a.inv, a.inv_hom, id_comp, A.projection_inclusion]
  inclusion_projection := by
    rw [← comp_assoc (a.hom.comp A.inclusion), comp_assoc a.hom A.inclusion,
      A.inclusion_projection, ha, comp_assoc, a.hom_inv, comp_id]

variable {F : Type v} [Field F] [Algebra O F] {U : Opens (PrimeSpectrum R)}

/-- Ambient conjugation cancels against the inclusion and projection of the transported images. -/
theorem restrictSection_transportIso (A : IdempotentImage e L) (B : IdempotentImage d L')
    (a : Iso M M') (b : Iso N N')
    (ha : a.hom.comp e = e'.comp a.hom) (hb : b.hom.comp d = d'.comp b.hom)
    (f : RationalSection F M N U) :
    (A.transport a ha).restrictSection (B.transport b hb)
      (RationalSection.transportIso a b U f) = A.restrictSection B f := by
  change RationalSection.comp (RationalSection.ofHom (B.projection.comp b.inv) U)
    (RationalSection.comp
      (RationalSection.comp (RationalSection.ofHom b.hom U)
        (RationalSection.comp f (RationalSection.ofHom a.inv U)))
      (RationalSection.ofHom (a.hom.comp A.inclusion) U)) = _
  simp only [← RationalSection.comp_ofHom, RationalSection.comp_assoc]
  rw [← RationalSection.comp_assoc (RationalSection.ofHom b.inv U), RationalSection.comp_ofHom,
    b.inv_hom, RationalSection.ofHom_id, RationalSection.id_comp,
    ← RationalSection.comp_assoc (RationalSection.ofHom a.inv U), RationalSection.comp_ofHom,
    a.inv_hom, RationalSection.ofHom_id, RationalSection.id_comp]
  rfl

/-- Restriction of ambient relative Frobenius is relative Frobenius of the image law. -/
theorem restrictHom_frobeniusHom (A : IdempotentImage e L)
    (p m : ℕ) [ExpChar R p] (θ : R →ₐ[O] R)
    (hθ : θ.toRingHom = iterateFrobenius R p m) :
    A.restrictHom (A.map θ) (M.frobeniusHom p m θ hθ) = L.frobeniusHom p m θ hθ := by
  change (A.projection.map θ).comp ((M.frobeniusHom p m θ hθ).comp A.inclusion) = _
  rw [A.inclusion.frobeniusHom_natural p m θ hθ, ← comp_assoc, ← map_comp,
    A.projection_inclusion, map_id, id_comp]

end IdempotentImage

end Hom

end Langlands.FormalGroup.ModuleLaw
