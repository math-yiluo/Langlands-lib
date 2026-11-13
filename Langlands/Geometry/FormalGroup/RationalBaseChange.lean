import Langlands.Geometry.FormalGroup.CoefficientCoherence

/-! # Coefficient extension of formal module isomorphisms and quasi-isogenies -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {S : Type w} [CommRing S] [Algebra O S]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

namespace Iso

/-- The inverse of an integral isomorphism is unique. -/
theorem inv_unique (f : Iso M N) (g : Hom N M) (h : g.comp f.hom = Hom.id M) :
    g = f.inv := by
  calc
    g = g.comp (Hom.id N) := (Hom.comp_id g).symm
    _ = g.comp (f.hom.comp f.inv) := by rw [f.hom_inv]
    _ = (g.comp f.hom).comp f.inv := (Hom.comp_assoc _ _ _).symm
    _ = f.inv := by rw [h, Hom.id_comp]

/-- Compatibility name for equality detected by the forward integral map. -/
@[ext]
theorem ext {f g : Iso M N} (h : f.hom = g.hom) : f = g := ext_hom h

@[simp]
theorem map_refl (φ : R →ₐ[O] S) :
    (refl M).map φ = refl (M.map φ) := by
  apply ext
  exact Hom.map_id φ

@[simp]
theorem map_symm (φ : R →ₐ[O] S) (f : Iso M N) :
    f.symm.map φ = (f.map φ).symm := rfl

@[simp]
theorem map_trans (φ : R →ₐ[O] S) (f : Iso M N) (g : Iso N P) :
    (f.trans g).map φ = (f.map φ).trans (g.map φ) := by
  apply ext
  exact Hom.map_comp φ g.hom f.hom

end Iso

namespace QuasiIsogeny

variable {F : Type*} [Field F] [Algebra O F] [IsDomain O] [IsFractionRing O F]

/-- Compatibility name for equality detected by the forward rational map. -/
@[ext]
theorem ext {f g : QuasiIsogeny F M N} (h : f.hom = g.hom) : f = g := ext_hom h

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw
