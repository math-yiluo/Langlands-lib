import Langlands.Geometry.FormalGroup.RationalSectionGlobal

/-! # Invertible actual rational sections and global tensor comparison -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
attribute [local instance] coefficientAlgebra coefficientScalarTower
variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω}

/-- An actual rational Hom sheaf section with an actual two-sided section inverse.
This does not assume or assert the local scalar-isogeny condition. -/
structure RationalSectionIso (F : Type v) [Field F] [Algebra O F]
    (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) (U : Opens (PrimeSpectrum R)) where
  hom : RationalSection F M N U
  inv : RationalSection F N M U
  inv_hom : RationalSection.comp inv hom = RationalSection.id M U
  hom_inv : RationalSection.comp hom inv = RationalSection.id N U

namespace RationalSectionIso
variable {U V W : Opens (PrimeSpectrum R)}

/-- Identity invertible section on every open. -/
def refl (M : ModuleLaw O R σ) (U : Opens (PrimeSpectrum R)) : RationalSectionIso F M M U where
  hom := RationalSection.id M U
  inv := RationalSection.id M U
  inv_hom := RationalSection.id_comp _
  hom_inv := RationalSection.id_comp _

/-- Reverse an actual section isomorphism. -/
def symm (e : RationalSectionIso F M N U) : RationalSectionIso F N M U where
  hom := e.inv
  inv := e.hom
  inv_hom := e.hom_inv
  hom_inv := e.inv_hom

/-- Compose actual invertible sheaf sections. -/
def trans (e : RationalSectionIso F M N U) (f : RationalSectionIso F N P U) :
    RationalSectionIso F M P U where
  hom := RationalSection.comp f.hom e.hom
  inv := RationalSection.comp e.inv f.inv
  inv_hom := by
    rw [RationalSection.comp_assoc, ← RationalSection.comp_assoc f.inv,
      f.inv_hom, RationalSection.id_comp, e.inv_hom]
  hom_inv := by
    rw [RationalSection.comp_assoc, ← RationalSection.comp_assoc e.hom,
      e.hom_inv, RationalSection.id_comp, f.hom_inv]

/-- The actual two-sided section inverse is uniquely determined. -/
theorem inv_unique (e : RationalSectionIso F M N U) (z : RationalSection F N M U)
    (hz : RationalSection.comp z e.hom = RationalSection.id M U) : z = e.inv := by
  calc
    z = RationalSection.comp z (RationalSection.id N U) := (RationalSection.comp_id z).symm
    _ = RationalSection.comp z (RationalSection.comp e.hom e.inv) := by rw [e.hom_inv]
    _ = RationalSection.comp (RationalSection.comp z e.hom) e.inv :=
      (RationalSection.comp_assoc _ _ _).symm
    _ = e.inv := by rw [hz, RationalSection.id_comp]

@[ext]
theorem ext {e f : RationalSectionIso F M N U} (h : e.hom = f.hom) : e = f := by
  have hi : e.inv = f.inv := f.inv_unique e.inv (by rw [← h]; exact e.inv_hom)
  cases e
  cases f
  cases h
  cases hi
  rfl

/-- Restrict the actual inverse together with the actual forward section. -/
def restrict (e : RationalSectionIso F M N U) (i : V ⟶ U) : RationalSectionIso F M N V where
  hom := RationalSection.restrict i e.hom
  inv := RationalSection.restrict i e.inv
  inv_hom := by
    rw [← RationalSection.restrict_comp_hom, e.inv_hom, RationalSection.restrict_id_section]
  hom_inv := by
    rw [← RationalSection.restrict_comp_hom, e.hom_inv, RationalSection.restrict_id_section]

@[simp]
theorem restrict_id (e : RationalSectionIso F M N U) : e.restrict (𝟙 U) = e := by
  apply ext
  exact RationalSection.restrict_id U e.hom

@[simp]
theorem restrict_comp (e : RationalSectionIso F M N U) (i : V ⟶ U) (j : W ⟶ V) :
    e.restrict (j ≫ i) = (e.restrict i).restrict j := by
  apply ext
  exact RationalSection.restrict_comp i j e.hom

@[simp]
theorem restrict_refl (M : ModuleLaw O R σ) (i : V ⟶ U) :
    (refl (F := F) M U).restrict i = refl M V := by
  apply ext
  exact RationalSection.restrict_id_section i

@[simp]
theorem restrict_symm (e : RationalSectionIso F M N U) (i : V ⟶ U) :
    e.symm.restrict i = (e.restrict i).symm := rfl

@[simp]
theorem restrict_trans (e : RationalSectionIso F M N U) (f : RationalSectionIso F N P U)
    (i : V ⟶ U) : (e.trans f).restrict i = (e.restrict i).trans (f.restrict i) := by
  apply ext
  exact RationalSection.restrict_comp_hom i f.hom e.hom

@[simp]
theorem refl_trans (e : RationalSectionIso F M N U) : (refl M U).trans e = e := by
  apply ext
  exact RationalSection.comp_id e.hom

@[simp]
theorem trans_refl (e : RationalSectionIso F M N U) : e.trans (refl N U) = e := by
  apply ext
  exact RationalSection.id_comp e.hom

theorem trans_assoc (e : RationalSectionIso F M N U) (f : RationalSectionIso F N P U)
    (g : RationalSectionIso F P Q U) : (e.trans f).trans g = e.trans (f.trans g) := by
  apply ext
  exact (RationalSection.comp_assoc g.hom f.hom e.hom).symm

@[simp]
theorem symm_symm (e : RationalSectionIso F M N U) : e.symm.symm = e := rfl

@[simp]
theorem self_trans_symm (e : RationalSectionIso F M N U) : e.trans e.symm = refl M U := by
  apply ext
  exact e.inv_hom

@[simp]
theorem symm_trans_self (e : RationalSectionIso F M N U) : e.symm.trans e = refl N U := by
  apply ext
  exact e.hom_inv

/-- Actual integral isomorphisms give actual invertible sections on every open. -/
def ofIso (e : Iso M N) (U : Opens (PrimeSpectrum R)) : RationalSectionIso F M N U where
  hom := RationalSection.ofHom e.hom U
  inv := RationalSection.ofHom e.inv U
  inv_hom := by rw [RationalSection.comp_ofHom, e.inv_hom, RationalSection.ofHom_id]
  hom_inv := by rw [RationalSection.comp_ofHom, e.hom_inv, RationalSection.ofHom_id]

@[simp]
theorem restrict_ofIso (e : Iso M N) (i : V ⟶ U) :
    (ofIso (F := F) e U).restrict i = ofIso e V := by
  apply ext
  exact RationalSection.restrict_ofHom i e.hom

variable [IsDomain O] [IsFractionRing O F]

/-- Map both actual tensors of a global quasi-isogeny into the rational Hom sheaves. -/
def ofQuasiIsogeny (e : QuasiIsogeny F M N) (U : Opens (PrimeSpectrum R)) :
    RationalSectionIso F M N U where
  hom := RationalSection.ofGlobalOn U e.hom
  inv := RationalSection.ofGlobalOn U e.inv
  inv_hom := by rw [← RationalSection.ofGlobalOn_comp, e.inv_hom, RationalSection.ofGlobalOn_id]
  hom_inv := by rw [← RationalSection.ofGlobalOn_comp, e.hom_inv, RationalSection.ofGlobalOn_id]

@[simp]
theorem restrict_ofQuasiIsogeny (e : QuasiIsogeny F M N) (i : V ⟶ U) :
    (ofQuasiIsogeny e U).restrict i = ofQuasiIsogeny e V := by
  apply ext
  exact RationalSection.restrict_ofGlobalOn i e.hom

@[simp]
theorem ofQuasiIsogeny_refl (M : ModuleLaw O R σ) (U : Opens (PrimeSpectrum R)) :
    ofQuasiIsogeny (QuasiIsogeny.refl (F := F) M) U = refl M U := by
  apply ext
  exact RationalSection.ofGlobalOn_id U

@[simp]
theorem ofQuasiIsogeny_symm (e : QuasiIsogeny F M N) (U : Opens (PrimeSpectrum R)) :
    ofQuasiIsogeny e.symm U = (ofQuasiIsogeny e U).symm := rfl

@[simp]
theorem ofQuasiIsogeny_trans (e : QuasiIsogeny F M N) (f : QuasiIsogeny F N P)
    (U : Opens (PrimeSpectrum R)) :
    ofQuasiIsogeny (e.trans f) U = (ofQuasiIsogeny e U).trans (ofQuasiIsogeny f U) := by
  apply ext
  exact RationalSection.ofGlobalOn_comp U f.hom e.hom

@[simp]
theorem ofQuasiIsogeny_ofIso (e : Iso M N) (U : Opens (PrimeSpectrum R)) :
    ofQuasiIsogeny (QuasiIsogeny.ofIso (F := F) e) U = ofIso e U := by
  apply ext
  exact RationalSection.ofGlobalOn_ofHom U e.hom

end RationalSectionIso
end Langlands.FormalGroup.ModuleLaw
