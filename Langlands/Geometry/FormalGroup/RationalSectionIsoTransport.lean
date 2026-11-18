import Langlands.Geometry.FormalGroup.RationalSectionIso
import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyIsoTransport

/-! # Integral-isomorphism transport of invertible rational sections -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ υ σ' τ' υ' : Type}
variable [Finite σ] [Finite τ] [Finite υ] [Finite σ'] [Finite τ'] [Finite υ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'} {P' : ModuleLaw O R υ'}

namespace RationalSection

/-- Transport preserves the section identity using the same comparison at both ends. -/
@[simp]
theorem transportIso_id (a : Iso M M') (U : Opens (PrimeSpectrum R)) :
    transportIso a a U (id (F := F) M U) = id M' U := by
  change comp (ofHom a.hom U) (comp (id M U) (ofHom a.inv U)) = _
  rw [id_comp, comp_ofHom, a.hom_inv, ofHom_id]

/-- Actual conjugation preserves composition of arbitrary rational sections. -/
theorem transportIso_comp (a : Iso M M') (b : Iso N N') (c : Iso P P')
    {U : Opens (PrimeSpectrum R)} (g : RationalSection F N P U)
    (f : RationalSection F M N U) :
    transportIso a c U (comp g f) =
      comp (transportIso b c U g) (transportIso a b U f) := by
  change comp (ofHom c.hom U) (comp (comp g f) (ofHom a.inv U)) =
    comp (comp (ofHom c.hom U) (comp g (ofHom b.inv U)))
      (comp (ofHom b.hom U) (comp f (ofHom a.inv U)))
  simp only [comp_assoc]
  rw [← comp_assoc (ofHom b.inv U), comp_ofHom, b.inv_hom, ofHom_id, id_comp]

end RationalSection

namespace RationalSectionIso

/-- Transport both actual inverse sections along actual integral isomorphisms. -/
def transportIso {U : Opens (PrimeSpectrum R)} (e : RationalSectionIso F M N U)
    (a : Iso M M') (b : Iso N N') : RationalSectionIso F M' N' U where
  hom := RationalSection.transportIso a b U e.hom
  inv := RationalSection.transportIso b a U e.inv
  inv_hom := by
    rw [← RationalSection.transportIso_comp, e.inv_hom, RationalSection.transportIso_id]
  hom_inv := by
    rw [← RationalSection.transportIso_comp, e.hom_inv, RationalSection.transportIso_id]

@[simp]
theorem transportIso_hom {U : Opens (PrimeSpectrum R)} (e : RationalSectionIso F M N U)
    (a : Iso M M') (b : Iso N N') :
    (e.transportIso a b).hom = RationalSection.transportIso a b U e.hom := rfl

@[simp]
theorem transportIso_inv {U : Opens (PrimeSpectrum R)} (e : RationalSectionIso F M N U)
    (a : Iso M M') (b : Iso N N') :
    (e.transportIso a b).inv = RationalSection.transportIso b a U e.inv := rfl

@[simp]
theorem restrict_transportIso {U V : Opens (PrimeSpectrum R)}
    (e : RationalSectionIso F M N U) (a : Iso M M') (b : Iso N N') (i : V ⟶ U) :
    (e.transportIso a b).restrict i = (e.restrict i).transportIso a b := by
  apply ext
  exact RationalSection.restrict_transportIso a b i e.hom

@[simp]
theorem transportIso_refl (a : Iso M M') (U : Opens (PrimeSpectrum R)) :
    (refl (F := F) M U).transportIso a a = refl M' U := by
  apply ext
  exact RationalSection.transportIso_id a U

@[simp]
theorem transportIso_symm {U : Opens (PrimeSpectrum R)} (e : RationalSectionIso F M N U)
    (a : Iso M M') (b : Iso N N') :
    e.symm.transportIso b a = (e.transportIso a b).symm := rfl

theorem transportIso_trans {U : Opens (PrimeSpectrum R)}
    (e : RationalSectionIso F M N U) (f : RationalSectionIso F N P U)
    (a : Iso M M') (b : Iso N N') (c : Iso P P') :
    (e.trans f).transportIso a c = (e.transportIso a b).trans (f.transportIso b c) := by
  apply ext
  exact RationalSection.transportIso_comp a b c f.hom e.hom

@[simp]
theorem transportIso_symm_transportIso {U : Opens (PrimeSpectrum R)}
    (e : RationalSectionIso F M N U) (a : Iso M M') (b : Iso N N') :
    (e.transportIso a b).transportIso a.symm b.symm = e := by
  apply ext
  exact RationalSection.transportIso_symm_transportIso a b U e.hom

/-- Integral comparisons induce a genuine equivalence on actual invertible sections. -/
def transportIsoEquiv (a : Iso M M') (b : Iso N N') (U : Opens (PrimeSpectrum R)) :
    RationalSectionIso F M N U ≃ RationalSectionIso F M' N' U where
  toFun e := e.transportIso a b
  invFun e := e.transportIso a.symm b.symm
  left_inv e := transportIso_symm_transportIso e a b
  right_inv e := transportIso_symm_transportIso e a.symm b.symm

end RationalSectionIso
end Langlands.FormalGroup.ModuleLaw
