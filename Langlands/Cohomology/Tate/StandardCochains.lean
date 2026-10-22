import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R G : Type u} [CommRing R] [Group G]

/-- Precomposition with Mathlib's actual standard-to-bar comparison. -/
def cochainsBarStandardEquiv (A : Rep.{u} R G) (n : ℕ) :
    ((Rep.barComplex R G).X n ⟶ A) ≃ₗ[R] ((Rep.standardComplex R G).X n ⟶ A) where
  toFun f := (Rep.barComplex.isoStandardComplex R G).inv.f n ≫ f
  invFun f := (Rep.barComplex.isoStandardComplex R G).hom.f n ≫ f
  left_inv f := by
    dsimp only
    rw [← Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
      HomologicalComplex.id_f, Category.id_comp]
  right_inv f := by
    dsimp only
    rw [← Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
      HomologicalComplex.id_f, Category.id_comp]
  map_add' f g := Preadditive.comp_add _ _ _ _ f g
  map_smul' r f := by simp only [Linear.comp_smul, RingHom.id_apply]

/-- The induced isomorphism of actual Hom complexes. -/
def cochainsBarStandardIso (A : Rep.{u} R G) :
    (Rep.barComplex R G).linearYonedaObj R A ≅
      (Rep.standardComplex R G).linearYonedaObj R A :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (cochainsBarStandardEquiv A n).toModuleIso) (fun n m h => by
      obtain rfl : n + 1 = m := h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      change (Rep.standardComplex R G).d (n + 1) n ≫
          (Rep.barComplex.isoStandardComplex R G).inv.f n ≫ f =
        (Rep.barComplex.isoStandardComplex R G).inv.f (n + 1) ≫
          (Rep.barComplex R G).d (n + 1) n ≫ f
      rw [← Category.assoc, ← Category.assoc,
        (Rep.barComplex.isoStandardComplex R G).inv.comm (n + 1) n])

/-- Mathlib's inhomogeneous cochains identified with the actual standard Hom complex. -/
def cochainsIsoStandard (A : Rep.{u} R G) :
    groupCohomology.inhomogeneousCochains A ≅
      (Rep.standardComplex R G).linearYonedaObj R A :=
  groupCohomology.inhomogeneousCochainsIso A ≪≫ cochainsBarStandardIso A

end Langlands.Tate
