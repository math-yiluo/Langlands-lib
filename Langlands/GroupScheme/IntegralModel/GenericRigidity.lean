import Langlands.GroupScheme.IntegralModel.Iso
import Langlands.GroupScheme.IntegralModel.BaseChangeCoefficientHom
import Langlands.AbelianScheme.RelativeHomNeronExtension

/-! # Generic rigidity and compatible isomorphisms of supplied integral models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  {M : IntegralModel R K G} {N : IntegralModel R K H}

/-- Morphisms of the actual flat affine models are determined by their generic fibres. -/
theorem hom_eq_of_generic {φ ψ : M.group ⟶ N.group}
    (h : (GroupScheme.baseChange (Spec.algebraMap R K)).map φ =
      (GroupScheme.baseChange (Spec.algebraMap R K)).map ψ) : φ = ψ := by
  apply Grp.hom_ext
  exact Langlands.AbelianScheme.genericFibre_map_injective K
    (congrArg (fun f => f.hom.hom) h)

/-- A specified generic morphism has at most one compatible extension. -/
theorem Hom.hom_eq {f : G ⟶ H} (φ ψ : M.Hom N f) : φ.hom = ψ.hom := by
  apply hom_eq_of_generic
  apply (cancel_mono N.genericIso.hom).mp
  exact φ.generic_comm.trans ψ.generic_comm.symm

instance {f : G ⟶ H} : Subsingleton (M.Hom N f) where
  allEq φ ψ := by
    have h := φ.hom_eq ψ
    cases φ
    cases ψ
    cases h
    rfl

namespace Iso

variable {f : G ≅ H}

/-- Opposite extensions of a generic isomorphism are automatically inverse. -/
def ofHoms (φ : M.Hom N f.hom) (ψ : N.Hom M f.inv) : M.Iso N f where
  iso :=
    { hom := φ.hom
      inv := ψ.hom
      hom_inv_id := by
        apply hom_eq_of_generic
        apply (cancel_mono M.genericIso.hom).mp
        rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, Category.id_comp,
          Category.assoc, ψ.generic_comm, ← Category.assoc, φ.generic_comm,
          Category.assoc, f.hom_inv_id, Category.comp_id]
      inv_hom_id := by
        apply hom_eq_of_generic
        apply (cancel_mono N.genericIso.hom).mp
        rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, Category.id_comp,
          Category.assoc, φ.generic_comm, ← Category.assoc, ψ.generic_comm,
          Category.assoc, f.inv_hom_id, Category.comp_id] }
  generic_comm := φ.generic_comm

@[simp] theorem ofHoms_hom (φ : M.Hom N f.hom) (ψ : N.Hom M f.inv) :
    (ofHoms φ ψ).iso.hom = φ.hom := rfl

@[simp] theorem ofHoms_inv (φ : M.Hom N f.hom) (ψ : N.Hom M f.inv) :
    (ofHoms φ ψ).iso.inv = ψ.hom := rfl

/-- The original point images coincide when the identity extends in both directions. -/
theorem integralPoints_eq_of_identityHoms {N : IntegralModel R K G}
    (φ : M.Hom N (𝟙 G)) (ψ : N.Hom M (𝟙 G)) :
    M.integralPoints = N.integralPoints :=
  (ofHoms (f := CategoryTheory.Iso.refl G) φ ψ).integralPoints_eq

variable (e : M.Iso N f)
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]

/-- Base change of a compatible model isomorphism over the actual coefficient square. -/
def baseChangeCoefficients :
    (M.baseChange A L).Iso (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).mapIso f) where
  iso := (GroupScheme.baseChange (Spec.algebraMap R A)).mapIso e.iso
  generic_comm := (e.toHom.baseChangeCoefficients A L).generic_comm

@[simp] theorem baseChangeCoefficients_hom :
    (e.baseChangeCoefficients A L).iso.hom =
      (GroupScheme.baseChange (Spec.algebraMap R A)).map e.iso.hom := rfl

@[simp] theorem baseChangeCoefficients_inv :
    (e.baseChangeCoefficients A L).iso.inv =
      (GroupScheme.baseChange (Spec.algebraMap R A)).map e.iso.inv := rfl

end Iso

end Langlands.GroupScheme.IntegralModel
