import Langlands.AlgebraicGeometry.FiniteFreeSchemeActionRelation
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Free finite group actions on affine schemes from ring actions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SpecRingAction

variable {Γ : Type u} [Group Γ] {B : Type u} [CommRing B]

/-- The scheme automorphism of `Spec B` induced by a ring automorphism. -/
def specIso (e : B ≃+* B) : Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of B) where
  hom := Spec.map (CommRingCat.ofHom e.toRingHom)
  inv := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    simp
  inv_hom_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    simp

/-- A group action on a ring by automorphisms gives an action on its spectrum,
which is free when no nontrivial group element fixes a field-valued point. -/
def finiteFreeSchemeAction (σ : Γ →* (B ≃+* B))
    (hfree : ∀ (K : Type u) [Field K] (φ : B →+* K) (g h : Γ),
      φ.comp (σ g).toRingHom = φ.comp (σ h).toRingHom → g = h) :
    FiniteFreeSchemeAction Γ (Spec (CommRingCat.of B)) where
  act g := specIso (σ g)
  one := by
    change Spec.map (CommRingCat.ofHom (σ 1).toRingHom) = _
    rw [map_one, ← Spec.map_id]
    rfl
  mul g h := by
    change Spec.map (CommRingCat.ofHom (σ g).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (σ h).toRingHom) = Spec.map (CommRingCat.ofHom (σ (g * h)).toRingHom)
    rw [← Spec.map_comp, map_mul]
    rfl
  free := by
    intro T _ a g h hgh
    obtain ⟨t⟩ := (inferInstance : Nonempty T)
    let p := T.fromSpecResidueField t
    have h1 : (p ≫ a) ≫ (specIso (σ g)).hom = (p ≫ a) ≫ (specIso (σ h)).hom := by
      simp only [Category.assoc]
      exact congrArg (p ≫ ·) hgh
    obtain ⟨φ, hφ⟩ : ∃ φ : CommRingCat.of B ⟶ T.residueField t, Spec.map φ = p ≫ a :=
      ⟨Spec.preimage (p ≫ a), Spec.map_preimage _⟩
    rw [← hφ] at h1
    change Spec.map φ ≫ Spec.map (CommRingCat.ofHom (σ g).toRingHom) =
      Spec.map φ ≫ Spec.map (CommRingCat.ofHom (σ h).toRingHom) at h1
    rw [← Spec.map_comp, ← Spec.map_comp] at h1
    have h2 := Spec.map_injective h1
    apply hfree (T.residueField t) φ.hom g h
    have := congrArg CommRingCat.Hom.hom h2
    simpa using this

end Langlands.AlgebraicGeometry.SpecRingAction
