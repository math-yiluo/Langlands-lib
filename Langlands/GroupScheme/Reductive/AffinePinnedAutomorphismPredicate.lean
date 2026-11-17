import Langlands.GroupScheme.Reductive.AffinePinnedModel
import Langlands.GroupScheme.Lie.KernelTargetMaps

/-! # The exact based and pinned automorphism predicates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffinePinnedModel

variable (M : AffinePinnedModel.{u})

/-- Automorphisms of the full root datum that preserve the chosen simple roots. -/
def basedAutomorphisms : Subgroup (RootPairing.Aut M.rootDatum) where
  carrier θ := ∀ j, j ∈ M.basis.support ↔ θ.indexEquiv j ∈ M.basis.support
  one_mem' j := Iff.rfl
  mul_mem' hθ hψ j := (hψ j).trans (hθ _)
  inv_mem' {θ} hθ j := by
    change j ∈ M.basis.support ↔ θ.indexEquiv.symm j ∈ M.basis.support
    simpa only [Equiv.apply_symm_apply] using (hθ (θ.indexEquiv.symm j)).symm

/-- The exact torus, character and simple-vector predicate of the published
affine pinned automorphism group statement, on a supplied pinned model. -/
def IsPinnedAutomorphism (σ : CategoryTheory.Aut M.group)
    (θ : RootPairing.Aut M.rootDatum) : Prop :=
  ∃ hθ : θ ∈ M.basedAutomorphisms,
    (∃ τ : splitTorus M.base M.coordinates ≅ splitTorus M.base M.coordinates,
      M.inclusion ≫ σ.hom = τ.hom ≫ M.inclusion ∧
      ∀ (U : Over M.base) (x : U ⟶ (splitTorus M.base M.coordinates).X)
        (m : M.coordinates → ℤ),
        ∏ j, splitTorus.pointsEquiv M.coordinates U (x ≫ τ.hom.hom.hom) j ^
            θ.weightMap m j =
          ∏ j, splitTorus.pointsEquiv M.coordinates U x j ^ m j) ∧
    ∀ a : M.basis.support,
      Lie.targetMapLinear σ.hom (CommRingCat.of M.ring) (M.pinning a 1).val =
        (M.pinning ⟨θ.indexEquiv a, (hθ a).mp a.property⟩ 1).val

theorem IsPinnedAutomorphism.based {σ : CategoryTheory.Aut M.group}
    {θ : RootPairing.Aut M.rootDatum} (h : M.IsPinnedAutomorphism σ θ) :
    θ ∈ M.basedAutomorphisms :=
  h.choose

private theorem targetMapLinear_id (v : Additive (lieKernel M.group M.ring)) :
    Lie.targetMapLinear (𝟙 M.group) (CommRingCat.of M.ring) v = v := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change v.toMul.val ≫ (𝟙 M.group : M.group ⟶ M.group).hom.hom = v.toMul.val
  rw [Grp.id_hom_hom, Category.comp_id]

private theorem targetMapLinear_mul (σ ρ : CategoryTheory.Aut M.group)
    (v : Additive (lieKernel M.group M.ring)) :
    Lie.targetMapLinear (σ * ρ).hom (CommRingCat.of M.ring) v =
      Lie.targetMapLinear σ.hom (CommRingCat.of M.ring)
        (Lie.targetMapLinear ρ.hom (CommRingCat.of M.ring) v) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change v.toMul.val ≫ (ρ.hom ≫ σ.hom).hom.hom =
    (v.toMul.val ≫ ρ.hom.hom.hom) ≫ σ.hom.hom.hom
  rw [Grp.comp_hom_hom, Category.assoc]

/-- The identity automorphism has identity label and preserves the pinning. -/
theorem isPinnedAutomorphism_one : M.IsPinnedAutomorphism 1 1 := by
  refine ⟨M.basedAutomorphisms.one_mem, ⟨Iso.refl _, ?_, ?_⟩, ?_⟩
  · change M.inclusion ≫ 𝟙 M.group = 𝟙 _ ≫ M.inclusion
    simp
  · intro U x m
    simp
  · intro a
    exact M.targetMapLinear_id _

/-- Products use the covariant root-datum convention of the target statement. -/
theorem IsPinnedAutomorphism.mul {σ ρ : CategoryTheory.Aut M.group}
    {θ ψ : RootPairing.Aut M.rootDatum}
    (hσ : M.IsPinnedAutomorphism σ θ) (hρ : M.IsPinnedAutomorphism ρ ψ) :
    M.IsPinnedAutomorphism (σ * ρ) (θ * ψ) := by
  obtain ⟨hθ, ⟨τ, hτ, hτχ⟩, hσX⟩ := hσ
  obtain ⟨hψ, ⟨υ, hυ, hυχ⟩, hρX⟩ := hρ
  refine ⟨M.basedAutomorphisms.mul_mem hθ hψ, ⟨υ ≪≫ τ, ?_, ?_⟩, ?_⟩
  · change M.inclusion ≫ (ρ.hom ≫ σ.hom) = (υ.hom ≫ τ.hom) ≫ M.inclusion
    rw [← Category.assoc, hυ, Category.assoc, hτ, ← Category.assoc]
  · intro U x m
    simp only [Iso.trans_hom, Grp.comp_hom_hom, ← Category.assoc]
    change
      (∏ j, splitTorus.pointsEquiv M.coordinates U
        ((x ≫ υ.hom.hom.hom) ≫ τ.hom.hom.hom) j ^
          θ.weightMap (ψ.weightMap m) j) =
        ∏ j, splitTorus.pointsEquiv M.coordinates U x j ^ m j
    rw [hτχ, hυχ]
  · intro a
    rw [M.targetMapLinear_mul, hρX a, hσX]
    rfl

end Langlands.GroupScheme.AffinePinnedModel
