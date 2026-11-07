import Langlands.Geometry.Building.KPApartment
import Langlands.GroupScheme.Reductive.RootDatumGaloisRoots

/-! # Actual Galois actions on reduced apartment translations -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.GroupScheme.RealTorusSpace

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

local notation "T_K" =>
  CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T

/-- Real scalar extension of the actual cocharacter Galois representation.
The original torus need not be split. -/
def galoisCocharacterAction : (K ≃ₐ[k] K) →* (V T_K ≃ₗ[ℝ] V T_K) where
  toFun σ := LinearEquiv.baseChange ℤ ℝ _ _ (cocharacterLattice.galoisEquiv k K T σ)
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    apply AlgebraTensorModule.ext
    intro r ν
    change r ⊗ₜ[ℤ] (cocharacterLattice.galoisRepresentation k K T 1 ν) = r ⊗ₜ[ℤ] ν
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply LinearEquiv.toLinearMap_injective
    apply AlgebraTensorModule.ext
    intro r ν
    change r ⊗ₜ[ℤ] (cocharacterLattice.galoisRepresentation k K T (σ * τ) ν) =
      r ⊗ₜ[ℤ] (cocharacterLattice.galoisRepresentation k K T σ
        (cocharacterLattice.galoisRepresentation k K T τ ν))
    rw [map_mul]
    rfl

@[simp] theorem galoisCocharacterAction_tmul (σ : K ≃ₐ[k] K)
    (r : ℝ) (ν : cocharacterLattice T_K) :
    galoisCocharacterAction k K T σ (r ⊗ₜ[ℤ] ν) =
      r ⊗ₜ[ℤ] cocharacterLattice.galoisRepresentation k K T σ ν := rfl

/-- Simultaneous actual character and real cocharacter transport preserves
evaluation. -/
theorem eval_galoisCocharacterAction (σ : K ≃ₐ[k] K)
    (χ : characterLattice T_K) (v : V T_K) :
    eval T_K (characterLattice.galoisRepresentation k K T σ χ)
        (galoisCocharacterAction k K T σ v) = eval T_K χ v := by
  induction v using TensorProduct.inductionOn with
  | tmul r ν =>
    rw [galoisCocharacterAction_tmul, eval_tmul, eval_tmul,
      latticePairing_galoisRepresentation]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- Moving actual coefficient transport from a vector to a character
introduces the inverse coefficient automorphism. -/
theorem eval_galoisCocharacterAction_right (σ : K ≃ₐ[k] K)
    (χ : characterLattice T_K) (v : V T_K) :
    eval T_K χ (galoisCocharacterAction k K T σ v) =
      eval T_K (characterLattice.galoisRepresentation k K T σ⁻¹ χ) v := by
  have h := eval_galoisCocharacterAction k K T σ
    (characterLattice.galoisRepresentation k K T σ⁻¹ χ) v
  simpa only [Representation.self_inv_apply] using h

end Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- Ordinary coefficient transport permutes the actual relative roots of a
descended torus map. -/
def galoisRootAction : (K ≃ₐ[k] K) →* Equiv.Perm (relativeRoots (T := T_K) i_K) where
  toFun σ := Equiv.subtypeEquiv (characterLattice.galoisEquiv k K T σ).toEquiv
    (fun χ => (mem_roots_galois_iff k K i σ χ).symm)
  map_one' := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    change characterLattice.galoisRepresentation k K T 1 a.val = a.val
    exact LinearMap.congr_fun (map_one (characterLattice.galoisRepresentation k K T)) a.val
  map_mul' σ τ := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    change characterLattice.galoisRepresentation k K T (σ * τ) a.val =
      characterLattice.galoisRepresentation k K T σ
        (characterLattice.galoisRepresentation k K T τ a.val)
    exact LinearMap.congr_fun (map_mul (characterLattice.galoisRepresentation k K T) σ τ) a.val

@[simp] theorem galoisRootAction_val (σ : K ≃ₐ[k] K) (a : relativeRoots (T := T_K) i_K) :
    (galoisRootAction k K i σ a).val =
      characterLattice.galoisRepresentation k K T σ a.val := rfl

/-- Actual cocharacter coefficient transport preserves the full common
annihilator of the upstairs roots. -/
theorem galoisCocharacterAction_mem_rootAnnihilator (σ : K ≃ₐ[k] K)
    {v : V T_K} (hv : v ∈ rootAnnihilator (S := T_K) i_K) :
    galoisCocharacterAction k K T σ v ∈ rootAnnihilator (S := T_K) i_K := by
  rw [mem_rootAnnihilator] at hv ⊢
  intro χ hχ
  rw [eval_galoisCocharacterAction_right]
  exact hv _ ((mem_roots_galois_iff k K i σ⁻¹ χ).mpr hχ)

/-- The root annihilator maps onto itself, including the full central
directions. -/
theorem map_galoisCocharacterAction_rootAnnihilator (σ : K ≃ₐ[k] K) :
    (rootAnnihilator (S := T_K) i_K).map
        (galoisCocharacterAction k K T σ : V T_K →ₗ[ℝ] V T_K) =
      rootAnnihilator (S := T_K) i_K := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact galoisCocharacterAction_mem_rootAnnihilator k K i σ hv
  · intro v hv
    refine ⟨galoisCocharacterAction k K T σ⁻¹ v,
      galoisCocharacterAction_mem_rootAnnihilator k K i σ⁻¹ hv, ?_⟩
    change (galoisCocharacterAction k K T σ *
      galoisCocharacterAction k K T σ⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

/-- The actual coefficient action descends to the existing reduced
translation space of the upstairs torus map. -/
def galoisTranslationAction :
    (K ≃ₐ[k] K) →* (TranslationSpace (S := T_K) i_K ≃ₗ[ℝ] TranslationSpace (S := T_K) i_K) where
  toFun σ := Submodule.Quotient.equiv _ _ (galoisCocharacterAction k K T σ)
    (map_galoisCocharacterAction_rootAnnihilator k K i σ)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    refine Submodule.Quotient.induction_on _ v fun w => ?_
    change Submodule.Quotient.mk (galoisCocharacterAction k K T 1 w) =
      Submodule.Quotient.mk w
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply LinearEquiv.ext
    intro v
    refine Submodule.Quotient.induction_on _ v fun w => ?_
    change Submodule.Quotient.mk (galoisCocharacterAction k K T (σ * τ) w) =
      Submodule.Quotient.mk (galoisCocharacterAction k K T σ
        (galoisCocharacterAction k K T τ w))
    rw [map_mul, LinearEquiv.mul_apply]

@[simp] theorem galoisTranslationAction_mk (σ : K ≃ₐ[k] K) (v : V T_K) :
    galoisTranslationAction k K i σ (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (galoisCocharacterAction k K T σ v) := rfl

/-- The existing actual root forms are covariant under the constructed
coefficient actions on roots and reduced translations. -/
theorem rootForm_galoisTranslationAction (σ : K ≃ₐ[k] K)
    (a : relativeRoots (T := T_K) i_K) (v : TranslationSpace (S := T_K) i_K) :
    rootForm (S := T_K) i_K (galoisRootAction k K i σ a)
        (galoisTranslationAction k K i σ v) = rootForm (S := T_K) i_K a v := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  exact eval_galoisCocharacterAction k K T σ a.val w

end Langlands.Geometry.Building
