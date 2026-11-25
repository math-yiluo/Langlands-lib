/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedModulePushforwardMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ModuleRegularUnitIso
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierScalars
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierChartAction
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierTranslationAlgebra
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierProjectorDescent
import WeilConjectures.CategoryTheory.CharacterProjectorEvaluation
import WeilConjectures.CategoryTheory.CharacterProjectorAlgebra
import WeilConjectures.CategoryTheory.ConservativeLeftExactFaithful
import WeilConjectures.CategoryTheory.ModuleObjects.ModuleGlobalSectionsMonoidalLinear

/-! # Counit and product identities for the condensed character projectors -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option quotPrecheck false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

private theorem projector_products_of_average
    {C : Type*} [Category C] [Abelian C]
    {K : Type*} [CommRing K] [Linear K C]
    {H : Type*} [AddCommGroup H] [Fintype H] [Invertible (Fintype.card H : K)]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    {P : C} (τ : H → (P ⟶ P)) (hτ : ∀ a b, τ a ≫ τ b = τ (a + b))
    (m : P ⊗ P ⟶ P) (η : 𝟙_ C ⟶ P)
    (hm : ∀ a, m ≫ τ a = (τ a ⊗ₘ τ a) ≫ m)
    (hη : ∀ a, η ≫ τ a = η)
    (e : AddChar H K → (P ⟶ P))
    (he : ∀ χ, e χ = ∑ a : H, (⅟(Fintype.card H : K) * χ (-a)) • τ a)
    (χ χ' : AddChar H K) :
    ((image.ι (e χ) ⊗ₘ image.ι (e χ')) ≫ m) ≫ e (χ * χ') =
        (image.ι (e χ) ⊗ₘ image.ι (e χ')) ≫ m ∧
      η ≫ e 1 = η := by
  have heq : e = fun χ ↦ ∑ a : H, (⅟(Fintype.card H : K) * χ (-a)) • τ a :=
    funext he
  subst e
  exact characterProjector_products_fixed τ hτ m η hm hη χ χ'

namespace AlgebraicGeometry.ProEtale

attribute [local instance] CondensedRing.moduleLowerStarMonoidal

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]
  [Invertible (Fintype.card k : MonObj.Γ Λ)]

local notation "A" => AffineSpace PUnit (Spec (CommRingCat.of k))
local notation "q" => AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)
local notation "F" => CondensedRing.upperStar Λ q
local notation "G" => CondensedRing.lowerStar Λ q
local notation "e" => condensedArtinSchreierProjector Λ k
local notation "τ" => condensedArtinSchreierTranslationAction Λ k
local notation "ρ" => condensedArtinSchreierChartProjection Λ k

-- Concrete linear and monoidal module comparisons need additional elaboration heartbeats.
/-- The character image evaluates to the regular module on the Artin–Schreier cover.

Source: latest blueprint `prop-kernel-lisse.proof.md`, character projector calculation
(blueprint: lem-kernel-condensed-projector-facts).

Proof. Module pullback preserves images and the scalar-weighted finite sum defining the
projector. In the split-cover product chart translations shift the coordinates. The
finite character calculation identifies the image of the pulled-back projector with
the coefficient module by evaluation on the zero coordinate. That coordinate is the
adjunction counit, so the preserved-image comparison gives the asserted counit map. -/
theorem condensedArtinSchreierProjector_evaluation (ψ : AddChar k (MonObj.Γ Λ)) :
    IsIso ((CondensedRing.upperStar Λ q).map (image.ι (e ψ).asHom) ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ q).counit.app
        (Mod.regular (condensedRingObj Λ A))) := by
  classical
  let := Mod.linearOfRingHom (MonObj.Γ.mapFunctor (upperStarFromPoint A) (R := Λ))
  let : (CondensedRing.upperStar Λ q).Linear (MonObj.Γ Λ) :=
    condensedModulePullback_linear Λ q
  have := condensedArtinSchreierChart_isIso Λ k
  have he : (CondensedRing.upperStar Λ q).map (e ψ).asHom =
      ∑ a : k, (⅟(Fintype.card k : MonObj.Γ Λ) * ψ (-a)) •
        (CondensedRing.upperStar Λ q).map (τ a).asHom := by
    rw [condensedArtinSchreierProjector_eq_sum, End.sum_asHom, CategoryTheory.Functor.map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [End.smul_asHom, CategoryTheory.Functor.map_smul]
  have hi : IsIso (image.ι ((CondensedRing.upperStar Λ q).map (e ψ).asHom) ≫ ρ 0) := by
    rw [he]
    exact characterProjector_reindexed_evaluation_isIso ρ (Fintype.card k)
      (Fintype.equivFin k).symm (condensedArtinSchreierChart_isIso Λ k)
      (fun a ↦ (CondensedRing.upperStar Λ q).map (τ a).asHom)
      (condensedArtinSchreierChart_translation Λ k) ψ
  have hh : (CondensedRing.upperStar Λ q).map (image.ι (e ψ).asHom) ≫
      (CondensedRing.upperStarLowerStarAdjunction Λ q).counit.app
        (Mod.regular (condensedRingObj Λ A)) =
      (PreservesImage.iso F (e ψ).asHom).inv ≫
        (image.ι ((CondensedRing.upperStar Λ q).map (e ψ).asHom) ≫ ρ 0) := by
    rw [← Category.assoc, PreservesImage.inv_comp_image_ι_map,
      condensedArtinSchreierChart_zero]
  rw [hh]
  infer_instance

omit [Invertible (Fintype.card k : MonObj.Γ Λ)] in
private theorem translation_add (a b : k) :
    (τ a).asHom ≫ (τ b).asHom = (τ (a + b)).asHom := by
  let := condensedArtinSchreierPullback_reflectsIsomorphisms Λ k
  let := Functor.faithful_of_preservesEqualizers_of_reflectsIsomorphisms F
  have := condensedArtinSchreierChart_isIso Λ k
  apply (CondensedRing.upperStar Λ q).map_injective
  apply (cancel_mono (Pi.lift (fun j : Fin (Fintype.card k) ↦
    ρ ((Fintype.equivFin k).symm j)))).1
  apply Pi.hom_ext
  intro c
  simp only [Category.assoc, Pi.lift_comp_π]
  rw [Functor.map_comp, Category.assoc,
    condensedArtinSchreierChart_translation, condensedArtinSchreierChart_translation,
    condensedArtinSchreierChart_translation, add_assoc, add_comm b a]

-- Concrete linear and monoidal module comparisons need additional elaboration heartbeats.
/-- Products of the two character images and constant functions are fixed by the
appropriate character projectors.

Source: latest blueprint `prop-kernel-lisse.proof.md`, character multiplication
(blueprint: lem-kernel-condensed-projector-facts).

Proof. Restriction to the cover is faithful because it preserves equalizers and reflects
isomorphisms. Its product chart therefore proves the addition law for deck operators.
The deck operators preserve multiplication and constants. Apply the generic character
product calculation using the module category's bilinear tensor product, and identify
the normalized average with the actual defining projector. -/
theorem condensedArtinSchreierProjector_products (ψ ψ' : AddChar k (MonObj.Γ Λ)) :
    (((image.ι (e ψ).asHom ⊗ₘ image.ι (e ψ').asHom) ≫ Functor.LaxMonoidal.μ G
      (Mod.regular (condensedRingObj Λ A)) (Mod.regular (condensedRingObj Λ A)) ≫
      (CondensedRing.lowerStar Λ q).map (Mod.regularMul (condensedRingObj Λ A))) ≫
        (e (ψ * ψ')).asHom =
        (image.ι (e ψ).asHom ⊗ₘ image.ι (e ψ').asHom) ≫ Functor.LaxMonoidal.μ G
      (Mod.regular (condensedRingObj Λ A)) (Mod.regular (condensedRingObj Λ A)) ≫
          (CondensedRing.lowerStar Λ q).map (Mod.regularMul (condensedRingObj Λ A))) ∧
      Functor.LaxMonoidal.ε G ≫ (e 1).asHom = Functor.LaxMonoidal.ε G := by
  classical
  let := Mod.linearOfRingHom (MonObj.Γ.mapFunctor (upperStarFromPoint A) (R := Λ))
  let := Mod.monoidalLinearOfRingHom
    (MonObj.Γ.mapFunctor (upperStarFromPoint A) (R := Λ))
  exact projector_products_of_average (fun a ↦ (τ a).asHom) (translation_add Λ k)
    (Functor.LaxMonoidal.μ G
      (Mod.regular (condensedRingObj Λ A)) (Mod.regular (condensedRingObj Λ A)) ≫
      (CondensedRing.lowerStar Λ q).map (Mod.regularMul (condensedRingObj Λ A)))
    (Functor.LaxMonoidal.ε G)
    (fun a ↦ (condensedArtinSchreierTranslation_algebra Λ k a).1)
    (fun a ↦ (condensedArtinSchreierTranslation_algebra Λ k a).2) (fun χ ↦ (e χ).asHom)
    (fun χ ↦ by
      simpa only [End.sum_asHom, End.smul_asHom] using
        congrArg End.asHom (condensedArtinSchreierProjector_eq_sum Λ k χ)) ψ ψ'

end AlgebraicGeometry.ProEtale
