/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.DerivedMorphismDescent
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift

/-!
# Descent of morphisms in the derived category along a surjective étale morphism, up to a shift

Let `u : U ⟶ T` be surjective and étale, and let `Z` with projections `r₁, r₂ : Z ⟶ U` be a
fibre product `U ×_T U`. Morphisms `K ⟶ M` in `D(T_ét, Λ)` between objects which are, up to a
common shift, sheaves placed in degree zero, descend along `u`: a morphism
`δ : Lu^* K ⟶ Lu^* M` whose two pullbacks to `Z` agree is `Lu^* γ` for some `γ : K ⟶ M`.
This reduces to the degree zero case
`AlgebraicGeometry.Etale.exists_leftDerivedUpperStar_map_eq_of_isPullback`.

## Main statements

- `AlgebraicGeometry.Etale.exists_leftDerivedUpperStar_map_eq_of_isPullback_of_shift`: up to a
  common shift.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E] {A : Type*} [AddMonoid A]
  [HasShift C A] [HasShift D A] [HasShift E A] (Φ : C ⥤ D) (Ψ : D ⥤ E) [Φ.CommShift A]
  [Ψ.CommShift A]

/-- A morphism `δ : Φ K ⟶ Φ M`, transported to `Φ (K⟦a⟧) ⟶ Φ (M⟦a⟧)` along the commutation of
`Φ` with the shift, and then mapped by `Ψ`, is `(Ψ δ)⟦a⟧` up to the commutation of `Φ ⋙ Ψ`
with the shift. -/
@[reassoc]
lemma commShiftIso_comp_inv_app_map_shift_comp {K M : C} (δ : Φ.obj K ⟶ Φ.obj M) (a : A) :
    ((Φ ⋙ Ψ).commShiftIso a).inv.app K ≫
        Ψ.map ((Φ.commShiftIso a).hom.app K ≫ δ⟦a⟧' ≫ (Φ.commShiftIso a).inv.app M) ≫
        ((Φ ⋙ Ψ).commShiftIso a).hom.app M = (Ψ.map δ)⟦a⟧' := by
  rw [Functor.commShiftIso_comp_inv_app, Functor.commShiftIso_comp_hom_app, Category.assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp

/-- Conjugating by an isomorphism `τ : Θ ≅ Φ ⋙ Ψ` commuting with the shifts commutes with the
transport of morphisms along the shift. -/
lemma conj_commShiftIso {Θ : C ⥤ E} [Θ.CommShift A] (τ : Θ ≅ Φ ⋙ Ψ) [NatTrans.CommShift τ.hom A]
    {K M : C} (δ : Φ.obj K ⟶ Φ.obj M) (a : A) :
    τ.hom.app (K⟦a⟧) ≫
        Ψ.map ((Φ.commShiftIso a).hom.app K ≫ δ⟦a⟧' ≫ (Φ.commShiftIso a).inv.app M) ≫
        τ.inv.app (M⟦a⟧) =
      (Θ.commShiftIso a).hom.app K ≫ (τ.hom.app K ≫ Ψ.map δ ≫ τ.inv.app M)⟦a⟧' ≫
        (Θ.commShiftIso a).inv.app M := by
  rw [NatTrans.app_shift τ.hom a K, NatTrans.app_shift τ.inv a M]
  simp only [Category.assoc]
  rw [commShiftIso_comp_inv_app_map_shift_comp_assoc]
  simp only [Functor.map_comp, Category.assoc]

end CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Descent of morphisms along a surjective étale morphism, up to a shift.** As
`AlgebraicGeometry.Etale.exists_leftDerivedUpperStar_map_eq_of_isPullback`, for `K, M` whose
shifts `K⟦n⟧, M⟦n⟧` are sheaves placed in degree zero: the derived pullbacks commute with the
shift, compatibly with their composition isomorphisms. -/
theorem Etale.exists_leftDerivedUpperStar_map_eq_of_isPullback_of_shift {T U Z : Scheme.{u}}
    {K M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (n : ℤ)
    (eK : K⟦n⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj F)
    (eM : M⟦n⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj G)
    (u : U ⟶ T) [Etale u] [Surjective u] {r₁ r₂ : Z ⟶ U} (hZ : IsPullback r₁ r₂ u u)
    (δ : (L((u)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ (L((u)^*[ModuleCat.{u + 1} Λ])).obj M)
    (hδ : (leftDerivedUpperStarComp _ r₁ u).hom.app K ≫ (L((r₁)^*[_])).map δ ≫
          (leftDerivedUpperStarComp _ r₁ u).inv.app M =
        (leftDerivedUpperStarComp _ r₂ u (r₁ ≫ u) hZ.w).hom.app K ≫ (L((r₂)^*[_])).map δ ≫
          (leftDerivedUpperStarComp _ r₂ u (r₁ ≫ u) hZ.w).inv.app M) :
    ∃ γ : K ⟶ M, (L((u)^*[ModuleCat.{u + 1} Λ])).map γ = δ := by
  let Φ := L((u)^*[ModuleCat.{u + 1} Λ])
  let δ' := (Φ.commShiftIso n).hom.app K ≫ δ⟦n⟧' ≫ (Φ.commShiftIso n).inv.app M
  -- The degree zero statement is elaborated with Mathlib's `IsGrothendieckAbelian (ModuleCat Λ)`
  -- instance, this file with the shortcut `ModuleCat.isGrothendieckAbelian_of_commRing`. The two
  -- instances are proofs of the same proposition, but the kernel unfolds
  -- `DerivedCategory.singleFunctor` to identify `(singleFunctor _ 0).obj F` for them. Transporting
  -- `eK` and `eM` along an equality abstracted over the instance avoids this.
  have e : ∀ X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ), _ := fun X ↦
    eq_of_heq (congr_arg_heq (a₁ := ModuleCat.isGrothendieckAbelian_of_commRing Λ)
      (a₂ := instIsGrothendieckAbelianModuleCat Λ)
      (fun [IsGrothendieckAbelian.{u + 1} (ModuleCat.{u + 1} Λ)] ↦
        (DerivedCategory.singleFunctor (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj X)
      (proof_irrel _ _))
  obtain ⟨γ', hγ'⟩ := Etale.exists_leftDerivedUpperStar_map_eq_of_isPullback
    (eK ≪≫ eqToIso (e F)) (eM ≪≫ eqToIso (e G)) u hZ δ' (by
    rw [Functor.conj_commShiftIso _ _ (leftDerivedUpperStarComp _ r₁ u) δ n,
      Functor.conj_commShiftIso _ _ (leftDerivedUpperStarComp _ r₂ u (r₁ ≫ u) hZ.w) δ n, hδ])
  refine ⟨(shiftFunctor _ n).preimage γ', (shiftFunctor _ n).map_injective ?_⟩
  have h := Φ.commShiftIso_hom_naturality ((shiftFunctor _ n).preimage γ') n
  rw [Functor.map_preimage, hγ'] at h
  rw [← cancel_epi ((Φ.commShiftIso n).hom.app K), ← h]
  simp only [δ', Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

end AlgebraicGeometry
