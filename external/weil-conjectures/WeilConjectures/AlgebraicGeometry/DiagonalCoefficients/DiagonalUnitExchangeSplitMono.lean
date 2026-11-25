/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullbackEndpoints
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalSectionUnitSplitMono

/-! # The exchange map is split injective on the adjunction-unit component -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem exchange_unit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {G : C ⥤ C'} {H : D ⥤ D'} (a : L ⊣ R) (b : L' ⊣ R')
    (θ : G ⋙ L' ≅ L ⋙ H) {M : C} {N : D} {Q : D'}
    (e : L.obj M ⟶ N) (d : H.obj N ⟶ Q) :
    G.map (a.unit.app M ≫ R.map e) ≫
        (Adjunction.exchangeRight a b θ).app N ≫ R'.map d =
      b.unit.app (G.obj M) ≫ R'.map (θ.hom.app M ≫ H.map e ≫ d) := by
  have hn := (Adjunction.exchangeRight a b θ).naturality e
  simp only [Functor.comp_map] at hn
  rw [Functor.map_comp, Category.assoc, reassoc_of% hn,
    Adjunction.exchangeRight_app]
  simp only [Category.assoc]
  have hη := b.unit.naturality (G.map (a.unit.app M))
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hη
  rw [reassoc_of% hη]
  simp only [← R'.map_comp]
  have hθ := θ.hom.naturality (a.unit.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hθ
  rw [reassoc_of% hθ]
  rw [← H.map_comp_assoc, a.left_triangle_components, H.map_id, Category.id_comp]

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  CondensedRing.upperStar CondensedRing.lowerStar

/-- On an inverse-image object, canonical exchange composed with the unit is split
injective whenever the new vertical map has a section.

Source: the adjunction-unit component in diagonal coefficients (3)
(blueprint: lem-diagonal-unit-exchange-split-mono).

Proof: naturality of exchange first moves the specified input isomorphism past
exchange. Expand the mate into the new unit, the pullback-square isomorphism and
the old counit. The old triangle identity contracts the old unit and counit.
The result is the new adjunction unit followed by the new direct image of a
composite of isomorphisms. A section of the new vertical morphism splits that unit. -/
theorem diagonalUnitExchange_splitMono
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f) (s' : S' ⟶ X') (hs' : s' ≫ f' = 𝟙 S')
    (M : DerivedCategory (Modules Λ S)) (N : DerivedCategory (Modules Λ X))
    (N' : DerivedCategory (Modules Λ X'))
    (e : (derivedUpper Λ f).obj M ≅ N) (d : (derivedUpper Λ hX).obj N ≅ N') :
    IsSplitMono ((derivedUpper Λ hS).map
        ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).unit.app M ≫
          (derivedLower Λ f).map e.hom) ≫
      (derivedExchange Λ f f' hX hS h).app N ≫ (derivedLower Λ f').map d.hom) := by
  let θ := (CondensedRing.leftDerivedUpperStarComp Λ f' hS).symm ≪≫
    Functor.leftDerivedFunctorNatIso _ (CondensedRing.upperStarCongr Λ h) ≪≫
      CondensedRing.leftDerivedUpperStarComp Λ hX f
  let j : (derivedUpper Λ f').obj ((derivedUpper Λ hS).obj M) ≅ N' :=
    θ.app M ≪≫ (derivedUpper Λ hX).mapIso e ≪≫ d
  dsimp only [derivedUpper, derivedLower] at e d ⊢
  unfold derivedExchange
  dsimp only [derivedUpper, derivedLower]
  rw [exchange_unit]
  exact diagonalSectionUnit_splitMono Λ f' s' hs' ((derivedUpper Λ hS).obj M) N' j

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
