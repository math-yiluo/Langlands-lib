/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.CategoryTheory.Triangulated.ReductionTriangleMate

/-!
# Exceptional inverse images from pullbacks along natural reduction triangles

Keep the setting of `WeilConjectures.CategoryTheory.Triangulated.ReductionTriangleMate`: two
levels `A_Y, A_Z` (integral coefficients) and `N_Y, N_Z` (reduced coefficients), adjunctions
`red ⊣ Res` whose monads carry natural reduction triangles `M --k--> M --η--> Res (red M) --δ-->`,
adjunctions `G ⊣ F` and `G' ⊣ F'` (typically `G = Lg^*`, `F = Rg_*`), a pullback comparison
`β : G ⋙ red_Z ≅ red_Y ⋙ G'` (Pull) and `ι : Res_Y ⋙ G ≅ G' ⋙ Res_Z` compatible with the units
and the connecting morphisms. Then the pushforward comparison `γ : F ⋙ red_Y ⟶ red_Z ⋙ F'`, the
mate of `β⁻¹`, is an isomorphism (`CategoryTheory.isIso_mateEquiv_of_reductionTriangle`).

Suppose moreover that `F` and `F'` are left adjoints, `F ⊣ H` and `F' ⊣ H'` (typically `g` proper,
`F = Rg_* = Rg_!` and `H = Rg^!`). This file shows that the exceptional comparison
`H ⋙ red_Z ⟶ red_Y ⋙ H'`, the mate of `γ⁻¹` under `F ⊣ H` and `F' ⊣ H'`, is an isomorphism as
well (`CategoryTheory.isIso_mateEquiv_mateEquiv_of_reductionTriangle`). Indeed, the compatibilities
of (Pull) with the units and the connecting morphisms transpose to the same compatibilities of
`γ`, with the conjugate `F' ⋙ Res_Y ≅ Res_Z ⋙ F` of `β` in place of `ι`
(`CategoryTheory.unit_comp_map_reductionComparison`,
`CategoryTheory.map_reductionComparison_comp_δ`), so that
`CategoryTheory.isIso_mateEquiv_of_reductionTriangle` applies a second time, to `F ⊣ H`.

No information on `H` is needed beyond its being a triangulated right adjoint of `F` compatible
with the shifts: this is the formal part of blueprint
`lemma-change-coefficients-exceptional-inverse-image` for a coefficient change whose monad is the
cone of a scalar (the reduction `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`).
-/

@[expose] public section

namespace CategoryTheory

open Limits Category Pretriangulated

section ReductionTriangle

variable {AY AZ NY NZ : Type*} [Category* AY] [Category* AZ] [Category* NY] [Category* NZ]
  {redY : AY ⥤ NY} {resY : NY ⥤ AY} (adjY : redY ⊣ resY)
  {redZ : AZ ⥤ NZ} {resZ : NZ ⥤ AZ} (adjZ : redZ ⊣ resZ)
  {G : AY ⥤ AZ} {F : AZ ⥤ AY} (adj : G ⊣ F)
  {G' : NY ⥤ NZ} {F' : NZ ⥤ NY} (adj' : G' ⊣ F')
  (β : G ⋙ redZ ≅ redY ⋙ G') (ι : resY ⋙ G ≅ G' ⋙ resZ)

/-- The conjugate `F' ⋙ Res_Y ⟶ Res_Z ⋙ F` of the pullback comparison `β` is an isomorphism. -/
instance isIso_conjugateEquiv_reductionComparison :
    IsIso (conjugateEquiv (adjY.comp adj') (adj.comp adjZ) β.hom) :=
  conjugateEquiv_iso _ _ _

/-- **The units transpose to the pushforward.** If `ι` is compatible with the units, then the
pushforward comparison `γ_K`, read through `Res_Y`, is compatible with the units, the
commutation of `Res` with `F` being the inverse of the conjugate of `β`. -/
lemma map_unit_comp_inv_conjugateEquiv_app
    (hι : ∀ M, G.map (adjY.unit.app M) ≫ ι.hom.app (redY.obj M) =
      adjZ.unit.app (G.obj M) ≫ resZ.map (β.hom.app M)) (K : AZ) :
    F.map (adjZ.unit.app K) ≫
        inv ((conjugateEquiv (adjY.comp adj') (adj.comp adjZ) β.hom).app (redZ.obj K)) =
      adjY.unit.app (F.obj K) ≫ resY.map ((mateEquiv adj adj' β.inv).app K) := by
  rw [IsIso.comp_inv_eq, assoc, ← unit_comp_map_reductionComparison adjY adjZ adj adj' β ι
    (mateEquiv_eq_of_map_unit_comp_hom_app adjY adjZ β ι hι) K]

variable [HasShift AY ℤ] [HasShift AZ ℤ] [G.CommShift ℤ] [F.CommShift ℤ] [adj.CommShift ℤ]
  (δY : redY ⋙ resY ⟶ shiftFunctor AY (1 : ℤ)) (δZ : redZ ⋙ resZ ⟶ shiftFunctor AZ (1 : ℤ))

/-- **The connecting morphisms transpose to the pushforward.** If `δ` commutes with `G` along
`ι` and `β`, then it commutes with `F` along the inverse of the conjugate of `β` and the
pushforward comparison `γ`. -/
lemma map_δ_comp_commShiftIso_hom_app_eq
    (hι : ∀ M, G.map (adjY.unit.app M) ≫ ι.hom.app (redY.obj M) =
      adjZ.unit.app (G.obj M) ≫ resZ.map (β.hom.app M))
    (hδ : ∀ M, G.map (δY.app M) ≫ (G.commShiftIso (1 : ℤ)).hom.app M =
      ι.hom.app (redY.obj M) ≫ resZ.map (β.inv.app M) ≫ δZ.app (G.obj M))
    (γ : F ⋙ redY ≅ redZ ⋙ F') (hγ : γ.hom = mateEquiv adj adj' β.inv) (K : AZ) :
    F.map (δZ.app K) ≫ (F.commShiftIso (1 : ℤ)).hom.app K =
      inv ((conjugateEquiv (adjY.comp adj') (adj.comp adjZ) β.hom).app (redZ.obj K)) ≫
        resY.map (γ.inv.app K) ≫ δY.app (F.obj K) := by
  have h := map_reductionComparison_comp_δ adjY adjZ adj adj' β ι δY δZ
    (mateEquiv_eq_of_map_unit_comp_hom_app adjY adjZ β ι hι) hδ K
  rw [← hγ] at h
  rw [IsIso.eq_inv_comp, ← h]
  simp only [assoc]
  rw [← resY.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp]

variable [HasZeroObject AY] [Preadditive AY] [∀ n : ℤ, (shiftFunctor AY n).Additive]
  [Pretriangulated AY] [HasZeroObject AZ] [Preadditive AZ]
  [∀ n : ℤ, (shiftFunctor AZ n).Additive] [Pretriangulated AZ]

/-- **Exceptional comparison from (Pull) along natural reduction triangles.** In the setting of
`CategoryTheory.isIso_mateEquiv_of_reductionTriangle`, let `γ : F ⋙ red_Y ≅ red_Z ⋙ F'` be the
pushforward comparison (the mate of `β⁻¹`, an isomorphism), and suppose `F ⊣ H`, `F' ⊣ H'` with
`H` triangulated and compatible with the shifts, and `Res_Z` reflecting isomorphisms. Then the
exceptional comparison `H ⋙ red_Z ⟶ red_Y ⋙ H'`, the mate of `γ⁻¹`, is an isomorphism. -/
theorem isIso_mateEquiv_mateEquiv_of_reductionTriangle [resZ.ReflectsIsomorphisms]
    {H : AY ⥤ AZ} {H' : NY ⥤ NZ} (adjH : F ⊣ H) (adjH' : F' ⊣ H') [H.CommShift ℤ]
    [adjH.CommShift ℤ] [H.IsTriangulated] (k : ℤ)
    (hY : ∀ M, Triangle.mk (k • 𝟙 M) (adjY.unit.app M) (δY.app M) ∈ distTriang AY)
    (hZ : ∀ M, Triangle.mk (k • 𝟙 M) (adjZ.unit.app M) (δZ.app M) ∈ distTriang AZ)
    (hι : ∀ M, G.map (adjY.unit.app M) ≫ ι.hom.app (redY.obj M) =
      adjZ.unit.app (G.obj M) ≫ resZ.map (β.hom.app M))
    (hδ : ∀ M, G.map (δY.app M) ≫ (G.commShiftIso (1 : ℤ)).hom.app M =
      ι.hom.app (redY.obj M) ≫ resZ.map (β.inv.app M) ≫ δZ.app (G.obj M))
    (γ : F ⋙ redY ≅ redZ ⋙ F') (hγ : γ.hom = mateEquiv adj adj' β.inv) :
    IsIso (mateEquiv adjH adjH' γ.inv) :=
  isIso_mateEquiv_of_reductionTriangle adjZ adjY adjH adjH' γ
    (asIso (conjugateEquiv (adjY.comp adj') (adj.comp adjZ) β.hom)).symm δZ δY k hZ hY
    (fun K ↦ by
      rw [hγ, Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app]
      exact map_unit_comp_inv_conjugateEquiv_app adjY adjZ adj adj' β ι hι K)
    (fun K ↦ by
      rw [Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app]
      exact map_δ_comp_commShiftIso_hom_app_eq adjY adjZ adj adj' β ι δY δZ hι hδ γ hγ K)

/-- `CategoryTheory.isIso_mateEquiv_mateEquiv_of_reductionTriangle` for a triangulated `F`, with
no shift data on its right adjoint `H`: `H` carries the unique commutation with the shifts
compatible with `F ⊣ H` (`Adjunction.rightAdjointCommShift`), for which it is triangulated
(`Adjunction.isTriangulated_rightAdjoint`). -/
theorem isIso_mateEquiv_mateEquiv_of_reductionTriangle' [resZ.ReflectsIsomorphisms]
    [F.IsTriangulated] {H : AY ⥤ AZ} {H' : NY ⥤ NZ} (adjH : F ⊣ H) (adjH' : F' ⊣ H') (k : ℤ)
    (hY : ∀ M, Triangle.mk (k • 𝟙 M) (adjY.unit.app M) (δY.app M) ∈ distTriang AY)
    (hZ : ∀ M, Triangle.mk (k • 𝟙 M) (adjZ.unit.app M) (δZ.app M) ∈ distTriang AZ)
    (hι : ∀ M, G.map (adjY.unit.app M) ≫ ι.hom.app (redY.obj M) =
      adjZ.unit.app (G.obj M) ≫ resZ.map (β.hom.app M))
    (hδ : ∀ M, G.map (δY.app M) ≫ (G.commShiftIso (1 : ℤ)).hom.app M =
      ι.hom.app (redY.obj M) ≫ resZ.map (β.inv.app M) ≫ δZ.app (G.obj M))
    (γ : F ⋙ redY ≅ redZ ⋙ F') (hγ : γ.hom = mateEquiv adj adj' β.inv) :
    IsIso (mateEquiv adjH adjH' γ.inv) := by
  let := adjH.rightAdjointCommShift ℤ
  have := adjH.commShift_of_leftAdjoint ℤ
  have := adjH.isTriangulated_rightAdjoint
  exact isIso_mateEquiv_mateEquiv_of_reductionTriangle adjY adjZ adj adj' β ι δY δZ adjH adjH' k
    hY hZ hι hδ γ hγ

end ReductionTriangle

end CategoryTheory
