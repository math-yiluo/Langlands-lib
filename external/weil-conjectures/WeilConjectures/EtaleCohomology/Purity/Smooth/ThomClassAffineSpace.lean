/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClassField
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ZeroSectionPurity

/-!
# The Thom class of the zero section of affine space over any base

For any scheme `B` on which the exponent of `Λ` is invertible and the zero section
`z : B ↪ 𝔸^c_B`, cut out by the coordinates `t₁, …, t_c`, the adjoint `Λ_B ⟶ Rz^! (Λ(c)[2c])`
of `∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_c)` is an isomorphism.

The proof is the induction of `ThomClassField.lean`, with the rank-one input over a field
replaced by relative purity for the zero section of the affine line over any base,
`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord_of_hasInvertibleExponent`.

## Main statements

- `isIso_supportedClassMap_kummerBoundaryProduct_cons_coord_of_hasInvertibleExponent`
- `isIso_supportedClassMap_kummerBoundaryProduct_coord_of_hasInvertibleExponent`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ]

/-- **The induction step for the Thom class, over any base.** Let `B'` be a scheme on which the
exponent of `Λ` is invertible, `X = 𝔸¹_{B'}` with coordinate `t` and projection `p`, and
`g₁, …, g_c` functions on `B'` such that the adjoint of `∂κ(g₁) ∪ ⋯ ∪ ∂κ(g_c)` is an
isomorphism. Then the adjoint of `∂κ(t) ∪ ∂κ(p^* g₁) ∪ ⋯ ∪ ∂κ(p^* g_c)` on `X` is an
isomorphism. -/
theorem isIso_supportedClassMap_kummerBoundaryProduct_cons_coord_of_hasInvertibleExponent
    (B' : Scheme.{u}) [HasInvertibleExponent Λ B'] {c : ℕ} (g₀ : Fin c → Γ(B', ⊤))
    (h : IsIso (supportedClassMap Λ (B'.zeroLocusSubschemeι (Set.range g₀))
      (kummerBoundaryProduct Λ g₀))) :
    IsIso (supportedClassMap Λ (𝔸(ULift.{u} (Fin 1); B').zeroLocusSubschemeι
        (Set.range (Fin.cons (AffineSpace.coord B' (ULift.up 0))
          fun a ↦ (𝔸(ULift.{u} (Fin 1); B') ↘ B').appTop (g₀ a) :
            Fin (c + 1) → Γ(𝔸(ULift.{u} (Fin 1); B'), ⊤))))
      (kummerBoundaryProduct Λ (Fin.cons (AffineSpace.coord B' (ULift.up 0))
          fun a ↦ (𝔸(ULift.{u} (Fin 1); B') ↘ B').appTop (g₀ a) :
            Fin (c + 1) → Γ(𝔸(ULift.{u} (Fin 1); B'), ⊤)))) := by
  set X := 𝔸(ULift.{u} (Fin 1); B')
  set p := 𝔸(ULift.{u} (Fin 1); B') ↘ B'
  set t := AffineSpace.coord B' (ULift.up (0 : Fin 1))
  set g : Fin c → Γ(X, ⊤) := fun a ↦ p.appTop (g₀ a)
  have : HasInvertibleExponent Λ X := .of_hom p
  set i₁ := X.zeroLocusSubschemeι {t}
  have : HasInvertibleExponent Λ (X.zeroLocusSubscheme {t}) := .of_hom i₁
  have hs : i₁.appTop '' Set.range g = Set.range (fun a ↦ i₁.appTop (g a)) := by
    rw [← Set.range_comp]
    rfl
  have hg := isPullback_zeroLocusSubschemeι i₁ (Set.range g) _ hs
  -- the restriction of `∂κ(p^* g₁) ∪ ⋯ ∪ ∂κ(p^* g_c)` to `V(t) ≅ B'` is `∂κ(g₁) ∪ ⋯ ∪ ∂κ(g_c)`
  have hβ : IsIso (supportedClassMap Λ _ (restrictSupportedClass Λ i₁ _ _ _
      hg (leftDerivedUpperStarConstantComplexIso Λ i₁).inv
      (leftDerivedUpperStarTateShiftIso Λ i₁ c) (kummerBoundaryProduct Λ g))) := by
    rw [restrictSupportedClass_kummerBoundaryProduct Λ i₁ g _ (fun _ ↦ rfl) _ hg]
    have : IsIso (i₁ ≫ p) :=
      (AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) B' (s := {t})
        Set.range_unique).isIso_inv
    exact isIso_supportedClassMap_kummerBoundaryProduct_of_etale Λ (i₁ ≫ p) g₀ _
      (fun a ↦ by rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]) h
  have hα := isIso_supportedClassMap_kummerBoundary_coord_of_hasInvertibleExponent Λ B'
  have hcup := isIso_supportedClassMap_cupWithSupports i₁ _
    (X.zeroLocusSubschemeι (Set.range (Fin.cons t g : Fin (c + 1) → Γ(X, ⊤)))) _ _ hg
    (by rw [Fin.range_cons, range_zeroLocusSubschemeι_insert])
    (DerivedCategory.isInvertible.shift (isInvertible_tateObject Λ X c) _) _ _
    (constantComplexDiagonal Λ X) (constantComplexDiagonal_comp_derivedTensorLeftUnitor_hom Λ X)
    _ _ hα hβ
  rw [kummerBoundaryProduct_cons, cupWithSupportsTateObject, Category.assoc,
    eqToHom_eq_map_map Λ _ (show (tateObject Λ X (1 + c))⟦2 * (1 + (c : ℤ))⟧ =
      (tateObject Λ X ((c + 1 : ℕ) : ℤ))⟦2 * ((c + 1 : ℕ) : ℤ)⟧ by
        rw [Nat.cast_succ, add_comm (1 : ℤ)]),
    ← Functor.map_comp, ← Functor.map_comp]
  exact isIso_supportedClassMap_comp_map Λ _ _ _ hcup

/-- Blueprint `proposition-purity-vector-bundles`: `𝔸¹ ⇒ 𝔸ⁿ`: the model purity, clause (i), over any
base.

For any scheme `B` on which the exponent of `Λ` is invertible and the zero section
`z : B ↪ 𝔸^c_B`, cut out by the coordinates `t₁, …, t_c`, the adjoint `Λ_B ⟶ Rz^! (Λ(c)[2c])`
of `∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_c)` (`AlgebraicGeometry.Etale.supportedClassMap`) is an isomorphism.

By induction on `c`, writing `𝔸^{c+1}_B ≅ 𝔸¹_{𝔸^c_B}`
(`AlgebraicGeometry.Etale.affineSpaceConsIso`) with the first coordinate as the coordinate of
the affine line; the step is
`isIso_supportedClassMap_kummerBoundaryProduct_cons_coord_of_hasInvertibleExponent`.
-/
theorem isIso_supportedClassMap_kummerBoundaryProduct_coord_of_hasInvertibleExponent (c : ℕ)
    (B : Scheme.{u}) [HasInvertibleExponent Λ B] :
    IsIso (supportedClassMap Λ (𝔸(ULift.{u} (Fin c); B).zeroLocusSubschemeι
        (Set.range fun a : Fin c ↦ AffineSpace.coord B (ULift.up a)))
      (kummerBoundaryProduct Λ fun a : Fin c ↦ AffineSpace.coord B (ULift.up a))) := by
  induction c with
  | zero => exact isIso_supportedClassMap_kummerBoundaryProduct_zero Λ _ _
  | succ c ih =>
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin c); B) :=
      .of_hom (𝔸(ULift.{u} (Fin c); B) ↘ B)
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin c); B)) :=
      .of_hom (𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin c); B)) ↘ 𝔸(ULift.{u} (Fin c); B))
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin (c + 1)); B) :=
      .of_hom (𝔸(ULift.{u} (Fin (c + 1)); B) ↘ B)
    refine isIso_supportedClassMap_kummerBoundaryProduct_of_etale Λ (affineSpaceConsIso c B).hom
      _ _ (fun a ↦ ?_)
      (isIso_supportedClassMap_kummerBoundaryProduct_cons_coord_of_hasInvertibleExponent Λ
        𝔸(ULift.{u} (Fin c); B) (fun a : Fin c ↦ AffineSpace.coord B (ULift.up a)) ih)
    cases a using Fin.cases with
    | zero => rw [Fin.cons_zero, affineSpaceConsIso_hom_appTop_coord_zero]
    | succ a => rw [Fin.cons_succ, affineSpaceConsIso_hom_appTop_coord_succ]

end Etale

end AlgebraicGeometry
