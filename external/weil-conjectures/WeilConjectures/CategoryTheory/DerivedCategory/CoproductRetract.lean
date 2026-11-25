/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts

/-!
# Morphisms out of a retract of a coproduct in the derived category

Let `C` be an abelian category with K-injective resolutions. Suppose that a cochain complex `M` is
a retract of a coproduct `P = ∐ᵢ Nᵢ` of complexes, via `s : M ⟶ P` and `t : P ⟶ M` with
`s ≫ t = 𝟙 M`. A morphism `δ : Q(M) ⟶ Y` in the derived category which vanishes on each of the
components `Q(ιᵢ ≫ t) : Q(Nᵢ) ⟶ Q(M)` is zero
(`DerivedCategory.eq_zero_of_Q_map_inj_comp_comp_eq_zero`, and its variant for two morphisms
`DerivedCategory.eq_of_Q_map_inj_comp_comp_eq`): indeed `Q` sends coproducts of
complexes to coproducts (`DerivedCategory.isColimitCofanMkQObj`), so `Q(t) ≫ δ` vanishes, and
`δ = Q(s) ≫ Q(t) ≫ δ`.

This allows one to deduce the vanishing of `δ` from a *locally finite* decomposition of the
identity of `M`, whose components need not form a finite sum.
-/

@[expose] public section

open CategoryTheory Limits Category

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C]

/-- **Morphisms out of a retract of a coproduct.** If a complex `M` is a retract (`s ≫ t = 𝟙 M`)
of a coproduct `P` of complexes, a morphism `δ : Q(M) ⟶ Y` in the derived category such that all
the `Q(ιᵢ ≫ t) ≫ δ` vanish is zero. -/
lemma eq_zero_of_Q_map_inj_comp_comp_eq_zero {ι : Type*} {N : ι → CochainComplex C ℤ}
    {P : Cofan N} (hP : IsColimit P) {M : CochainComplex C ℤ} (s : M ⟶ P.pt) (t : P.pt ⟶ M)
    (hst : s ≫ t = 𝟙 M) {Y : DerivedCategory C} (δ : Q.obj M ⟶ Y)
    (hδ : ∀ i, Q.map (P.inj i ≫ t) ≫ δ = 0) : δ = 0 := by
  have h : Q.map t ≫ δ = 0 :=
    Cofan.IsColimit.hom_ext (isColimitCofanMkQObj hP) _ _ fun i ↦ by
      change Q.map (P.inj i) ≫ Q.map t ≫ δ = _
      rw [← assoc, ← Functor.map_comp, hδ i, comp_zero]
  rw [← id_comp δ, ← Q.map_id, ← hst, Functor.map_comp, assoc, h, comp_zero]

/-- **Morphisms out of a retract of a coproduct are determined by the components.** If a complex
`M` is a retract (`s ≫ t = 𝟙 M`) of a coproduct `P` of complexes, two morphisms
`δ₁ δ₂ : Q(M) ⟶ Y` in the derived category which agree after all the `Q(ιᵢ ≫ t)` are equal. -/
lemma eq_of_Q_map_inj_comp_comp_eq {ι : Type*} {N : ι → CochainComplex C ℤ}
    {P : Cofan N} (hP : IsColimit P) {M : CochainComplex C ℤ} (s : M ⟶ P.pt) (t : P.pt ⟶ M)
    (hst : s ≫ t = 𝟙 M) {Y : DerivedCategory C} (δ₁ δ₂ : Q.obj M ⟶ Y)
    (hδ : ∀ i, Q.map (P.inj i ≫ t) ≫ δ₁ = Q.map (P.inj i ≫ t) ≫ δ₂) : δ₁ = δ₂ := by
  have h : Q.map t ≫ δ₁ = Q.map t ≫ δ₂ :=
    Cofan.IsColimit.hom_ext (isColimitCofanMkQObj hP) _ _ fun i ↦ by
      change Q.map (P.inj i) ≫ Q.map t ≫ δ₁ = Q.map (P.inj i) ≫ Q.map t ≫ δ₂
      rw [← assoc, ← assoc, ← Functor.map_comp, hδ i]
  calc δ₁ = Q.map (s ≫ t) ≫ δ₁ := by rw [hst, Q.map_id, id_comp]
    _ = Q.map s ≫ Q.map t ≫ δ₁ := by rw [Functor.map_comp, assoc]
    _ = Q.map s ≫ Q.map t ≫ δ₂ := by rw [h]
    _ = δ₂ := by rw [← assoc, ← Functor.map_comp, hst, Q.map_id, id_comp]

end DerivedCategory
