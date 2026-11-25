/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.UnitPairing
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism

/-!
# Nondegeneracy of the trace–cup pairing at a finite level

Let `k` be separably closed, `a : X ⟶ Spec k` proper with a Tate orientation `γ` of relative
dimension `d`, and `Λ` a finite self-injective cogenerating coefficient ring (e.g. `ℤ/ℓᵐ`) whose
characteristic is invertible on `X`. Write `Hⁿ(X, Λ) = Hom(Λ_X, Λ_X[n])`. There is an additive
map `T : H^{2d}(X, Λ) ⟶ Λ` (a trace) such that for every `i + j = 2d` the trace–cup pairing
`(x, y) ↦ T(x ⌣ y)` is nondegenerate on both sides
(`AlgebraicGeometry.Etale.TateOrientation.exists_nondegenerate_traceCup`).

The trace is `z ↦ 1 ≫ (z ≫ γ')^♭`, where `γ' : Λ_X[2d] ≅ Ra^! Λ` is the orientation read through
`Λ(d) ≅ Λ` over the separably closed `k`, `(-)^♭` is the adjunction `Ra_! ⊣ Ra^!` and
`1 : Λ ⟶ Ra_! Λ_X` is the unit class (`AlgebraicGeometry.Etale.unitClassCompactSupport`). The
cup product is the Yoneda product `x ⌣ y = x ≫ y[i]`
(`CategoryTheory.MonoidalCategory.shiftProduct_eq`), so that
`T(x ⌣ y) = (1 ≫ Ra_!(x)) ≫ (y[i] ≫ γ')^♭`: the composition pairing
`Hom(Λ, E) × Hom(E, Λ) ⟶ End(Λ)` at `E = Ra_!(Λ_X[i])`, nondegenerate at the separably closed point
(`AlgebraicGeometry.Etale.nondegenerate_comp_unit_of_isSepClosed_of_injective`), read through the
bijections `x ↦ 1 ≫ Ra_!(x)` (`La^* ⊣ Ra_*` and `Ra_! ≅ Ra_*`) and `y ↦ (y[i] ≫ γ')^♭`.

This is the finite-level duality of blueprint `theorem-poincare-duality--9` in the form needed for
the trace–cup structure at `ℚ̄_ℓ` (`corollary-cup-product-pairing--1`,
`corollary-degreewise-duality-over-fields`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [Module.Injective Λ Λ] [HasTateTwist Λ]
  {k : Type u} [Field k] [IsSepClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  {X : Scheme.{u}} [HasInvertibleExponent Λ X] {a : X ⟶ Spec (.of k)} [HasCompactification a]
  [IsProper a] {d : ℕ}

namespace TateOrientation

/-- A pairing `(x, y) ↦ p x ≫ q y` through zero-preserving bijections `p : α → Hom(B, E)` and
`q : β → Hom(E, B)` is nondegenerate on both sides as soon as the composition pairing
`Hom(B, E) × Hom(E, B) ⟶ End(B)` is. -/
lemma nondegenerate_of_bijective_comp {C : Type*} [Category C] [Preadditive C] {B E : C}
    {α β : Type*} [Zero α] [Zero β] (p : α → (B ⟶ E)) (q : β → (E ⟶ B))
    (hp : Function.Bijective p) (hq : Function.Bijective q) (hp0 : p 0 = 0) (hq0 : q 0 = 0)
    (h : (∀ v : B ⟶ E, v ≠ 0 → ∃ f : E ⟶ B, v ≫ f ≠ 0) ∧
      (∀ f : E ⟶ B, f ≠ 0 → ∃ v : B ⟶ E, v ≫ f ≠ 0)) :
    (∀ x, (∀ y, p x ≫ q y = 0) → x = 0) ∧ (∀ y, (∀ x, p x ≫ q y = 0) → y = 0) := by
  refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · by_contra hne
    obtain ⟨f, hf⟩ := h.1 (p x) fun h0 ↦ hne (hp.1 (h0.trans hp0.symm))
    obtain ⟨y, rfl⟩ := hq.2 f
    exact hf (hx y)
  · by_contra hne
    obtain ⟨v, hv⟩ := h.2 (q y) fun h0 ↦ hne (hq.1 (h0.trans hq0.symm))
    obtain ⟨x, rfl⟩ := hp.2 v
    exact hv (hy x)

/-- Composing `η_A ≫ G(e) ≫ α⁻¹_B` with `L(x)`, for `F ⊣ G` and `α : L ≅ G`, is
`(e ≫ x)^♯ ≫ α⁻¹`. -/
lemma unit_comp_map_comp_eq_homEquiv_comp {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {G L : D ⥤ C} (adj : F ⊣ G) (α : L ≅ G) {A : C} {B M : D} (e : F.obj A ≅ B) (x : B ⟶ M) :
    (adj.unit.app A ≫ G.map e.hom ≫ α.inv.app B) ≫ L.map x =
      adj.homEquiv A M (e.hom ≫ x) ≫ α.inv.app M := by
  simp [Adjunction.homEquiv_unit]

/-- **The trace–cup pairing is nondegenerate at a finite level.** For `a : X ⟶ Spec k` proper
over a separably closed field with a Tate orientation `γ` of relative dimension `d`, and a finite
self-injective cogenerating ring `Λ`, there is an additive map `T : H^{2d}(X, Λ) ⟶ Λ` such that,
for all `i + j = 2d`, the pairing `(x, y) ↦ T(x ⌣ y)` on `Hⁱ(X, Λ) × Hʲ(X, Λ)` is nondegenerate
on both sides. -/
theorem exists_nondegenerate_traceCup
    (hcog : ∀ (M : ModuleCat.{u + 1} Λ) (x : M), x ≠ 0 → ∃ χ : M →ₗ[Λ] Λ, χ x ≠ 0)
    (γ : TateOrientation Λ a d) :
    ∃ T : (𝟙_ (DerivedCategoryModule Λ X) ⟶
        (𝟙_ (DerivedCategoryModule Λ X))⟦(2 * d : ℤ)⟧) →+ Λ,
      ∀ (i j : ℤ) (hij : i + j = 2 * d),
        (∀ x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦i⟧,
          (∀ y : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦j⟧,
            T (cupProduct _ i j x y ≫ eqToHom (by rw [hij])) = 0) → x = 0) ∧
        (∀ y : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦j⟧,
          (∀ x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦i⟧,
            T (cupProduct _ i j x y ≫ eqToHom (by rw [hij])) = 0) → y = 0) := by
  obtain ⟨eT⟩ := nonempty_tateObject_iso_unit Λ k (d : ℤ)
  let eX : tateObject Λ X d ≅ 𝟙_ (DerivedCategoryModule Λ X) :=
    (leftDerivedUpperStarTateObjectIso a (d : ℤ)).symm ≪≫
      (L((a)^*[ModuleCat.{u + 1} Λ])).mapIso eT ≪≫ leftDerivedUpperStarConstantComplexIso Λ a
  let γ' : (𝟙_ (DerivedCategoryModule Λ X))⟦(2 * d : ℤ)⟧ ≅
      (R(a)^![Λ]).obj (𝟙_ (DerivedCategoryModule Λ (Spec (.of k)))) :=
    (shiftFunctor _ (2 * d : ℤ)).mapIso eX.symm ≪≫ γ.dualizingComplexIso
  let adj := rightDerivedUpperShriekAdjunction Λ a
  let α := rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) a
  let e : (L((a)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ (DerivedCategoryModule Λ (Spec (.of k)))) ≅
      𝟙_ (DerivedCategoryModule Λ X) := leftDerivedUpperStarConstantComplexIso Λ a
  let adj' := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a
  obtain ⟨u, hu⟩ : ∃ u : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶
      (R(a)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ (DerivedCategoryModule Λ X)),
      u = adj'.unit.app _ ≫ (R((a)_*[ModuleCat.{u + 1} Λ])).map e.hom ≫ α.inv.app _ :=
    ⟨_, rfl⟩
  let eΛ := (endUnitAddEquiv Λ (Spec (.of k))).symm
  let T : (𝟙_ (DerivedCategoryModule Λ X) ⟶
      (𝟙_ (DerivedCategoryModule Λ X))⟦(2 * d : ℤ)⟧) →+ Λ :=
    AddMonoidHom.mk' (fun z ↦ eΛ (u ≫
      (adj.homEquiv (𝟙_ (DerivedCategoryModule Λ X)) _).symm (z ≫ γ'.hom))) fun z z' ↦ by
        rw [← map_add]
        congr 1
        simp only [Adjunction.homEquiv_counit, Preadditive.add_comp, Functor.map_add,
          Preadditive.comp_add]
  refine ⟨T, fun i j hij ↦ ?_⟩
  let p : ((𝟙_ (DerivedCategoryModule Λ X)) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦i⟧) →
      (𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶
        (R(a)_![ModuleCat.{u + 1} Λ]).obj ((𝟙_ (DerivedCategoryModule Λ X))⟦i⟧)) :=
    fun x ↦ u ≫ (R(a)_![ModuleCat.{u + 1} Λ]).map x
  let Φ : ((𝟙_ (DerivedCategoryModule Λ X))⟦j⟧)⟦i⟧ ≅
      (R(a)^![Λ]).obj (𝟙_ (DerivedCategoryModule Λ (Spec (.of k)))) :=
    (shiftFunctorAdd' _ j i (i + j) (add_comm j i)).symm.app _ ≪≫
      eqToIso (by rw [hij]) ≪≫ γ'
  let q : ((𝟙_ (DerivedCategoryModule Λ X)) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦j⟧) →
      ((R(a)_![ModuleCat.{u + 1} Λ]).obj ((𝟙_ (DerivedCategoryModule Λ X))⟦i⟧) ⟶
        𝟙_ (DerivedCategoryModule Λ (Spec (.of k)))) :=
    fun y ↦ (adj.homEquiv _ _).symm (y⟦i⟧' ≫ Φ.hom)
  have key : ∀ x y, T (cupProduct _ i j x y ≫ eqToHom (by rw [hij])) = eΛ (p x ≫ q y) := by
    intro x y
    change eΛ _ = eΛ _
    congr 1
    rw [cupProduct_eq_shiftProduct,
      MonoidalCategory.shiftProduct_eq (DerivedCategory.unitorsCommShift _)]
    simp only [p, q, Φ, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, eqToIso.hom]
    simp only [Category.assoc]
    rw [Adjunction.homEquiv_naturality_left_symm]
  have hpx : ∀ x, p x = adj'.homEquiv (𝟙_ (DerivedCategoryModule Λ (Spec (.of k)))) _
      (e.hom ≫ x) ≫ α.inv.app _ := by
    intro x
    change u ≫ _ = _
    rw [hu]
    exact unit_comp_map_comp_eq_homEquiv_comp adj' α e x
  have hp : Function.Bijective p := by
    rw [show p = _ from funext hpx]
    exact ((α.app _).symm.homToEquiv.bijective.comp (adj'.homEquiv _ _).bijective).comp
      e.symm.homFromEquiv.bijective
  have hq : Function.Bijective q :=
    (adj.homEquiv _ _).symm.bijective.comp (Φ.homToEquiv.bijective.comp
      ⟨Functor.map_injective _, Functor.map_surjective _⟩)
  have hp0 : p 0 = 0 := by simp only [p, Functor.map_zero, Limits.comp_zero]
  have hq0 : q 0 = 0 := by
    simp only [q, Functor.map_zero, Limits.zero_comp, Adjunction.homEquiv_counit]
  obtain ⟨h₁, h₂⟩ := nondegenerate_of_bijective_comp p q hp hq hp0 hq0
    (nondegenerate_comp_unit_of_isSepClosed_of_injective hcog _)
  refine ⟨fun x hx ↦ h₁ x fun y ↦ ?_, fun y hy ↦ h₂ y fun x ↦ ?_⟩
  · have h := hx y
    rw [key] at h
    exact (AddEquiv.map_eq_zero_iff eΛ).1 h
  · have h := hy x
    rw [key] at h
    exact (AddEquiv.map_eq_zero_iff eΛ).1 h

end TateOrientation

end AlgebraicGeometry.Etale
