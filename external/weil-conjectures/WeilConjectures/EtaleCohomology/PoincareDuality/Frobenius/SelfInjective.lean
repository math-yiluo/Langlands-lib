/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.HomToInjective
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Perfectness

/-!
# Degreewise Poincaré duality over a self-injective coefficient ring

Let `Λ` be a finite coefficient ring which is self-injective and cogenerates (every nonzero
element of a `Λ`-module is detected by a linear form to `Λ`), e.g. `Λ = ℤ/ℓᵐ`
(`ZModLike.injective_self`, `ZModLike.exists_apply_ne_zero`). Then the degreewise Poincaré
pairings `⟨-, -⟩_i : H^i_c(X, K) × H^{2d-i}(X, K^∨(d)) ⟶ Λ` are nondegenerate on both sides
(`AlgebraicGeometry.Etale.TateOrientation.injective_degreewisePoincarePairing`): over a
self-injective ring the dual `RHom(C, Λ)` of a complex is computed degreewise,
`Hom(C, Λ[0]) = Hom(H⁰(C), Λ)`
(`DerivedCategory.bijective_homologyFunctor_map_singleFunctor_of_injective`).

This is the finite-level duality `A_{E,n}` of blueprint `theorem-poincare-duality--9` in the form
needed for the transport to `ℚ̄_ℓ` (`LinearMap.mem_torsion_of_finiteLevel`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]
  [Module.Injective R R]

/-- **The composition pairing with `R[0]` is nondegenerate over a self-injective
cogenerating ring.** Let `R` be self-injective such that every nonzero element of an `R`-module
is detected by a linear form. Then for every `E ∈ D(R)` the composition pairing
`Hom(R[0], E) × Hom(E, R[0]) ⟶ End(R[0])` is nondegenerate on both sides. -/
theorem nondegenerate_comp_singleFunctor_of_injective
    (hcog : ∀ (M : ModuleCat.{u} R) (x : M), x ≠ 0 → ∃ χ : M →ₗ[R] R, χ x ≠ 0)
    (E : DerivedCategory (ModuleCat.{u} R)) :
    (∀ x : (singleFunctor _ 0).obj (ModuleCat.of R R) ⟶ E, x ≠ 0 →
        ∃ f : E ⟶ (singleFunctor _ 0).obj (ModuleCat.of R R), x ≫ f ≠ 0) ∧
      (∀ f : E ⟶ (singleFunctor _ 0).obj (ModuleCat.of R R), f ≠ 0 →
        ∃ x : (singleFunctor _ 0).obj (ModuleCat.of R R) ⟶ E, x ≫ f ≠ 0) := by
  have : Injective (ModuleCat.of R R) := Module.injective_object_of_injective_module R R
  let U := (singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  let ε := (singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app (ModuleCat.of R R)
  have hH := bijective_homologyFunctor_map_singleFunctor_of_injective E (ModuleCat.of R R)
  have hθ (Y : DerivedCategory (ModuleCat.{u} R)) :
      Function.Bijective (homSingleToHomology (ModuleCat.of R R) 0 Y) := by
    convert (homSingleEquivOfProjective (ModuleCat.of R R) 0 Y).bijective using 1
    exact funext fun φ ↦ (homSingleEquivOfProjective_apply _ _ _ φ).symm
  have hθ0 (Y : DerivedCategory (ModuleCat.{u} R)) :
      homSingleToHomology (ModuleCat.of R R) 0 Y 0 = 0 := by
    simp [homSingleToHomology]
  have hne (Y : DerivedCategory (ModuleCat.{u} R)) (z : U ⟶ Y)
      (hz : (homSingleToHomology (ModuleCat.of R R) 0 Y z).hom 1 ≠ 0) : z ≠ 0 := by
    rintro rfl
    rw [hθ0] at hz
    exact hz rfl
  refine ⟨fun x hx ↦ ?_, fun f hf ↦ ?_⟩
  · have hx' : (homSingleToHomology (ModuleCat.of R R) 0 E x).hom 1 ≠ 0 := by
      intro h
      apply hx
      refine (hθ E).1 ?_
      rw [hθ0]
      exact ModuleCat.hom_ext (LinearMap.ext_ring h)
    obtain ⟨χ, hχ⟩ := hcog _ _ hx'
    obtain ⟨f, hf⟩ := hH.2 (ModuleCat.ofHom χ ≫ ε.inv)
    refine ⟨f, hne U _ ?_⟩
    simp only at hf
    rw [homSingleToHomology_comp, hf]
    have hinj : Function.Injective ε.inv.hom :=
      (ModuleCat.mono_iff_injective ε.inv).1 inferInstance
    intro h0
    apply hχ
    apply hinj
    rw [map_zero]
    exact h0
  · have hHf : (homologyFunctor _ 0).map f ≠ 0 := fun h ↦ hf (hH.1 (by
      simp only [h, Functor.map_zero]))
    obtain ⟨v, hv⟩ : ∃ v, ((homologyFunctor _ 0).map f).hom v ≠ 0 := by
      by_contra! h
      exact hHf (ModuleCat.hom_ext (LinearMap.ext h))
    obtain ⟨x, hx⟩ := (hθ E).2 (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ v))
    refine ⟨x, hne U _ ?_⟩
    rw [homSingleToHomology_comp, hx]
    simpa using hv

end DerivedCategory

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Module.Injective Λ Λ] {k : Type u} [Field k]
  [IsSepClosed k]

/-- **The composition pairing with the unit is nondegenerate at the point, over a self-injective
cogenerating ring.** For `k` separably closed and `E` in the point category `D(Spec k_ét, Λ)`,
the composition pairing `Hom(Λ_s, E) × Hom(E, Λ_s) ⟶ End(Λ_s)` is nondegenerate on both sides.
This follows from the case of `D(Λ)` through the equivalence `RΓ(Spec k, -)`. -/
theorem nondegenerate_comp_unit_of_isSepClosed_of_injective
    (hcog : ∀ (M : ModuleCat.{u + 1} Λ) (x : M), x ≠ 0 → ∃ χ : M →ₗ[Λ] Λ, χ x ≠ 0)
    (E : DerivedCategoryModule Λ (Spec (.of k))) :
    (∀ x : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ E, x ≠ 0 →
        ∃ f : E ⟶ 𝟙_ _, x ≫ f ≠ 0) ∧
      (∀ f : E ⟶ 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))), f ≠ 0 →
        ∃ x : 𝟙_ _ ⟶ E, x ≫ f ≠ 0) := by
  let F := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))
  obtain ⟨h₁, h₂⟩ := DerivedCategory.nondegenerate_comp_singleFunctor_of_injective hcog (F.obj E)
  exact ⟨F.exists_comp_ne_zero_of_fullyFaithful (rightDerivedGlobalSectionsUnitIso Λ k)
      (Iso.refl _) h₁,
    F.exists_comp_ne_zero_of_fullyFaithful' (rightDerivedGlobalSectionsUnitIso Λ k)
      (Iso.refl _) h₂⟩

variable [Finite Λ] [HasTateTwist Λ] {X : Scheme.{u}} {a : X ⟶ Spec (.of k)}
  [HasCompactification a] [HasInvertibleExponent Λ X] {d : ℕ}

namespace TateOrientation

/-- **Degreewise Poincaré duality over a self-injective coefficient ring** (finite level of
blueprint `theorem-poincare-duality--9`). Let `k` be separably closed, `Λ` a finite self-injective
cogenerating ring (e.g. `ℤ/ℓᵐ`) whose characteristic is invertible on `X`, and `γ` a Tate
orientation of `a : X ⟶ Spec k`. For every `K ∈ D(X_ét, Λ)` and `i + j = 2d`, the degreewise
Poincaré pairing `H^i_c(X, K) × H^j(X, K^∨(d)) ⟶ End(Λ_s)` is nondegenerate on both sides.

The derived Poincaré pairing is perfect
(`AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing_of_finite`), so its
degree-zero part is a composition pairing `⟨x, y⟩ = x ≫ g(y)` with `g` bijective, which is
nondegenerate (`AlgebraicGeometry.Etale.nondegenerate_comp_unit_of_isSepClosed_of_injective`). -/
theorem injective_degreewisePoincarePairing
    (hcog : ∀ (M : ModuleCat.{u + 1} Λ) (x : M), x ≠ 0 → ∃ χ : M →ₗ[Λ] Λ, χ x ≠ 0)
    (γ : TateOrientation Λ a d) (K : DerivedCategoryModule Λ X) (i j : ℤ)
    (hij : i + j = 2 * d) :
    Function.Injective (γ.degreewisePoincarePairing K i j hij) ∧
      Function.Injective (γ.degreewisePoincarePairing K i j hij).flip := by
  obtain ⟨g, hg⟩ := (γ.isPerfectPairing_poincarePairing_of_finite K).exists_addEquiv_degreeZero
    i (j - 2 * d) (by omega)
  obtain ⟨h₁, h₂⟩ := nondegenerate_comp_unit_of_isSepClosed_of_injective hcog
    (((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)
  let s := (shiftFunctorAdd' (DerivedCategoryModule Λ (Spec (.of k))) (2 * d : ℤ) (j - 2 * d) j
    (by omega)).app ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))
  have hp (x y) : γ.degreewisePoincarePairing K i j hij x y = x ≫ g (y ≫ s.hom) := by
    rw [degreewisePoincarePairing_apply, degreewisePairing_apply]
    simp only [Category.assoc]
    rw [hg x]
    rfl
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_,
    (injective_iff_map_eq_zero _).2 fun y hy ↦ ?_⟩
  · by_contra hx0
    obtain ⟨f, hf⟩ := h₁ x hx0
    obtain ⟨z, rfl⟩ := g.surjective f
    have := LinearMap.congr_fun hx (z ≫ s.inv)
    rw [hp, Category.assoc, s.inv_hom_id] at this
    erw [Category.comp_id] at this
    simp only [LinearMap.zero_apply] at this
    exact hf this
  · by_contra hy0
    have hgy : g (y ≫ s.hom) ≠ 0 := fun h ↦ hy0 (by
      have h' := g.injective (h.trans (map_zero g).symm)
      simpa using congrArg (· ≫ s.inv) h')
    obtain ⟨x, hx⟩ := h₂ _ hgy
    have := LinearMap.congr_fun hy x
    rw [LinearMap.flip_apply, hp] at this
    exact hx this

end TateOrientation

end AlgebraicGeometry.Etale
