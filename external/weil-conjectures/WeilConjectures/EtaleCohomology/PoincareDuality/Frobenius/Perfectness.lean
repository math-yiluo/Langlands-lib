/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.CompositionPairing
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.PointPairing
public import WeilConjectures.EtaleCohomology.PoincareDuality.InvertibleTwist
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# Degreewise perfectness of the Poincaré pairings over a field

Let `k` be a separably closed field, `Λ` a finite field whose characteristic is invertible on
`X`, `γ` a Tate orientation of `a : X ⟶ Spec k` of relative dimension `d`, and
`K ∈ D^b_{ctf}(X, Λ)`. The degreewise Poincaré pairings
`⟨-, -⟩_i : H^i_c(X, K) × H^{2d-i}(X, K^∨(d)) ⟶ Λ`
(`AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing`) are perfect: the adjoint
`H^{2d-i}(X, K^∨(d)) ⟶ H^i_c(X, K)^∨` is an isomorphism.

The proof is the one of the blueprint, read on classes. The derived pairing `β_K` is perfect
(`AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing_of_finite`), so its
degree-zero part is the composition pairing `⟨x, y⟩ = x ≫ g(y)` for a bijection
`g : H^{2d-i}(X, K^∨(d)) ≃ Hom((Ra_! K)[i], Λ_s)`
(`AlgebraicGeometry.Etale.IsPerfectPairing.exists_addEquiv_degreeZero`). Over the field `Λ`,
the composition pairing `Hom(Λ_s, E) × Hom(E, Λ_s) ⟶ End(Λ_s) = Λ` is perfect for
`E = (Ra_! K)[i]`, whose `H^0` is the finite-dimensional space `H^i_c(X, K)`
(`AlgebraicGeometry.Etale.nondegenerate_comp_unit_of_isSepClosed`): this is where
`H^{-i}(C^∨) ≅ H^i(C)^∨` over a field enters.

## Main statements

- `AlgebraicGeometry.Etale.TateOrientation.isPerfPair_degreewisePoincarePairing`
  (`corollary-degreewise-duality-over-fields--1`, `corollary-degreewise-duality-over-fields`): the
  degreewise pairings are perfect.
- `AlgebraicGeometry.Etale.TateOrientation.isPerfPair_degreewisePoincarePairing_of_isProper`
  (`theorem-poincare-duality--8`): the same for `a` proper, with `H^i(X, K)` in place of
  `H^i_c(X, K)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [IsDomain Λ] [Finite Λ] {k : Type u} [Field k]
  [IsSepClosed k]

/-- Over a separably closed field `k`, if `H^i(RΓ(Spec k, C))` is finite-dimensional over the
finite field `Λ`, then `Hom(Λ_s, C[i])` is finite and the composition pairing
`Hom(Λ_s, C[i]) × Hom(C[i], Λ_s) ⟶ End(Λ_s)` is nondegenerate on both sides. -/
lemma nondegenerate_comp_unit_shift_of_isSepClosed (C : DerivedCategoryModule Λ (Spec (.of k)))
    (i : ℤ)
    (hC : Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C))) :
    Finite (𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ C⟦i⟧) ∧
      (∀ x : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ C⟦i⟧, x ≠ 0 →
        ∃ f : C⟦i⟧ ⟶ 𝟙_ _, x ≫ f ≠ 0) ∧
      (∀ f : C⟦i⟧ ⟶ 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))), f ≠ 0 →
        ∃ x : 𝟙_ _ ⟶ C⟦i⟧, x ≫ f ≠ 0) := by
  let RΓ := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))
  let e := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0).mapIso
      ((RΓ.commShiftIso i).app C) ≪≫
    ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0).shiftIso i 0 i
      (by simp)).app _
  have hC' : Module.Finite Λ (((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0).shift
      i).obj (RΓ.obj C)) := hC
  exact nondegenerate_comp_unit_of_isSepClosed (Finite.isField_of_domain Λ) _
    (Module.Finite.equiv e.toLinearEquiv.symm)

variable [HasTateTwist Λ] {X : Scheme.{u}} {a : X ⟶ Spec (.of k)} [HasCompactification a]
  [LocallyOfFiniteType a] [HasInvertibleExponent Λ X] {d : ℕ}

namespace TateOrientation

/-- Blueprint `corollary-degreewise-duality-over-fields--1`: Degreewise perfectness over a
field (finite-field case). This is also the degreewise part of blueprint
`corollary-degreewise-duality-over-fields`.

Let `k` be separably closed, `Λ` a finite field (a finite domain) whose characteristic is
invertible on `X`, `γ` a Tate orientation of `a : X ⟶ Spec k` of relative dimension `d`, with
`a` locally of finite type, and `K ∈ D^b_{ctf}(X, Λ)`. Then for `i + j = 2d` the degreewise
Poincaré pairing

`⟨-, -⟩_i : H^i_c(X, K) × H^j(X, K^∨(d)) ⟶ Λ`

(`AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing`, with values in
`End(Λ_s)`, read in `Λ` through any linear isomorphism `ℓ : End(Λ_s) ≃ Λ`) is perfect: its
adjoint `H^j(X, K^∨(d)) ⟶ H^i_c(X, K)^∨` is an isomorphism of finite-dimensional
`Λ`-vector spaces.

It follows from the derived Poincaré duality
(`AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing_of_finite`): the
degree-zero part of a perfect pairing is a composition pairing
(`AlgebraicGeometry.Etale.IsPerfectPairing.exists_addEquiv_degreeZero`), and over a field the
composition pairing with the unit of the point category is perfect
(`AlgebraicGeometry.Etale.nondegenerate_comp_unit_of_isSepClosed`). -/
theorem isPerfPair_degreewisePoincarePairing (γ : TateOrientation Λ a d)
    {K : DerivedCategoryModule Λ X} (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K)
    (i j : ℤ) (hij : i + j = 2 * d)
    (ℓ : (𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ 𝟙_ _) ≃ₗ[Λ] Λ) :
    ((γ.degreewisePoincarePairing K i j hij).compr₂ ℓ.toLinearMap).IsPerfPair := by
  obtain ⟨g, hg⟩ := (γ.isPerfectPairing_poincarePairing_of_finite K).exists_addEquiv_degreeZero
    i (j - 2 * d) (by omega)
  have hC : Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
        ((R(a)_![ModuleCat.{u + 1} Λ]).obj K))) :=
    finite_compactlySupportedCohomology Λ a K hK i
  obtain ⟨h₀, h₁, h₂⟩ := nondegenerate_comp_unit_shift_of_isSepClosed _ i hC
  let s := (shiftFunctorAdd' (DerivedCategoryModule Λ (Spec (.of k))) (2 * d : ℤ) (j - 2 * d) j
    (by omega)).app ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))
  refine LinearMap.isPerfPair_of_comp (Finite.isField_of_domain Λ) _ (fun y ↦ g (y ≫ s.hom))
    (g.bijective.comp ⟨fun y y' h ↦ (cancel_mono s.hom).1 h, fun z ↦ ⟨z ≫ s.inv, by simp⟩⟩)
    (by simp) ℓ
    (fun z hz ↦ ℓ.injective (hz.trans ℓ.map_zero.symm)) (fun x y ↦ ?_) h₁ h₂
  rw [LinearMap.compr₂_apply, degreewisePoincarePairing_apply, degreewisePairing_apply]
  simp only [Category.assoc]
  rw [hg x]
  rfl

omit [LocallyOfFiniteType a] in
/-- Blueprint `theorem-poincare-duality--8`: Proper Poincaré duality (degreewise form,
finite-field case).

In the situation of
`AlgebraicGeometry.Etale.TateOrientation.isPerfPair_degreewisePoincarePairing`, if moreover `a`
is proper, then for `i + j = 2d` the degreewise pairing

`H^i(X, K) × H^j(X, K^∨(d)) ⟶ Λ`,

that is `⟨-, -⟩_i` read on `H^i(X, K) = Hom(Λ_s, (Ra_* K)[i])` through `Ra_! ≅ Ra_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`), is perfect. -/
theorem isPerfPair_degreewisePoincarePairing_of_isProper [IsProper a]
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) (i j : ℤ) (hij : i + j = 2 * d)
    (ℓ : (𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ 𝟙_ _) ≃ₗ[Λ] Λ) :
    (((γ.degreewisePoincarePairing K i j hij).compr₂ ℓ.toLinearMap).compl₁₂
      (Linear.homCongr Λ (Iso.refl _) ((shiftFunctor _ i).mapIso
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ a).app K).symm)).toLinearMap
      (LinearEquiv.refl Λ _).toLinearMap).IsPerfPair :=
  have := γ.isPerfPair_degreewisePoincarePairing hK i j hij ℓ
  inferInstance

end TateOrientation

end Etale

end AlgebraicGeometry
