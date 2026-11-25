/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.SelfInjective
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism.Point

/-!
# Finite-level Poincaré duality for the cohomology of the constant sheaf

Let `k` be separably closed, `a : X ⟶ Spec k` proper with a Tate orientation `γ` of relative
dimension `d`, and `Λ` a finite self-injective cogenerating coefficient ring (e.g. `ℤ/ℓᵐ`)
whose characteristic is invertible on `X`. Write `H^n(X, Λ) = Hom(Λ_X, Λ_X[n])`. For
`i + j = 2d` there is a biadditive pairing `H^i(X, Λ) × H^j(X, Λ) ⟶ Λ` which is nondegenerate on
both sides (`AlgebraicGeometry.Etale.TateOrientation.exists_nondegenerate_unitPairing`): it is the
degreewise Poincaré pairing of `K = Λ_X`
(`AlgebraicGeometry.Etale.TateOrientation.injective_degreewisePoincarePairing`) read through
`H^i_c(X, Λ) ≅ H^i(X, Λ)` (`a` proper), `Λ_X^∨(d) ≅ Λ_X` (the Tate twists are trivial over a
separably closed field) and `End(Λ_s) ≅ Λ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

/-- Composition with an isomorphism, as an additive equivalence of Hom groups. -/
@[simps!]
def _root_.CategoryTheory.Iso.postcompAddEquiv {C : Type*} [Category C] [Preadditive C]
    {X Y Y' : C} (e : Y ≅ Y') : (X ⟶ Y) ≃+ (X ⟶ Y') :=
  AddEquiv.mk' ((Iso.refl X).homCongr e) fun f g ↦ by simp

variable {Λ : Type (u + 1)} [CommRing Λ] {k : Type u} [Field k] [IsSepClosed k]

variable (Λ) in
/-- Over a connected scheme, `r ↦ r • 𝟙` identifies `Λ` with the endomorphisms of `Λ_X`. -/
noncomputable def endUnitAddEquiv (X : Scheme.{u}) [ConnectedSpace X] :
    Λ ≃+ (𝟙_ (DerivedCategoryModule Λ X) ⟶ 𝟙_ (DerivedCategoryModule Λ X)) :=
  AddEquiv.ofBijective (AddMonoidHom.mk' (fun r : Λ ↦ r • 𝟙 (𝟙_ (DerivedCategoryModule Λ X)))
    fun r s ↦ add_smul r s _) (bijective_smul_id_unit Λ X)

variable (Λ) in
/-- The coefficient dual of the unit is the unit: `RHom(Λ_X, Λ_X) ≅ Λ_X`. -/
noncomputable def coefficientDualUnitIso (X : Scheme.{u}) :
    (DerivedCategory.coefficientDual _ X).obj (op (𝟙_ (DerivedCategoryModule Λ X))) ≅
      𝟙_ (DerivedCategoryModule Λ X) :=
  (((derivedTensorHomAdjunction _ (𝟙_ (DerivedCategoryModule Λ X))).ofNatIsoLeft
    (derivedTensorLeftUnitorNatIso _ X)).rightAdjointUniq Adjunction.id).app _

variable [HasTateTwist Λ] [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}}
  [HasInvertibleExponent Λ X]

/-- Over a separably closed field, the twisted dual of the unit is the unit: `Λ_X^∨(d) ≅ Λ_X`. -/
theorem nonempty_twistedDual_unit_iso (a : X ⟶ Spec (.of k)) (d : ℕ) :
    Nonempty (twistedDual Λ d (𝟙_ (DerivedCategoryModule Λ X)) ≅
      𝟙_ (DerivedCategoryModule Λ X)) := by
  obtain ⟨e⟩ := nonempty_tateObject_iso_unit Λ k (d : ℤ)
  exact ⟨((derivedTensor _ X).mapIso (coefficientDualUnitIso Λ X)).app _ ≪≫
    derivedTensorLeftUnitor _ X _ ≪≫ (leftDerivedUpperStarTateObjectIso a (d : ℤ)).symm ≪≫
    (L((a)^*[ModuleCat.{u + 1} Λ])).mapIso e ≪≫ leftDerivedUpperStarConstantComplexIso Λ a⟩

variable [Finite Λ] [Module.Injective Λ Λ] {a : X ⟶ Spec (.of k)} [HasCompactification a]
  [IsProper a] {d : ℕ}

namespace TateOrientation

/-- **Finite-level Poincaré duality for the constant sheaf** (finite level of blueprint
`theorem-poincare-duality--9`, for `K = Λ_X`). Let `k` be separably closed, `a : X ⟶ Spec k` proper
with a Tate orientation `γ` of relative dimension `d`, and `Λ` a finite self-injective cogenerating
ring. For `i + j = 2d` there is a biadditive pairing `H^i(X, Λ) × H^j(X, Λ) ⟶ Λ`,
`H^n(X, Λ) = Hom(Λ_X, Λ_X[n])`, which is nondegenerate on both sides: the degreewise Poincaré
pairing of `Λ_X` read through `H^i_c = H^i`, `Λ_X^∨(d) ≅ Λ_X` and `End(Λ_s) ≅ Λ`. -/
theorem exists_nondegenerate_unitPairing
    (hcog : ∀ (M : ModuleCat.{u + 1} Λ) (x : M), x ≠ 0 → ∃ χ : M →ₗ[Λ] Λ, χ x ≠ 0)
    (γ : TateOrientation Λ a d) (i j : ℤ) (hij : i + j = 2 * d) :
    ∃ P : (𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦i⟧) →+
        (𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦j⟧) →+ Λ,
      (∀ x, (∀ y, P x y = 0) → x = 0) ∧ (∀ y, (∀ x, P x y = 0) → y = 0) := by
  obtain ⟨eT⟩ := nonempty_twistedDual_unit_iso (Λ := Λ) a d
  obtain ⟨h₁, h₂⟩ := γ.injective_degreewisePoincarePairing hcog (𝟙_ _) i j hij
  let B := γ.degreewisePoincarePairing (𝟙_ _) i j hij
  let eI := cohomologyAddEquivCompactSupport a (leftDerivedUpperStarConstantComplexIso Λ a) i
  let eJ := (cohomologyAddEquivCompactSupport a
    (leftDerivedUpperStarConstantComplexIso Λ a) j).trans
      ((shiftFunctor _ j).mapIso
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ a).app _ ≪≫
          (R((a)_*[ModuleCat.{u + 1} Λ])).mapIso eT.symm)).postcompAddEquiv
  let eΛ := (endUnitAddEquiv Λ (Spec (.of k))).symm
  refine ⟨AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk' (fun y ↦ eΛ (B (eI x) (eJ y)))
    fun y y' ↦ by simp) fun x x' ↦ by ext y; simp, fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · refine eI.injective (h₁ ?_)
    ext y'
    obtain ⟨y, rfl⟩ := eJ.surjective y'
    simpa using hx y
  · refine eJ.injective (h₂ ?_)
    ext x'
    obtain ⟨x, rfl⟩ := eI.surjective x'
    simpa using hy x

end TateOrientation

end AlgebraicGeometry.Etale
