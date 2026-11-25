/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.PoincareReduction

/-!
# Reduction of the derived Poincaré pairing from its constituents

Let `Λ, Λ'` be coefficient rings, for instance `A_n = 𝒪_E/ϖⁿ` and `A_m = 𝒪_E/ϖᵐ` with
`m ≤ n`, and let `G : D(Y, Λ) ⥤ D(Y, Λ')` be a lax monoidal change of coefficients, such as the
derived reduction `K ↦ K ⊗ᴸ_{A_n} A_m`. The finite reduction of the Poincaré pairing
(blueprint `theorem-poincare-duality--9`,
`AlgebraicGeometry.Etale.map_inv_curry_poincarePairing_comp`) assumes that the reduction of the
derived Poincaré pairing `β_{K_n}` is the pairing `β_{K_m}` of the reduction. This file reduces
that hypothesis to the constituent squares of the blueprint proof: the reduction of the cup
product, evaluation and shift part of the pairing
(`proposition-six-operations-change-coefficients`), and of the orientation and of the counit of
`Ra_! ⊣ Ra^!` (`proposition-compatibility-purity-change-coefficients`).

## Main statements

- `AlgebraicGeometry.Etale.map_smoothTrace`: the smooth trace reduces.
- `AlgebraicGeometry.Etale.map_poincarePairing`: the reduction of the derived Poincaré pairing is
  the Poincaré pairing of the reduction.

## Implementation notes

As in `WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction`, the coefficient change and its
compatibilities with the operations are arguments: the repository does not provide the coherent
comparisons of the derived reduction with `Ra_!`, `Ra_*` and the coefficient dual.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable (A' : Type*) [Category.{u + 1} A'] [Abelian A'] [IsGrothendieckAbelian.{u + 1} A']
  [MonoidalCategory A'] [MonoidalPreadditive A'] [SymmetricCategory A'] [MonoidalClosed A']
  [Abelian.HasFunctorialFlatResolution A']
  {FA' : A' → A' → Type (u + 1)} {CA' : A' → Type (u + 1)}
  [∀ X Y, FunLike (FA' X Y) (CA' X) (CA' Y)] [ConcreteCategory.{u + 1} A' FA']
  [Etale.UpperStarPreservesFlat A']
  [(CategoryTheory.forget A').ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A')]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A')]

/-- The derived category `D(X_ét, A)` of `A`-valued étale sheaves on `X`. -/
local notation "𝐃(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) A)

namespace Etale

variable {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a] {d : ℕ}
  {P : 𝐃(Y, A) ⥤ 𝐃(X, A)} (adj : R(a)_![A] ⊣ P) {P' : 𝐃(Y, A') ⥤ 𝐃(X, A')}
  (adj' : R(a)_![A'] ⊣ P')

/-- The derived Poincaré pairing before the trace,
`Ra_! K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ Ra_!(T[2d])`: the shift moved out, the mixed-support cup
product, the twisted evaluation and the shift compatibility of `Ra_!`. The derived Poincaré
pairing is this map followed by the smooth trace
(`AlgebraicGeometry.Etale.poincarePairing_eq`). -/
noncomputable def poincarePairingUntraced (d : ℕ) (T K : 𝐃(X, A)) :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).obj
        (((R((a)_*[A])).obj (((derivedTensor A X).obj
          ((DerivedCategory.coefficientDual A X).obj (op K))).obj T))⟦(2 * d : ℤ)⟧) ⟶
      (R(a)_![A]).obj (T⟦(2 * d : ℤ)⟧) :=
  (((derivedTensor A Y).obj ((R(a)_![A]).obj K)).commShiftIso (2 * d : ℤ)).hom.app _ ≫
    (poincarePairingEvaluation a T K)⟦(2 * d : ℤ)⟧' ≫
      ((R(a)_![A]).commShiftIso (2 * d : ℤ)).inv.app _

variable {A a}

/-- The derived Poincaré pairing is the untraced pairing followed by the smooth trace. -/
lemma poincarePairing_eq {T : 𝐃(X, A)} (γ : T⟦(2 * d : ℤ)⟧ ≅ P.obj (𝟙_ _))
    (K : 𝐃(X, A)) :
    poincarePairing adj γ K = poincarePairingUntraced A a d T K ≫ smoothTrace adj γ := by
  simp only [poincarePairing, poincarePairingUntraced, Category.assoc]

variable {A'}

omit [Etale.UpperStarPreservesFlat A] [Etale.UpperStarPreservesFlat A'] in
/-- Blueprint `proposition-compatibility-purity-change-coefficients` (the smooth trace): **the
smooth trace reduces.** Let `G` be a change of coefficients on the base, `ψ : Ra_! ⋙ G ≅ Ψ_X ⋙ Ra_!`
its commutation with `Ra_!`, `e : G Λ_Y ⟶ Λ'_Y`, `v₀ : Ψ_X(T[2d]) ≅ T'[2d]` and
`vω : Ψ_X ω_X ≅ ω'_X`, where `ω_X = P Λ_Y` for the right adjoint `P` of `Ra_!` (for finite
coefficients, `P = Ra^!`). If the orientations `γ : T[2d] ≅ ω_X`, `γ'` reduce (`hγ`) and the
counit of `Ra_! ⊣ P` at `Λ_Y` reduces (`hS`), then `G(Tr_γ) = Tr_{γ'}` read through `ψ`, `v₀`
and `e`. -/
theorem map_smoothTrace (ΨX : 𝐃(X, A) ⥤ 𝐃(X, A')) (G : 𝐃(Y, A) ⥤ 𝐃(Y, A'))
    (ψ : R(a)_![A] ⋙ G ≅ ΨX ⋙ R(a)_![A']) (e : G.obj (𝟙_ _) ⟶ 𝟙_ _) {T : 𝐃(X, A)}
    {T' : 𝐃(X, A')} (γ : T⟦(2 * d : ℤ)⟧ ≅ P.obj (𝟙_ _))
    (γ' : T'⟦(2 * d : ℤ)⟧ ≅ P'.obj (𝟙_ _))
    (v₀ : ΨX.obj (T⟦(2 * d : ℤ)⟧) ≅ T'⟦(2 * d : ℤ)⟧)
    (vω : ΨX.obj (P.obj (𝟙_ _)) ≅ P'.obj (𝟙_ _))
    (hγ : ΨX.map γ.hom ≫ vω.hom = v₀.hom ≫ γ'.hom)
    (hS : ψ.hom.app _ ≫ (R(a)_![A']).map vω.hom ≫
        adj'.counit.app (𝟙_ _) =
      G.map (adj.counit.app (𝟙_ _)) ≫ e) :
    G.map (smoothTrace adj γ) ≫ e =
      ψ.hom.app _ ≫ (R(a)_![A']).map v₀.hom ≫ smoothTrace adj' γ' := by
  have hψ := ψ.hom.naturality γ.hom
  simp only [Functor.comp_obj, Functor.comp_map] at hψ
  simp only [smoothTrace, Functor.map_comp, Category.assoc, ← hS]
  rw [reassoc_of% hψ, ← Functor.map_comp_assoc, hγ, Functor.map_comp_assoc]

/-- Blueprint `theorem-poincare-duality--9` (first assertion): **the reduction of the derived
Poincaré pairing is the Poincaré pairing of the reduction.** Let `G` be a lax monoidal change
of coefficients on the base (for instance `- ⊗ᴸ_{A_n} A_m`), `K ∈ D(X, A)` and `K' ∈ D(X, A')`
(the reduction `K_m` of `K = K_n`), with comparisons `c_X : Ra_! K' ⟶ G(Ra_! K)` (compact
support) and `c_Y : G(Ra_*(K^∨ ⊗ᴸ T)[2d]) ⟶ Ra_*(K'^∨ ⊗ᴸ T')[2d]` (ordinary global sections).
If the cup product, evaluation and shift part of the pairing reduces (`hE`,
`proposition-six-operations-change-coefficients`), and so do the orientation (`hγ`) and the counit
(`hS`) (`proposition-compatibility-purity-change-coefficients`), then `G(β_K)` is `β_{K'}` read
through `c_X`, `c_Y` and `e`. This is the hypothesis of the finite reduction
`AlgebraicGeometry.Etale.map_inv_curry_poincarePairing_comp`. -/
theorem map_poincarePairing (ΨX : 𝐃(X, A) ⥤ 𝐃(X, A')) (G : 𝐃(Y, A) ⥤ 𝐃(Y, A'))
    [G.LaxMonoidal] (ψ : R(a)_![A] ⋙ G ≅ ΨX ⋙ R(a)_![A']) (e : G.obj (𝟙_ _) ⟶ 𝟙_ _)
    {T : 𝐃(X, A)} {T' : 𝐃(X, A')} (γ : T⟦(2 * d : ℤ)⟧ ≅ P.obj (𝟙_ _))
    (γ' : T'⟦(2 * d : ℤ)⟧ ≅ P'.obj (𝟙_ _))
    (v₀ : ΨX.obj (T⟦(2 * d : ℤ)⟧) ≅ T'⟦(2 * d : ℤ)⟧)
    (vω : ΨX.obj (P.obj (𝟙_ _)) ≅ P'.obj (𝟙_ _))
    (hγ : ΨX.map γ.hom ≫ vω.hom = v₀.hom ≫ γ'.hom)
    (hS : ψ.hom.app _ ≫ (R(a)_![A']).map vω.hom ≫
        adj'.counit.app (𝟙_ _) =
      G.map (adj.counit.app (𝟙_ _)) ≫ e)
    {K : 𝐃(X, A)} {K' : 𝐃(X, A')}
    (cX : (R(a)_![A']).obj K' ⟶ G.obj ((R(a)_![A]).obj K))
    (cY : G.obj (((R((a)_*[A])).obj (((derivedTensor A X).obj
        ((DerivedCategory.coefficientDual A X).obj (op K))).obj T))⟦(2 * d : ℤ)⟧) ⟶
      ((R((a)_*[A'])).obj (((derivedTensor A' X).obj
        ((DerivedCategory.coefficientDual A' X).obj (op K'))).obj T'))⟦(2 * d : ℤ)⟧)
    (hE : cX ▷ _ ≫ μ G _ _ ≫ G.map (poincarePairingUntraced A a d T K) ≫ ψ.hom.app _ ≫
        (R(a)_![A']).map v₀.hom =
      (R(a)_![A']).obj K' ◁ cY ≫ poincarePairingUntraced A' a d T' K') :
    (R(a)_![A']).obj K' ◁ cY ≫ poincarePairing adj' γ' K' =
      cX ▷ _ ≫ μ G _ _ ≫ G.map (poincarePairing adj γ K) ≫ e := by
  simp only [poincarePairing_eq, Functor.map_comp, Category.assoc]
  rw [map_smoothTrace adj adj' ΨX G ψ e γ γ' v₀ vω hγ hS, ← reassoc_of% hE]

end Etale

end AlgebraicGeometry
