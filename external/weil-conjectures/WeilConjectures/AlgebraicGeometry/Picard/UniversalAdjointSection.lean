/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FiniteFibre
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme

/-!
# The adjoint section of the normalized universal module

Let `k` be a separably closed field, `X` a smooth proper geometrically integral curve of genus
`g` over `k` with a rational point `σ`, and let `D ⊆ X_T` be a point of `Hilb^g_{X/k}(T)`, e.g.
the universal divisor over `T = H = Hilb^g_{X/k}`. This file complements the per-`T` statement
`AlgebraicGeometry.zeroLocus_directImageCounit_eq_of_iso` on the open chart of divisors of
degree `g`:

* `AlgebraicGeometry.isQuasicoherent_pushforward_dual_toModules`: the direct image
  `𝒩 = f_{T,*} 𝒪(D)` is a quasi-coherent `𝒪_T`-module;
* `AlgebraicGeometry.Scheme.Modules.nonempty_tensorObj_dual_pullback_pushforward_iso`: if
  `ℒ ≅ 𝒪(D) ⊗ f_T^* ℳ` with `ℳ` invertible and `f_{T,*} 𝒪(D)` invertible, then
  `ℒ ⊗ f_T^* (f_{T,*} ℒ)^{-1} ≅ 𝒪(D) ⊗ f_T^* (f_{T,*} 𝒪(D))^{-1}` (the `σ`-terms cancel);
* `AlgebraicGeometry.zeroLocus_adjointSection_eq_of_iso`: for `ℒ ∈ F(T)` with
  `ℒ ≅ 𝒪(D) ⊗ f_T^* 𝒩`, the section of `ℒ ⊗ f_T^* 𝒩^{-1}` adjoint to `𝒩 ≅ f_{T,*} ℒ` has zero
  scheme `D`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme

/-- The pullback of the class of an invertible module is the class of its pullback. -/
lemma Scheme.Pic.map_ofIsInvertible {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules)
    [M.IsInvertible] :
    Pic.map g (Pic.ofIsInvertible M) = Pic.ofIsInvertible ((Modules.pullback g).obj M) :=
  (Pic.eq_ofIsInvertible_iff _ _).2
    ⟨fromSkeletonToSkeletonIso _ ≪≫ (Modules.pullback g).mapIso (Pic.ofIsInvertibleIso M)⟩

/-- **The `σ`-terms cancel.** Let `π: Y ⟶ T`, let `ℒ` and `𝒪(D)` be invertible `𝒪_Y`-modules
with `ℒ ≅ 𝒪(D) ⊗ π^* ℳ` for an invertible `𝒪_T`-module `ℳ`, and assume `π_* 𝒪(D)` is
invertible. Then `π_* ℒ ≅ π_* 𝒪(D) ⊗ ℳ` (projection formula) and

  `ℒ ⊗ π^* (π_* ℒ)^{-1} ≅ 𝒪(D) ⊗ π^* (π_* 𝒪(D))^{-1}`. -/
theorem Scheme.Modules.nonempty_tensorObj_dual_pullback_pushforward_iso {Y T : Scheme.{u}}
    (π : Y ⟶ T) (L OD : Y.Modules) [L.IsInvertible] [OD.IsInvertible] (M : T.Modules)
    [M.IsInvertible] [((pushforward π).obj OD).IsInvertible]
    (e : L ≅ OD ⊗ (pullback π).obj M) :
    Nonempty (L ⊗ (pullback π).obj ((pushforward π).obj L)ᵛ ≅
      OD ⊗ (pullback π).obj ((pushforward π).obj OD)ᵛ) := by
  obtain ⟨p⟩ := nonempty_pushforward_tensorObj_pullback_iso π OD M
  let p' := (pushforward π).mapIso e ≪≫ p
  have : ((pushforward π).obj L).IsInvertible := IsInvertible.of_iso p'.symm
  apply Pic.nonempty_iso_of_ofIsInvertible_eq
  rw [Pic.ofIsInvertible_tensorObj, Pic.ofIsInvertible_tensorObj, ← Pic.map_ofIsInvertible,
    ← Pic.map_ofIsInvertible, Pic.ofIsInvertible_dual, Pic.ofIsInvertible_dual,
    Pic.ofIsInvertible_eq_of_iso p', Pic.ofIsInvertible_eq_of_iso e,
    Pic.ofIsInvertible_tensorObj, Pic.ofIsInvertible_tensorObj, ← Pic.map_ofIsInvertible,
    ← Pic.mapHom_apply, ← Pic.mapHom_apply, ← Pic.mapHom_apply, map_inv, map_inv, map_mul]
  group

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **`𝒩 = f_{T,*} 𝒪(D)` is quasi-coherent.** For a proper `k`-scheme `X`, a `k`-scheme `T` and
an effective Cartier divisor `D ⊆ X_T` (e.g. a point of `Hilb^g_{X/k}(T)`, such as the universal
divisor over `T = H`), the direct image `f_{T,*} 𝒪(D)` along `f_T: X_T ⟶ T` is a
quasi-coherent `𝒪_T`-module. -/
theorem isQuasicoherent_pushforward_dual_toModules [IsProper (X ↘ Spec (.of k))]
    (T : Over (Spec (.of k))) {D : (Limits.pullback (X ↘ Spec (.of k)) T.hom).IdealSheafData}
    (hD : D.IsInvertible) :
    SheafOfModules.IsQuasicoherent (R := T.left.ringCatSheaf)
      ((Modules.pushforward (Limits.pullback.snd (X ↘ Spec (.of k)) T.hom)).obj
        D.toModulesᵛ) :=
  have := hD.isInvertible_dual_toModules
  Modules.isQuasicoherent_pushforward _ _

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [GeometricallyIntegral (X ↘ Spec (.of k))]

attribute [local instance] instSmoothOfSmoothOfRelativeDimensionOfNatNat_weilConjectures

/-- **The adjoint section has zero scheme `D`.** Let `ℒ ∈ F(T)` and let `D` be a point of
`Hilb^g_{X/k}(T)` with `ℒ ≅ 𝒪(D) ⊗ f_T^* N` for an invertible `𝒪_T`-module `N` (for the
normalized universal module `ℒ_H` over the open `W ⊆ H` where it lies in `F`, `D = D_univ|_W`).
Let `𝒩` be an invertible `𝒪_T`-module with `i: 𝒩 ≅ f_{T,*} ℒ`, i.e. `Rf_{T,*} ℒ ≅ 𝒩[0]`, and let
`s ∈ H⁰(X_T, ℒ ⊗ f_T^* 𝒩^{-1})` be the section adjoint to the adjunction map `f_T^* 𝒩 ⟶ ℒ`
(`AlgebraicGeometry.Scheme.Modules.Hom.adjointSection`, transported along an identification
`ε: (f_T^* 𝒩)^∨ ≅ f_T^* (𝒩^∨)`). Then `Z(s) = D`. -/
theorem zeroLocus_adjointSection_eq_of_iso
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (T : Over (Spec (.of k)))
    (ℒ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj (op T))
    {D : (Limits.pullback (X ↘ Spec (.of k)) T.hom).IdealSheafData}
    (hD : IsHilbertSubscheme (X ↘ Spec (.of k)) (arithmeticGenus k X) T D)
    (N : T.left.Modules) [SheafOfModules.IsInvertible.{u, u, u} N]
    (e : (fromSkeleton _).obj ℒ.1.1.val ≅
      D.toModulesᵛ ⊗ (Modules.pullback (Limits.pullback.snd (X ↘ Spec (.of k)) T.hom)).obj N)
    (𝒩 : T.left.Modules) [𝒩.IsInvertible]
    (i : 𝒩 ≅ (Modules.pushforward (Limits.pullback.snd (X ↘ Spec (.of k)) T.hom)).obj
      ((fromSkeleton _).obj ℒ.1.1.val))
    (ε : ((Modules.pullback (Limits.pullback.snd (X ↘ Spec (.of k)) T.hom)).obj 𝒩)ᵛ ≅
      (Modules.pullback (Limits.pullback.snd (X ↘ Spec (.of k)) T.hom)).obj 𝒩ᵛ) :
    (Modules.Hom.adjointSection
        ((Modules.pullback (Limits.pullback.snd (X ↘ Spec (.of k)) T.hom)).map i.hom ≫
          Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1) ≫
        (fromSkeleton _).obj ℒ.1.1.val ◁ ε.hom).zeroLocus = D := by
  have := ℒ.1.1.isInvertible
  have := Modules.IsInvertible.of_sheafOfModules ((fromSkeleton _).obj ℒ.1.1.val)
  rw [Modules.Hom.zeroLocus_adjointSection_comp_whiskerLeft,
    ← zeroLocus_directImageCounit_eq_of_iso σ hσ T ℒ hD N e]
  exact Modules.Hom.zeroLocus_eq_of_arrowIso _ _
    (Arrow.isoMk ((Modules.pullback _).mapIso i) (Iso.refl _) (by simp))

end AlgebraicGeometry
