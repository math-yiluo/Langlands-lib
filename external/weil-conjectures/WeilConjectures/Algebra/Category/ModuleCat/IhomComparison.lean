/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison

/-!
# Exact monoidal functors preserve internal homs out of finitely presented modules

Let `R` be a commutative ring and let `F : ModuleCat R ⥤ D` be a lax monoidal functor to a
braided monoidal closed preadditive category, with invertible unit map, which is additive, left
exact and preserves epimorphisms; for instance the constant sheaf functor on a site. Then for
every finitely presented module `P` the comparison map `F [P, Q] ⟶ [F P, F Q]` is an
isomorphism (`ModuleCat.isIso_ihomComparison_app_of_finitePresentation`): it is one for
`P = R`, hence for the finite free modules, and a finitely presented module is the cokernel of a
morphism of finite free modules.
-/

@[expose] public section

universe u

namespace ModuleCat

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

variable {R : Type u} [CommRing R] {D : Type*} [Category* D] [Preadditive D]
  [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D] [BraidedCategory D]
  (F : ModuleCat.{u} R ⥤ D) [F.LaxMonoidal] [IsIso (ε F)] [F.Additive]
  [PreservesFiniteLimits F] [F.PreservesEpimorphisms]

/-- **An exact monoidal functor preserves internal homs out of finitely presented modules**: the
comparison map `F [P, Q] ⟶ [F P, F Q]` is an isomorphism for a finitely presented module `P`. -/
theorem isIso_ihomComparison_app_of_finitePresentation (P : ModuleCat.{u} R)
    [Module.FinitePresentation R P] (Q : ModuleCat.{u} R) :
    IsIso ((ihomComparison F P).app Q) := by
  have hfree (n : ℕ) : IsIso ((ihomComparison F (ModuleCat.of R (Fin n → R))).app Q) := by
    have (_ : Fin n) : IsIso ((ihomComparison F (𝟙_ (ModuleCat.{u} R))).app Q) :=
      isIso_ihomComparison_app_unit F Q
    have := @isIso_ihomComparison_app_biproduct _ _ _ _ _ _ _ _ F _ _ _ _ _ _ _ _
      (fun _ : Fin n ↦ 𝟙_ (ModuleCat.{u} R)) _ Q this
    let e : (⨁ fun _ : Fin n ↦ 𝟙_ (ModuleCat.{u} R)) ≅ ModuleCat.of R (Fin n → R) :=
      biproductIsoPi _
    exact (isIso_ihomComparison_app_iff_of_iso_left F e Q).1 inferInstance
  obtain ⟨n, m, π, g, hπ, hexact⟩ := Module.FinitePresentation.exists_fin' R P
  let S : ShortComplex (ModuleCat.{u} R) := ShortComplex.mk (ofHom g) (ofHom π)
    (ModuleCat.hom_ext (LinearMap.ext hexact.apply_apply_eq_zero))
  have hS : S.Exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hexact
  have : Epi S.g := (ModuleCat.epi_iff_surjective _).2 hπ
  have := hfree n
  have := hfree m
  have : Epi (F.map S.g) := F.map_epi _
  exact isIso_ihomComparison_app_of_isColimit F S.zero hS.gIsCokernel Q

end ModuleCat

namespace Module.Finite

/-- Over a noetherian ring, the module of linear maps between finitely generated modules is
finitely generated: it embeds into `(Rⁿ →ₗ N) ≅ Nⁿ` along a surjection `Rⁿ ⟶ M`. -/
theorem linearMap_of_isNoetherianRing {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [AddCommGroup N] [Module R N]
    [Module.Finite R N] : Module.Finite R (M →ₗ[R] N) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact Module.Finite.of_injective (LinearMap.lcomp R N f) fun a b h ↦
    (LinearMap.cancel_right hf).1 h

end Module.Finite
