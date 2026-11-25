/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.TowerLimitFiniteOfExact

/-!
# Finiteness of the limit of a homological functor along a Bockstein tower

Let `C` be a `Λ`-linear pretriangulated category, `H : C ⥤ Mod_Λ` a `Λ`-linear homological
functor, `ϖ ∈ Λ` and `L ∈ C`. A *Bockstein tower* of `L` is a sequence of distinguished triangles

`L --ϖⁿ⁺¹--> L --uₙ--> Xₙ --δₙ--> L⟦1⟧`

with morphisms of triangles `(ϖ, 𝟙, tₙ)` from the `(n + 1)`-st to the `n`-th one, `ϖⁿ⁺¹` killing
`Xₙ`. In `D(Λ)` (or `D(Y_ét, Λ)`, followed by a stalk functor and a cohomology functor) the
reductions `Xₙ = L ⊗ᴸ Λ ⧸ ϖⁿ⁺¹` form such a tower.

`CategoryTheory.Pretriangulated.finite_limit_of_bockstein`: if `Λ` is noetherian and
`ϖ`-adically complete, `H(L) ⧸ ϖ` is finite and the `ϖ`-torsion of `H(L⟦1⟧)` is finitely
generated, then `lim_n H(Xₙ)` is a finite `Λ`-module. This is
`ModuleCat.finite_limit_of_exact_tateSubmodule` applied to the long exact sequences
`H(L) --ϖⁿ⁺¹--> H(L) ⟶ H(Xₙ) ⟶ H(L⟦1⟧)`.
-/

@[expose] public section

universe u v w w'

open CategoryTheory Limits Opposite

namespace CategoryTheory.Pretriangulated

variable {C : Type w} [Category.{w'} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {Λ : Type u} [CommRing Λ] [Linear Λ C]
  (H : C ⥤ ModuleCat.{v} Λ) [H.IsHomological] [H.Linear Λ]
  {ϖ : Λ} {L : C} {X : ℕ → C} (u : ∀ n, L ⟶ X n) (δ : ∀ n, X n ⟶ L⟦(1 : ℤ)⟧)
  (t : ∀ n, X (n + 1) ⟶ X n)

omit [Linear Λ C] [H.Linear Λ] in
/-- **Finiteness of the limit along a Bockstein tower**, in a form where the multiplications by
powers of `ϖ` are only recognised after applying `H`: the triangles are
`L --mₙ--> L --uₙ--> Xₙ --δₙ--> L⟦1⟧` with `H(mₙ) = ϖⁿ⁺¹`, the morphisms of triangles are
`(aₙ, 𝟙, tₙ)` with `H(aₙ⟦1⟧) = ϖ`, and `ϖⁿ⁺¹` kills `H(Xₙ)`. See
`CategoryTheory.Pretriangulated.finite_limit_of_bockstein`. -/
theorem finite_limit_of_bockstein_of_map [IsNoetherianRing Λ]
    [IsAdicComplete (Ideal.span {ϖ}) Λ] (m a : ∀ _ : ℕ, L ⟶ L)
    (hm : ∀ n (y : H.obj L), H.map (m n) y = ϖ ^ (n + 1) • y)
    (ha : ∀ n (y : H.obj (L⟦(1 : ℤ)⟧)), H.map ((a n)⟦(1 : ℤ)⟧') y = ϖ • y)
    (hT : ∀ n, Triangle.mk (m n) (u n) (δ n) ∈ distTriang C)
    (hu : ∀ n, u (n + 1) ≫ t n = u n) (hδ : ∀ n, δ (n + 1) ≫ (a n)⟦(1 : ℤ)⟧' = t n ≫ δ n)
    (hkill : ∀ n (y : H.obj (X n)), ϖ ^ (n + 1) • y = 0)
    [Module.Finite Λ (H.obj L ⧸ (Ideal.span {ϖ} • ⊤ : Submodule Λ (H.obj L)))]
    (hB : (LinearMap.ker (ϖ • LinearMap.id : H.obj (L⟦(1 : ℤ)⟧) →ₗ[Λ] _)).FG) :
    Module.Finite Λ
      ↑(limit (Functor.ofOpSequence (X := fun n ↦ H.obj (X n)) fun n ↦ H.map (t n))) := by
  refine ModuleCat.finite_limit_of_exact_tateSubmodule _ (fun n ↦ (H.map (u n)).hom)
    (fun n ↦ (H.map (δ n)).hom) (fun n y ↦ ?_) (fun n x ↦ ?_) (fun n ↦ ?_) (fun n ↦ ?_)
    hkill hB
  · rw [Functor.ofOpSequence_map_homOfLE_succ]
    change (H.map (u (n + 1)) ≫ H.map (t n)) y = _
    rw [← H.map_comp, hu]
    rfl
  · rw [Functor.ofOpSequence_map_homOfLE_succ]
    change (H.map (t n) ≫ H.map (δ n)) x = _
    rw [← H.map_comp, ← hδ, H.map_comp]
    exact ha n _
  · have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (H.map_distinguished_exact _ (hT n))
    ext y
    rw [LinearMap.mem_ker, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    refine (hex y).trans ⟨fun ⟨b, hb⟩ ↦ ⟨b, Submodule.mem_top, ?_⟩,
      fun ⟨b, _, hb⟩ ↦ ⟨b, ?_⟩⟩
    · rw [← hb]
      exact (hm n b).symm
    · rw [← hb]
      exact hm n b
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (H.map_distinguished_exact _ (rot_of_distTriang _ (hT n)))

/-- **Finiteness of the limit along a Bockstein tower.** For a `Λ`-linear homological functor
`H`, a noetherian `ϖ`-adically complete ring `Λ` and a Bockstein tower
`L --ϖⁿ⁺¹--> L --uₙ--> Xₙ --δₙ--> L⟦1⟧` with transition maps `tₙ : Xₙ₊₁ ⟶ Xₙ` (forming morphisms
of triangles `(ϖ, 𝟙, tₙ)`), if `H(L) ⧸ ϖ` is finite and `H(L⟦1⟧)[ϖ]` is finitely generated, then
`lim_n H(Xₙ)` is a finite `Λ`-module. -/
theorem finite_limit_of_bockstein [IsNoetherianRing Λ] [IsAdicComplete (Ideal.span {ϖ}) Λ]
    [∀ n : ℤ, (shiftFunctor C n).Linear Λ]
    (hT : ∀ n, Triangle.mk (ϖ ^ (n + 1) • 𝟙 L) (u n) (δ n) ∈ distTriang C)
    (hu : ∀ n, u (n + 1) ≫ t n = u n)
    (hδ : ∀ n, δ (n + 1) ≫ (ϖ • 𝟙 L)⟦(1 : ℤ)⟧' = t n ≫ δ n)
    (hkill : ∀ n, ϖ ^ (n + 1) • 𝟙 (X n) = 0)
    [Module.Finite Λ (H.obj L ⧸ (Ideal.span {ϖ} • ⊤ : Submodule Λ (H.obj L)))]
    (hB : (LinearMap.ker (ϖ • LinearMap.id : H.obj (L⟦(1 : ℤ)⟧) →ₗ[Λ] _)).FG) :
    Module.Finite Λ
      ↑(limit (Functor.ofOpSequence (X := fun n ↦ H.obj (X n)) fun n ↦ H.map (t n))) := by
  have hsmul (r : Λ) (Y : C) (y : H.obj Y) : H.map (r • 𝟙 Y) y = r • y := by
    rw [Functor.map_smul, H.map_id]
    rfl
  refine finite_limit_of_bockstein_of_map H u δ t (fun n ↦ ϖ ^ (n + 1) • 𝟙 L)
    (fun _ ↦ ϖ • 𝟙 L) (fun n y ↦ hsmul _ _ y) (fun n y ↦ ?_) hT hu hδ (fun n y ↦ ?_) hB
  · rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    exact hsmul _ _ y
  · rw [← hsmul, hkill, H.map_zero]
    rfl

end CategoryTheory.Pretriangulated
