/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsFiniteTypeEtaleModuleSheaf
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Locally constant sheaves with finitely generated values are of finite type

Source: Stacks Project, Lemma 093N (1), direction from finite values to finite type
(blueprint: lem-weil-pbc-locally-constant-finite-values-finite-type).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A locally constant sheaf whose local constant values are finitely generated modules is
of finite type. For each supplied isomorphism and generating tuple, the sheafification of
`c ↦ ∑ j, c j • x j`, followed by the inverse isomorphism, is an epimorphism. Its basis
sections are exactly the global sections corresponding to the specified generators.

Proof:
1. On each cover member use the supplied isomorphism to transport the canonical sections
   associated to the generators of the constant value. The displayed linear map sends each
   basis vector to its specified generator (`def-weil-finitely-generated-module`,
   `def-weil-pbc-constant-sheaf`, `def-weil-pbc-etale-module-finite-type`).
2. Every section of the constant sheaf locally comes from an element of the value module
   (`lem-weil-pbc-constant-module-sheaf-sections-locally-constant`). Write that element as a
   linear combination of the generators. Linearity and compatibility with restriction give
   a local lift through the displayed sheaf map, including the zero-generator case.
3. Local surjectivity gives an epimorphism of underlying abelian sheaves
   (`lem-weil-pbc-abelian-sheaf-epi-locally-surjective`). The faithful forgetful functor
   reflects epimorphisms, so this is an epimorphism of module sheaves. On each member choose
   a finite generating tuple; the given etale cover then witnesses finite type
   (`def-weil-pbc-etale-module-finite-type`).

Source: Stacks Project, Lemma 093N (1), first two sentences of the proof; Lemma 093J
(blueprint: lem-weil-pbc-locally-constant-finite-values-finite-type). -/
theorem locallyConstant_finiteValues_isFiniteType
    {Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (𝒰 : Cover.{u} etalePrecoverage Y)
    (M : 𝒰.I₀ → ModuleCat.{u + 1} Λ)
    (hfinite : ∀ i : 𝒰.I₀, Module.Finite Λ (M i))
    (α : ∀ i : 𝒰.I₀, F.over (𝒰.etalePrecoverageToEtale i) ≅
      (constantSheaf (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
        (ModuleCat.{u + 1} Λ)).obj (M i)) :
    IsFiniteTypeEtaleModuleSheaf F ∧
      ∀ (i : 𝒰.I₀) (n : ℕ) (x : Fin n → M i),
        Submodule.span Λ (Set.range x) = ⊤ →
          Epi ((constantSheaf
            (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} Λ)).map
              (ModuleCat.ofHom
                (∑ j : Fin n, (LinearMap.proj j).smulRight (x j) :
                  (Fin n → Λ) →ₗ[Λ] M i)) ≫ (α i).inv) := by
  classical
  have hEpi : ∀ (i : 𝒰.I₀) (n : ℕ) (x : Fin n → M i),
      Submodule.span Λ (Set.range x) = ⊤ →
        Epi ((constantSheaf
          (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} Λ)).map
            (ModuleCat.ofHom
              (∑ j : Fin n, (LinearMap.proj j).smulRight (x j) :
                (Fin n → Λ) →ₗ[Λ] M i)) ≫ (α i).inv) := by
    intro i n x hx
    let f : (Fin n → Λ) →ₗ[Λ] M i :=
      ∑ j : Fin n, (LinearMap.proj j).smulRight (x j)
    have hf : f = Fintype.linearCombination Λ x := by
      ext c
      simp [f, Fintype.linearCombination_apply]
    have hfepi : Epi (ModuleCat.ofHom f) := by
      apply (ModuleCat.epi_iff_surjective _).mpr
      change Function.Surjective f
      rw [hf]
      exact (span_range_eq_top_iff_surjective_fintypeLinearCombination Λ x).mp hx
    infer_instance
  refine ⟨⟨𝒰, ?_⟩, hEpi⟩
  intro i
  let := hfinite i
  obtain ⟨n, x, hx⟩ := Module.Finite.exists_fin (R := Λ) (M := M i)
  exact ⟨n, _, hEpi i n x hx⟩

end AlgebraicGeometry.Scheme
