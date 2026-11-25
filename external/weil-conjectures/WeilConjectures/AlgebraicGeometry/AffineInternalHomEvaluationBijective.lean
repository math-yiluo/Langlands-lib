/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.InternalHomAffineChartEvaluation
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Evaluation of internal Hom on affine opens

Source: Stacks Project, duality.tex, Tag 0BUZ, lemma-compute-sheafhom-affine.
(blueprint: lem-sc-affine-internal-hom-evaluation-bijective).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

private theorem spec_map_bijective {R : CommRingCat.{u}}
    (M F : (Spec R).Modules) [M.IsQuasicoherent] :
    Function.Bijective (fun φ : M ⟶ F ↦ (moduleSpecΓFunctor (R := R)).map φ) := by
  let adj := tilde.adjunction (R := R)
  have : IsIso (adj.counit.app M) :=
    inferInstanceAs (IsIso (Scheme.Modules.fromTildeΓ M))
  let e := (Iso.homCongr (asIso (adj.counit.app M)).symm (Iso.refl F)).trans
    (adj.homEquiv _ F)
  have he : (fun φ : M ⟶ F ↦ (moduleSpecΓFunctor (R := R)).map φ) = e := by
    funext φ
    dsimp [e, Iso.homCongr, Adjunction.homEquiv]
    simp only [Category.comp_id]
    rw [Functor.map_comp, ← Category.assoc, adj.right_triangle_components, Category.id_comp]
  rw [he]
  exact e.bijective

/-- A morphism from a quasi-coherent module on an affine open is uniquely
specified by its map on sections, even when the target is not quasi-coherent.

Source: Stacks Project, duality.tex, Tag 0BUZ, lemma-compute-sheafhom-affine;
Mathlib, AlgebraicGeometry.tilde.adjunction.
(blueprint: lem-sc-affine-internal-hom-evaluation-bijective).

Proof: Restrict M and F to U. The over-category description of the internal
Hom identifies its sections on U with morphisms of module sheaves on U.
Identify the affine scheme U with Spec Gamma(U,O). Quasi-coherence of M
makes the counit from the tilde of Gamma(U,M) to M invertible. Precompose
with this counit, and apply the tilde/global-sections adjunction, which
holds for every target module sheaf. Its unit identifies the sections of
the tilde with the original module, so the resulting bijection sends a
morphism to its component at U. Both changes of chart and restriction
preserve these components. Thus evaluation at the terminal object of
Over U is bijective. No finite presentation or quasi-coherence of F is used.
For U empty all section modules are zero and the same argument applies. -/
theorem affine_internalHom_evaluation_bijective
    {X : Scheme.{u}} (M F : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective
      (fun φ : (SheafOfModules.homObj M F).val.obj (op U) ↦
        (φ.app (op (Over.mk (𝟙 U)))).hom) := by
  let e := chartHomEquiv M F U hU
  let c :
      ((moduleSpecΓFunctor (R := Γ(X, U))).obj (M.restrict hU.fromSpec) →ₗ[Γ(X, U)]
        (moduleSpecΓFunctor (R := Γ(X, U))).obj (F.restrict hU.fromSpec)) ≃ₗ[Γ(X, U)]
        (Γ(M, U) →ₗ[Γ(X, U)] Γ(F, U)) :=
    LinearEquiv.arrowCongr (chartSectionsEquiv M U hU) (chartSectionsEquiv F U hU)
  have hspec := spec_map_bijective (M.restrict hU.fromSpec) (F.restrict hU.fromSpec)
  have hcomp := c.bijective.comp (ModuleCat.homEquiv.bijective.comp
    (hspec.comp e.bijective))
  have heq :
      (fun φ : (SheafOfModules.homObj M F).val.obj (op U) ↦
        c ((moduleSpecΓFunctor (R := Γ(X, U))).map (e φ)).hom) =
      (fun φ : (SheafOfModules.homObj M F).val.obj (op U) ↦
        (φ.app (op (Over.mk (𝟙 U)))).hom) := by
    funext φ
    exact internalHom_evaluation_chart_compare M F U hU φ
  rw [← heq]
  exact hcomp

end AlgebraicGeometry
