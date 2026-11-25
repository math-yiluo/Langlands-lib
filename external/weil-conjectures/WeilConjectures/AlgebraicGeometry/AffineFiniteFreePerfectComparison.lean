/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineFiniteFreeModelComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Derived comparison for an explicit affine resolution complex

Source: Stacks Project, Tag 068C, and the derived localization construction of Tag 05RU
(blueprint: lem-affine-finite-free-perfect-comparison).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The transported extension-by-zero quasi-isomorphism identifies the derived restriction
with the explicitly constructed local model. No boundedness or freeness is needed.
Source: Stacks Project, Tag 068C, and derived localization, Tag 05RU
(blueprint: lem-affine-finite-free-perfect-comparison).

Proof: Extend `q` along the shape embedding `n ↦ -n`. Extension preserves
quasi-isomorphisms, and the extension of the degree-zero single complex is
canonically a degree-zero integer single complex. Apply the inverse open-site
equivalence termwise; this exact functor preserves quasi-isomorphisms. The derived
localization inverts the resulting morphism. The unit of the open-site equivalence
and `overFunctorEquiv` identify the restricted sheaf with the transported sheaf on
the open subscheme. Commute restriction with the derived single functor, apply
that sheaf isomorphism to the single complex, and commute single with termwise
transport. Compose these three isomorphisms with the inverse of the localized
quasi-isomorphism. All these constructions include the empty open and zero sheaf. -/
theorem affine_finite_free_perfect_comparison {Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (U : Y.Opens) (hU : IsAffineOpen U)
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (K : ChainComplex (ModuleCat.{u} (Γ(Y, U) : Type u)) ℕ)
    (q : ((tilde.functor Γ(Y, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K ⟶ (ChainComplex.single₀ U.toScheme.Modules).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj M)) [QuasiIso q] :
    Nonempty ((SheafOfModules.overFunctor.{u}
        (moduleRings Y.toRingedSpace) U).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M) ≅
        DerivedCategory.Q.obj (affineFiniteFreeModelComplex U hU K)) := by
  let F := (Scheme.Modules.overEquiv U).inverse
  let N := (Scheme.Modules.restrictFunctor U.ι).obj M
  let e₀ := HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat N 0 0 (by simp)
  let φ := HomologicalComplex.extendMap q ComplexShape.embeddingDownNat ≫ e₀.hom
  have : QuasiIso φ := by dsimp [φ]; infer_instance
  let ψ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ
  have : QuasiIso ψ := by dsimp [ψ]; infer_instance
  let eM : (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U).obj M ≅ F.obj N :=
    (Scheme.Modules.overEquiv U).unitIso.app _ ≪≫
      F.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)
  let G := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U
  let e₁ := (G.mapDerivedCategorySingleFunctor 0).app M
  let e₂ := DerivedCategory.Q.mapIso
    ((CochainComplex.singleFunctor _ 0).mapIso eM)
  let e₃ := DerivedCategory.Q.mapIso
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app N)
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃.symm ≪≫ (asIso (DerivedCategory.Q.map ψ)).symm⟩

end AlgebraicGeometry
