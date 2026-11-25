/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Modules.Tilde

import WeilConjectures.AlgebraicGeometry.AffineHomComparisonLeft
import WeilConjectures.AlgebraicGeometry.AffineHomComparisonRight
import WeilConjectures.AlgebraicGeometry.AffineHomComparisonRankOne

/-! # Natural affine Hom comparison maps

Source: Stacks Project, Tag 01HV (4)-(5), and Tag 0BQZ.
(blueprint: lem-sc-k3-affine-hom-comparison-maps). -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The forward affine Hom comparison exists for arbitrary modules, is natural
in both arguments, and is invertible when the source is the rank-one module.
Source: Stacks Project, Tag 01HV, lemma-spec-sheaves (4)-(5); Tag 0BQZ,
lemma-regular-immersion-ext, the coefficient comparison.
(blueprint: lem-sc-k3-affine-hom-comparison-maps).

Proof: For modules M,N, on D(a) send a localized linear map h/a^r to the
map M_a -> N_a taking m/a^s to h(m)/a^(r+s). The localization universal
property makes this independent of representatives and linear over A_a.
These maps commute with restriction to smaller principal opens, by the
uniqueness clause of localization, and thus glue to a sheaf morphism from
associated Hom to internal Hom. This construction does not assert that
Hom commutes with localization for arbitrary M. Composing before or after
h commutes with the displayed formula, proving the two naturality squares.
For M=A, evaluation at 1 identifies both sides with associated N, and the
comparison with its identity; this proves invertibility in rank one.
Transport along isoSpec preserves maps, compositions and invertibility.
The formulas also apply to the zero ring and the zero coefficient module. -/
theorem exists_affine_hom_comparison_maps {Y : Scheme.{u}} (U : Y.affineOpens) :
    let A := (Γ(Y, U.1) : Type u)
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    ∃ c : ∀ (M N : ModuleCat.{u} A),
        T.obj (ModuleCat.of A (M ⟶ N)) ⟶
          SheafOfModules.homObj (R := U.1.toScheme.toRingedSpace.sheaf)
            (T.obj M) (T.obj N),
      (∀ (M M' N : ModuleCat.{u} A) (f : M' ⟶ M),
        c M N ≫ SheafOfModules.homObjMap (R := U.1.toScheme.toRingedSpace.sheaf)
          (T.map f) (𝟙 (T.obj N)) =
        T.map (ModuleCat.ofHom (Linear.leftComp A N f)) ≫ c M' N) ∧
      (∀ (M N N' : ModuleCat.{u} A) (g : N ⟶ N'),
        c M N ≫ SheafOfModules.homObjMap (R := U.1.toScheme.toRingedSpace.sheaf)
          (𝟙 (T.obj M)) (T.map g) =
        T.map (ModuleCat.ofHom (Linear.rightComp A M g)) ≫ c M N') ∧
      (∀ N : ModuleCat.{u} A, IsIso (c (ModuleCat.of A A) N)) := by
  rw [← affineHomComparisonFunctor_eq U]
  dsimp only
  exact ⟨affineHomComparison U, affineHomComparison_chart_left U,
    affineHomComparison_chart_right U, affineHomComparison_chart_rankone U⟩

end AlgebraicGeometry
