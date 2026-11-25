/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChangeIsIsoOnAffine

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

/-- The base-change map for an affine morphism and a quasi-coherent module is invertible.
This is the affine computation and locality argument of Stacks Project, Lemma 02KG.
The proof proceeds by restricting to affine charts, identifying the chart with spectra of
rings, and using the tensor identification `R' ⊗[R] M ≅ (R' ⊗[R] B) ⊗[B] M`.
(blueprint: lem-weil-pbc-affine-pushforward-base-change-isIso) -/
theorem affinePushforward_baseChange_isIso {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIso (moduleBaseChangeMap f f' g g' sq.w F) := by
  apply isIso_of_bijective_app_of_isAffineOpen
  exact affinePushforward_baseChange_app_bijective f f' g g' sq F

end
end AlgebraicGeometry.Scheme.Modules
