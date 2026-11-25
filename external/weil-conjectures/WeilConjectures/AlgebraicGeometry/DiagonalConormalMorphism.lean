/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DiagonalConormal
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.AlgebraicGeometry.DiagonalConormalDerivationCore

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The sheaf morphism underlying the normalized difference derivation.
Source: Stacks Project, Tag 08S2. Construct the morphism from the universal relative
 differential sheaf by the difference of the two splittings of the square-zero diagonal
 extension; the local kernel calculation gives the displayed normalization.
(blueprint: lem-sc-diagonal-conormal-morphism-exists). -/
theorem exists_diagonalConormalMorphism (f : X ⟶ S) :
    ∃ φ : f.relativeDifferentials ⟶ diagonalConormal f,
      ∀ (U : X.Opens) (W : (pullback f f).Opens)
        (h₁ : W ≤ (pullback.fst f f) ⁻¹ᵁ U)
        (h₂ : W ≤ (pullback.snd f f) ⁻¹ᵁ U)
        (hδ : U ≤ (pullback.diagonal f) ⁻¹ᵁ W)
        (a : Γ(X, U)) (s : Γ(kernel (SheafOfModules.unitToPushforwardObjUnit
          (pullback.diagonal f).toRingCatSheafHom), W)),
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (pullback.diagonal f).toRingCatSheafHom)).val.app (op W) s =
            (pullback.snd f f).appLE U W h₂ a -
              (pullback.fst f f).appLE U W h₁ a →
        (f.relativeDifferentialsDerivation.postcomp φ.val).d (X := op U) a =
          (diagonalConormal f).presheaf.map (homOfLE hδ).op
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
              (pullback.diagonal f))).unit.app
                (kernel (SheafOfModules.unitToPushforwardObjUnit
                  (pullback.diagonal f).toRingCatSheafHom))).val.app (op W) s) := by
  obtain ⟨D, hD⟩ := exists_diagonalConormalDerivation_core f
  let φ : f.relativeDifferentials ⟶ diagonalConormal f :=
    (f.relativeDifferentialsHomEquiv (diagonalConormal f)).symm D
  refine ⟨φ, ?_⟩
  intro U W h₁ h₂ hδ a s hs
  have he := f.relativeDifferentialsHomEquiv_symm_app_d D a
  exact he.trans (hD U W h₁ h₂ hδ a s hs)

end AlgebraicGeometry
