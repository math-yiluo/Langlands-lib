/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine

/-! # The affine-section flatness of an associated flat module

Source: Stacks Project, Tags 01I9 (affine sections and pullbacks) and 00HT (flatness).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- A flat global-ring module gives an associated module flat over the affine base itself.
This is an affine module/sheaf fact, with no cover, complex or cohomology.
Source: Stacks Project, Tags 01I9 and 00HT.
(blueprint: lem-pc-affine-associated-module-flat-over).

Proof: Write A=Gamma(T,O). The affine chart T -> Spec A is an isomorphism. On an
affine open W of T, the sections of the chart pullback of M tilde identify with
Gamma(W,O) tensor_A M, by the affine pullback formula and the section formula for
tilde. This module is flat over Gamma(W,O) by base change of flat modules. Given
affine W contained in affine Z, the inclusion is a flat morphism, and hence
Gamma(W,O) is flat over Gamma(Z,O). Transitivity gives flatness of the same sections
over Gamma(Z,O). Naturality of the affine pullback formula identifies the action
with the restriction map appearing in IsFlatOver of the identity. These are all
the affine pairs required by that predicate. On empty affine opens the ring and
section module are zero and the same argument applies; zero M is also included.
No quasi-coherence-to-flatness converse for arbitrary sheaves is assumed. -/
theorem flatOver_affineAssociatedModule (T : Scheme.{u}) [IsAffine T]
    (M : ModuleCat.{u} Γ(T, ⊤)) (hM : Module.Flat Γ(T, ⊤) M) :
    ((Modules.pullback T.toSpecΓ).obj ((tilde.functor Γ(T, ⊤)).obj M)).IsFlatOver
      (𝟙 T) := by
  let := hM
  let F := (Modules.pullback T.toSpecΓ).obj ((tilde.functor Γ(T, ⊤)).obj M)
  -- Compute sections through the affine chart of U, preserving the Γ(T, U)-action.
  have hsections (U : T.affineOpens) : Module.Flat Γ(T, U.1) Γ(F, U.1) := by
    let φ := T.presheaf.map U.1.leTop.op
    let : Algebra Γ(T, ⊤) Γ(T, U.1) := φ.hom.toAlgebra
    let e : F.restrict U.2.fromSpec ≅
        (pullback (Spec.map φ)).obj (tilde M) :=
      (restrictFunctorIsoPullback U.2.fromSpec).app F ≪≫
        (pullbackComp U.2.fromSpec T.toSpecΓ).app (tilde M) ≪≫
        (pullbackCongr U.2.fromSpec_toSpecΓ).app (tilde M)
    let eΓ := (moduleSpecΓFunctor.mapIso e).toLinearEquiv
    let e₀ := ModuleCat.tensorEquivExtendScalars Γ(T, ⊤) Γ(T, U.1) M
    let e₁ := tildePullbackΓEquiv φ M
    let e₂ := sectionsRestrictFromSpecLinearEquiv F U.2
    exact Module.Flat.of_linearEquiv (e₀ ≪≫ₗ e₁ ≪≫ₗ eΓ.symm ≪≫ₗ e₂).symm
  -- Restriction between affine opens is flat; compose the two flat module structures.
  intro V U e
  let := ((𝟙 T : T ⟶ T).appLE V.1 U.1 e).hom.toAlgebra
  have : Module.Flat Γ(T, V.1) Γ(T, U.1) :=
    HasRingHomProperty.appLE @Flat (𝟙 T) inferInstance V U e
  have := hsections U
  let : Module Γ(T, V.1) Γ(F, U.1) :=
    Module.compHom _ ((𝟙 T : T ⟶ T).appLE V.1 U.1 e).hom
  have : IsScalarTower Γ(T, V.1) Γ(T, U.1) Γ(F, U.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Flat.trans Γ(T, V.1) Γ(T, U.1) Γ(F, U.1)

end AlgebraicGeometry.Scheme.Modules
