/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! Finite pushforward preserves quasi-coherence and finite type without
Noetherian hypotheses.
(blueprint: lem-pc-f3-finite-pushforward-finite-type)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A finite direct image preserves quasi-coherent modules of finite type on arbitrary
schemes. Source: Stacks Project, Tag 01Y6, finite morphism case, and Tag 01LC.
(blueprint: lem-pc-f3-finite-pushforward-finite-type)

Proof: Finite morphisms are quasi-compact and separated, so the existing qcqs
pushforward theorem proves quasi-coherence. Restriction of a finite-type module
preserves finite type: pull its local generating cover back along the slice forgetful
functor and transport the finite generating families along the colimit-preserving
local functors. On each inverse-image affine open the affine finite-type criterion
therefore gives finite sections. The coordinate ring there is finite over the base
coordinate ring, since the morphism is finite. Restriction of scalars and transitivity
of module finiteness give finite sections of the pushforward on every base affine
open. The affine finite-type criterion on the full affine cover proves finite type.
This also covers empty schemes and the zero module; no Noetherianity is used. -/
theorem isQuasicoherent_and_isFiniteType_pushforward_of_isFinite
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] (F : Y.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    ((pushforward f).obj F).IsQuasicoherent ∧ ((pushforward f).obj F).IsFiniteType := by
  have hp : ((pushforward f).obj F).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated f F
  have hs (U : X.Opens) (hU : IsAffineOpen U) :
      Module.Finite Γ(X, U) Γ((pushforward f).obj F, U) := by
    have hV := hU.preimage f
    have hM : Module.Finite Γ(Y, f ⁻¹ᵁ U) Γ(F, f ⁻¹ᵁ U) :=
      finite_sections_of_finiteType F hV
    let := (f.app U).hom.toAlgebra
    let : Module Γ(Y, f ⁻¹ᵁ U) Γ((pushforward f).obj F, U) :=
      inferInstanceAs (Module Γ(Y, f ⁻¹ᵁ U) Γ(F, f ⁻¹ᵁ U))
    have : Module.Finite Γ(Y, f ⁻¹ᵁ U) Γ((pushforward f).obj F, U) := hM
    have : IsScalarTower Γ(X, U) Γ(Y, f ⁻¹ᵁ U) Γ((pushforward f).obj F, U) :=
      .of_algebraMap_smul fun _ _ ↦ rfl
    have : Module.Finite Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := f.finite_app U hU
    exact Module.Finite.trans Γ(Y, f ⁻¹ᵁ U) Γ((pushforward f).obj F, U)
  have hft : ((pushforward f).obj F).IsFiniteType :=
    ((((quasicoherent_finite_type_affine.{u, u} X).2 _ hp).2.1)
      X.affineOpens (fun U ↦ U.1) (iSup_affineOpens_eq_top X)
      (fun U ↦ U.2) (fun U ↦ hs U.1 U.2)).1
  exact ⟨hp, hft⟩

end AlgebraicGeometry.Scheme.Modules
