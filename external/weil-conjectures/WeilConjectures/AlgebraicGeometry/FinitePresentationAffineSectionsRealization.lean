/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine

/-! # Realizing affine algebraic module models
Source: Stacks Project, Tags 01ZR and 05N7. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

open Scheme.Modules

/-- Realize an algebraic finite-presentation model of sections as an affine sheaf.
Source: Stacks Project, Modules on Schemes Tag 01I6; Limits Tag 01ZR, affine proof.
(blueprint: lem-pc-fp-affine-sections-realization).

Proof: Transport Q to Spec of the global-section ring of X and take its associated
quasi-coherent sheaf; pull it back along the canonical isomorphism X to that
spectrum. A finite presentation of Q gives a finite global presentation of the
associated sheaf, so it is finitely presented. The affine pullback/tensor comparison
identifies the sections of its pullback along g with scalar extension of Q.
Compose this with e. Both sheaves on Y are quasi-coherent, hence the affine module
equivalence lifts that section isomorphism to an isomorphism of sheaves. The
construction uses Q itself and its associated sheaf, not an arbitrary witness of
existence. Empty affine schemes and zero modules follow from the same equivalence. -/
theorem exists_finitePresentation_affine_sections_realization
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : Y ⟶ X)
    (P : Y.Modules) (hPq : P.IsQuasicoherent)
    (Q : ModuleCat.{u} Γ(X, ⊤)) (hQ : Module.FinitePresentation Γ(X, ⊤) Q)
    (e : Nonempty ((ModuleCat.extendScalars g.appTop.hom).obj Q ≅
      ModuleCat.of Γ(Y, ⊤) Γ(P, ⊤))) :
    ∃ N : X.Modules, N.IsFinitePresentation ∧ N.IsQuasicoherent ∧
      Nonempty ((Scheme.Modules.pullback g).obj N ≅ P) := by
  let TX := tilde.functor Γ(X, ⊤)
  let TY := tilde.functor Γ(Y, ⊤)
  let RX := restrictFunctor X.isoSpec.hom
  let RY := restrictFunctor Y.isoSpec.hom
  let B := restrictFunctor Y.isoSpec.inv
  let N := RX.obj (TX.obj Q)
  obtain ⟨s, hs, t, ht⟩ := hQ.out
  let pres := presentationTilde Q (s : Set Q) hs (t : Set _) ht
  have : pres.IsFinite :=
    { isFiniteType_generators := ⟨inferInstanceAs (Finite (s : Set Q))⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite (t : Set (s →₀ Γ(X, ⊤))))⟩ }
  have : (TX.obj Q).IsFinitePresentation := pres.isFinitePresentation
  have : N.IsFinitePresentation := by dsimp [N, RX]; infer_instance
  refine ⟨N, this, inferInstance, ?_⟩
  let comparison : RX ⋙ Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback (Spec.map g.appTop) ⋙ RY :=
    Functor.isoWhiskerRight (restrictFunctorIsoPullback X.isoSpec.hom)
      (Scheme.Modules.pullback g) ≪≫
      pullbackComp g X.isoSpec.hom ≪≫
      pullbackCongr (Scheme.isoSpec_hom_naturality g).symm ≪≫
      (pullbackComp Y.isoSpec.hom (Spec.map g.appTop)).symm ≪≫
      Functor.isoWhiskerLeft (Scheme.Modules.pullback (Spec.map g.appTop))
        (restrictFunctorIsoPullback Y.isoSpec.hom).symm
  let baseIso : (Scheme.Modules.pullback g).obj N ≅
      RY.obj (TY.obj ((ModuleCat.extendScalars g.appTop.hom).obj Q)) :=
    comparison.app (TX.obj Q) ≪≫
      RY.mapIso ((tildePullbackIso g.appTop).app Q)
  have : P.IsQuasicoherent := hPq
  have : (B.obj P).IsQuasicoherent := by dsimp [B]; infer_instance
  have : IsIso (fromTildeΓ (B.obj P)) := isIso_fromTildeΓ_of_isQuasicoherent _
  let sectionsIso : moduleSpecΓFunctor.obj (B.obj P) ≅
      ModuleCat.of Γ(Y, ⊤) Γ(P, ⊤) := by
    apply LinearEquiv.toModuleIso
    change moduleSpecΓFunctor.obj (P.restrict Y.isoSpec.inv) ≃ₗ[Γ(Y, ⊤)] Γ(P, ⊤)
    let a := moduleSpecΓFunctor.mapIso
      ((restrictFunctorCongr (IsAffineOpen.fromSpec_top (X := Y))).app P)
    exact a.toLinearEquiv.symm ≪≫ₗ
      sectionsRestrictFromSpecLinearEquiv P (isAffineOpen_top Y)
  let cancel : B ⋙ RY ≅ 𝟭 Y.Modules :=
    (restrictFunctorComp Y.isoSpec.hom Y.isoSpec.inv).symm ≪≫
      restrictFunctorCongr Y.isoSpec.hom_inv_id ≪≫ restrictFunctorId
  obtain ⟨e⟩ := e
  exact ⟨baseIso ≪≫ RY.mapIso (TY.mapIso (e ≪≫ sectionsIso.symm)) ≪≫
    RY.mapIso (asIso (fromTildeΓ (B.obj P))) ≪≫ cancel.app P⟩

end AlgebraicGeometry

set_option linter.style.longLine false
