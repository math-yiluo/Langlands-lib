/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Extending affine section maps

Source: Stacks Project, Schemes, Lemma 01IB; Properties, Lemma 01PM.
(blueprint: lem-weil-pbc-affine-section-linear-map-extension).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

namespace Modules

private lemma quasicoherent_pushforward_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  let A := (pushforward f).obj M
  let e : A ≅ M.restrict (inv f) :=
    (restrictFunctorId.app A).symm ≪≫
      (restrictFunctorCongr (IsIso.inv_hom_id f)).symm.app A ≪≫
      (restrictFunctorComp (inv f) f).app A ≪≫
      (restrictFunctor (inv f)).mapIso ((restrictFunctorAdjCounitIso f).app M)
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso e.symm inferInstance

private lemma fromTildeΓ_app_toOpen_any {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (m : Γ(M, ⊤)) :
    M.fromTildeΓ.app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m) = m := by
  have h := congr($(toOpen_fromTildeΓ_app M ⊤) m)
  refine h.trans ?_
  change M.presheaf.map (homOfLE le_top).op m = m
  rw [show (homOfLE le_top : (⊤ : (Spec R).Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

private lemma exists_hom_app_top_eq_any {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} [M.IsQuasicoherent]
    (χ : moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N) :
    ∃ φ : M ⟶ N, ∀ m : Γ(M, ⊤), φ.app ⊤ m = χ m := by
  have : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  refine ⟨inv M.fromTildeΓ ≫ tilde.map χ ≫ N.fromTildeΓ, fun m ↦ ?_⟩
  have hm : (inv M.fromTildeΓ).app ⊤ m = tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m := by
    have k : ∀ x, (inv M.fromTildeΓ).app ⊤ (M.fromTildeΓ.app ⊤ x) = x := fun x ↦
      congr($(IsIso.hom_inv_id M.fromTildeΓ).app ⊤ x)
    exact (congrArg ((inv M.fromTildeΓ).app ⊤) (fromTildeΓ_app_toOpen_any M m)).symm.trans (k _)
  change N.fromTildeΓ.app ⊤ ((tilde.map χ).app ⊤ ((inv M.fromTildeΓ).app ⊤ m)) = χ m
  rw [hm]
  have h₂ : (tilde.map χ).app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m) =
      tilde.toOpen (moduleSpecΓFunctor.obj N) ⊤ (χ m) :=
    congr($(tilde.toOpen_map_app χ ⊤) m)
  rw [h₂]
  exact fromTildeΓ_app_toOpen_any N (χ m)

private lemma exists_hom_app_top_eq_any' {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} [M.IsQuasicoherent]
    (g : Γ(M, ⊤) →+ Γ(N, ⊤))
    (hsmul : ∀ (a : R) (m : Γ(M, ⊤)),
      g (((ΓSpecIso R).inv ≫ (Spec R).presheaf.map
        (homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤)).op).hom a • m) =
        ((ΓSpecIso R).inv ≫ (Spec R).presheaf.map
          (homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤)).op).hom a • g m) :
    ∃ φ : M ⟶ N, ∀ m : Γ(M, ⊤), φ.app ⊤ m = g m := by
  let X := moduleSpecΓFunctor.obj M
  let Y := moduleSpecΓFunctor.obj N
  exact exists_hom_app_top_eq_any (@ModuleCat.ofHom R _ X Y _ X.isModule _ Y.isModule
    { toFun := g
      map_add' := g.map_add
      map_smul' a m := hsmul a m })

private lemma exists_hom_app_top_eq_of_isAffine_any
    {X : Scheme.{u}} [IsAffine X] {M N : X.Modules} [M.IsQuasicoherent]
    (χ : Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(N, ⊤)) :
    ∃ φ : M ⟶ N, ∀ m : Γ(M, ⊤), φ.app ⊤ m = χ m := by
  have := quasicoherent_pushforward_iso X.toSpecΓ M
  obtain ⟨φ', hφ'⟩ := exists_hom_app_top_eq_any' (M := (pushforward X.toSpecΓ).obj M)
    (N := (pushforward X.toSpecΓ).obj N) χ.toAddMonoidHom fun a m ↦ by
      have key (P : X.Modules) (x : Γ((pushforward X.toSpecΓ).obj P, ⊤)) :
          ((ΓSpecIso Γ(X, ⊤)).inv ≫ (Spec Γ(X, ⊤)).presheaf.map
            (homOfLE (le_top : (⊤ : (Spec Γ(X, ⊤)).Opens) ≤ ⊤)).op).hom a • x =
            (a • (show Γ(P, ⊤) from x) : Γ(P, ⊤)) := by
        change X.toSpecΓ.appTop ((ΓSpecIso Γ(X, ⊤)).inv a) •
          (show Γ(P, ⊤) from x) = a • (show Γ(P, ⊤) from x)
        have h2 : X.toSpecΓ.appTop ((ΓSpecIso Γ(X, ⊤)).inv a) = a := by
          rw [← CommRingCat.comp_apply, toSpecΓ_appTop, Iso.inv_hom_id]
          rfl
        rw [h2]
      exact (congrArg χ (key M m)).trans ((χ.map_smul a m).trans (key N (χ m)).symm)
  refine ⟨(pushforward X.toSpecΓ).preimage φ', fun m ↦ ?_⟩
  have := congr(Hom.app $((pushforward X.toSpecΓ).map_preimage φ') ⊤ m)
  exact this.trans (hφ' m)

end Modules

/-- A linear map on an affine open extends from a quasi-coherent source to a sheaf map.

Source: Stacks Project, Schemes, Lemma 01IB (affine equivalence), and Properties,
Lemma 01PM (passing from linear maps to sheaf maps).
(blueprint: lem-weil-pbc-affine-section-linear-map-extension).

Proof: Identify V with Spec R, R = O_X(V). Quasi-coherence identifies P|V with
Gamma(V,P) tilde. The tilde-Gamma adjunction sends f to a morphism from this
tilde module into Q|V; compose with the inverse of the source identification.
The unit identity of the adjunction says its value on every global section b
is f(b). Transport back along V = Spec R and the equivalence between modules
on V and modules over the category of opens below V. The target need not be
quasi-coherent, since the adjunction applies to every sheaf of modules.
The construction works also when V is empty or P or Q is zero. -/
theorem affine_section_linear_map_extension
    {X : Scheme.{u}} (P Q : X.Modules) [P.IsQuasicoherent]
    (V : X.affineOpens) (f : Γ(P, V.1) →ₗ[Γ(X, V.1)] Γ(Q, V.1)) :
    ∃ φ : P.over V.1 ⟶ Q.over V.1,
      ∀ b : Γ(P, V.1), φ.val.app (op (Over.mk (homOfLE (le_refl V.1)))) b =
        f b := by
  let U := V.1
  let χ₀ : Γ(P, U.ι ''ᵁ ⊤) →ₗ[Γ(X, U.ι ''ᵁ ⊤)] Γ(Q, U.ι ''ᵁ ⊤) :=
    U.ι_image_top.symm ▸ f
  let χ : Γ(P.restrict U.ι, ⊤) →ₗ[Γ(U.toScheme, ⊤)] Γ(Q.restrict U.ι, ⊤) :=
    { toFun := χ₀
      map_add' := χ₀.map_add
      map_smul' := fun r b ↦ by
        change χ₀ ((U.ι.appIso ⊤).inv r • (show Γ(P, U.ι ''ᵁ ⊤) from b)) =
          (U.ι.appIso ⊤).inv r • χ₀ b
        exact χ₀.map_smul _ _ }
  have : IsAffine U.toScheme := V.2
  obtain ⟨ψ, hψ⟩ := Modules.exists_hom_app_top_eq_of_isAffine_any χ
  let E := (Modules.overEquiv U).functor
  let eP := (Modules.overFunctorEquiv U).app P
  let eQ := (Modules.overFunctorEquiv U).app Q
  let φ : P.over U ⟶ Q.over U := E.preimage (eP.hom ≫ ψ ≫ eQ.inv)
  have hm (m : Γ(P, U.ι ''ᵁ ⊤)) :
      φ.val.app (op (Over.mk (homOfLE (U.ι_image_le ⊤)))) m = χ₀ m := by
    have hφ := E.map_preimage (eP.hom ≫ ψ ≫ eQ.inv)
    have h := congr(Modules.Hom.app $hφ ⊤ m)
    change φ.val.app (op (Over.mk (homOfLE (U.ι_image_le ⊤)))) m = ψ.app ⊤ m at h
    exact h.trans (hψ m)
  refine ⟨φ, ?_⟩
  have transport (W : X.Opens) (h : W = U) (hWU : W ≤ U)
      (g : Γ(P, W) →ₗ[Γ(X, W)] Γ(Q, W))
      (hg : g = h.symm ▸ f)
      (hm : ∀ m : Γ(P, W), φ.val.app (op (Over.mk (homOfLE hWU))) m = g m) :
      ∀ b : Γ(P, U), φ.val.app (op (Over.mk (homOfLE (le_refl U)))) b = f b := by
    subst W
    subst g
    exact hm
  apply transport _ U.ι_image_top (U.ι_image_le ⊤) χ₀ _ hm
  rfl

end AlgebraicGeometry.Scheme
