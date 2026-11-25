/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.AffineBaseChangeChartCoordinates
import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

/-- The algebra in the affine base change calculation, including its generator formula. -/
private theorem tensor_baseChange_equiv
    (R B R' M : Type u) [CommRing R] [CommRing B] [CommRing R']
    [Algebra R B] [Algebra R R'] [AddCommGroup M] [Module R M] [Module B M]
    [IsScalarTower R B M] :
    letI : Algebra B (TensorProduct R R' B) := Algebra.TensorProduct.rightAlgebra
    ∃ e : TensorProduct R R' M ≃+ TensorProduct B (TensorProduct R R' B) M,
      ∀ (r : R') (m : M), e (TensorProduct.tmul R r m) =
        TensorProduct.tmul B (TensorProduct.tmul R r (1 : B)) m := by
  let : Algebra B (TensorProduct R R' B) := Algebra.TensorProduct.rightAlgebra
  let e := (TensorProduct.comm R R' M).toAddEquiv |>.trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R B B M R').symm.toAddEquiv |>.trans
    (TensorProduct.congr (LinearEquiv.refl B M)
      (Algebra.TensorProduct.commRight R B R').toLinearEquiv).toAddEquiv |>.trans
    (TensorProduct.comm B M (TensorProduct R R' B)).toAddEquiv
  refine ⟨e, ?_⟩
  intro r m
  simp [e]

/-- Affine-local section computation for affine pushforward base change.
The map on sections over every affine open is bijective by identifying all four schemes
with spectra of rings and computing the canonical tensor-product map.
(blueprint: lem-weil-pbc-affine-pushforward-base-change-app-bijective)
Proof: Restrict the cartesian square to an affine open, identify it with spectra of rings,
and calculate the map as the canonical tensor-product isomorphism. -/
theorem affinePushforward_baseChange_app_bijective {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∀ V : S'.Opens, IsAffineOpen V →
      Function.Bijective ((moduleBaseChangeMap f f' g g' sq.w F).app V) := by
  let beta := moduleBaseChangeMap f f' g g' sq.w F
  let C : Set S'.Opens := {W | IsAffineOpen W ∧
    ∃ U : S.Opens, IsAffineOpen U ∧ W ≤ g ⁻¹ᵁ U}
  have hC : TopologicalSpace.Opens.IsBasis C := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro O x hx
    obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := S) (x := g x) (U := ⊤) (by trivial)
    obtain ⟨W, hW, hxW, hWO⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ O ⊓ g ⁻¹ᵁ U from ⟨hx, hxU⟩)
    exact ⟨W, ⟨hW, U, hU, le_trans hWO inf_le_right⟩, hxW,
      le_trans hWO inf_le_left⟩
  have hlocal (W : S'.Opens) (hW : W ∈ C) : Function.Bijective (beta.app W) := by
    obtain ⟨hW, U, hU, hWU⟩ := hW
    let R := Γ(S, U)
    let B := Γ(X, f ⁻¹ᵁ U)
    let R' := Γ(S', W)
    let M := Γ(F, f ⁻¹ᵁ U)
    let : Algebra R B := (f.app U).hom.toAlgebra
    let : Algebra R R' := (g.appLE U W hWU).hom.toAlgebra
    let : Module R M := Module.compHom M (f.app U).hom
    have : IsScalarTower R B M := IsScalarTower.of_compHom R B M
    let : Algebra B (TensorProduct R R' B) := Algebra.TensorProduct.rightAlgebra
    obtain ⟨a, b, hab⟩ := exists_affineBaseChange_chart_coordinates f f' g g' sq F
      U hU W hW hWU
    obtain ⟨e, he⟩ := tensor_baseChange_equiv R B R' M
    have hcalc (t : TensorProduct R R' M) : b (beta.app W (a.symm t)) = e t := by
      change b ((beta.app W).hom (a.symm t)) = e t
      induction t using TensorProduct.inductionOn with
      | tmul r m => exact (hab r m).trans (he r m).symm
      | add t s ht hs =>
          rw [a.symm.map_add, map_add, b.map_add, e.map_add, ht, hs]
    have heq : (fun t ↦ b (beta.app W (a.symm t))) = e := funext hcalc
    have hb : Function.Bijective (fun t ↦ b (beta.app W (a.symm t))) := by
      rw [heq]
      exact e.bijective
    constructor
    · intro m n hmn
      apply a.injective
      apply hb.1
      simpa only [a.symm_apply_apply] using congrArg b hmn
    · intro n
      obtain ⟨t, ht⟩ := hb.2 (b n)
      exact ⟨a.symm t, b.injective ht⟩
  let A : TopCat.Sheaf AddCommGrpCat.{u} S' :=
    ⟨((tensorPullback g).obj ((pushforward f).obj F)).presheaf,
      ((tensorPullback g).obj ((pushforward f).obj F)).isSheaf⟩
  let D : TopCat.Sheaf AddCommGrpCat.{u} S' :=
    ⟨((pushforward f').obj ((tensorPullback g').obj F)).presheaf,
      ((pushforward f').obj ((tensorPullback g').obj F)).isSheaf⟩
  let psi : A ⟶ D := Sheaf.homEquiv.symm ((toPresheaf S').map beta)
  have hB : TopologicalSpace.Opens.IsBasis
      (Set.range (fun W : C ↦ (W : S'.Opens))) := by
    simpa only [Subtype.range_coe] using hC
  have : IsIso psi := TopCat.Sheaf.isIso_iff_isIso_basis hB fun W ↦
    (ConcreteCategory.isIso_iff_bijective _).2 (hlocal W W.2)
  intro V _
  exact ConcreteCategory.bijective_of_isIso (psi.hom.app (op V))

end
end AlgebraicGeometry.Scheme.Modules
