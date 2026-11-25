/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.ResidueFiber
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-!
# Pullback, tensor products and fibres of invertible modules

## References

* Stacks Project, Modules, Tags 01CD, 0B8L, 01C8, 01CT, 01CA, 01CB
* Stacks Project, Sheaves, Tags 0096, 0097, 0098
* Stacks Project, Algebra, Tags 00D0, 00CY, 00D2
-/

@[expose] public section

universe v

open CategoryTheory MonoidalCategory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem stalk_generator_bijective {X : Scheme.{v}} {M : X.Modules}
    {U : X.Opens} {e : Γ(M, U)} (he : IsFreeGenerator e) (x : X) (hx : x ∈ U) :
    Function.Bijective (LinearMap.toSpanSingleton (X.presheaf.stalk x)
      (M.presheaf.stalk x) (M.presheaf.germ U x hx e)) := by
  constructor
  · intro r r' h
    obtain ⟨V, hVU, hxV, a, rfl⟩ := X.presheaf.exists_le_germ_eq r hx
    obtain ⟨W, hWU, hxW, b, rfl⟩ := X.presheaf.exists_le_germ_eq r' hx
    have hV := M.presheaf.germ_res_apply (homOfLE hVU) x hxV e
    have hW := M.presheaf.germ_res_apply (homOfLE hWU) x hxW e
    change X.presheaf.germ V x hxV a • M.presheaf.germ U x hx e =
      X.presheaf.germ W x hxW b • M.presheaf.germ U x hx e at h
    have h' : M.presheaf.germ V x hxV (a • M.presheaf.map (homOfLE hVU).op e) =
        M.presheaf.germ W x hxW (b • M.presheaf.map (homOfLE hWU).op e) := by
      rw [germ_smul, germ_smul, hV, hW]
      exact h
    obtain ⟨T, hxT, iV, iW, ht⟩ := M.presheaf.germ_eq x hxV hxW _ _ h'
    have hTU : T ≤ U := iV.le.trans hVU
    have hab : X.presheaf.map iV.op a = X.presheaf.map iW.op b := by
      apply (he T hTU).injective
      simp only [map_smul, presheaf_map_map_apply] at ht
      rwa [Subsingleton.elim (iV ≫ homOfLE hVU) (homOfLE hTU),
        Subsingleton.elim (iW ≫ homOfLE hWU) (homOfLE hTU)] at ht
    rw [← X.presheaf.germ_res_apply iV x hxT a,
      ← X.presheaf.germ_res_apply iW x hxT b, hab]
  · intro m
    obtain ⟨V, hVU, hxV, s, rfl⟩ := M.presheaf.exists_le_germ_eq m hx
    obtain ⟨a, ha⟩ := (he V hVU).surjective s
    dsimp only at ha
    refine ⟨X.presheaf.germ V x hxV a, ?_⟩
    change X.presheaf.germ V x hxV a • M.presheaf.germ U x hx e = _
    rw [← M.presheaf.germ_res_apply (homOfLE hVU) x hxV e, ← germ_smul, ha]

private theorem tensorFold_perm {X : Scheme.{v}} {l l' : List X.Modules}
    (h : l.Perm l') :
    Nonempty (l.foldr (fun A B ↦ A ⊗ B) (𝟙_ X.Modules) ≅
      l'.foldr (fun A B ↦ A ⊗ B) (𝟙_ X.Modules)) := by
  induction h with
  | nil => exact ⟨Iso.refl _⟩
  | cons A h ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Iso.refl A ⊗ᵢ e⟩
  | swap A B l =>
    exact ⟨(α_ B A _).symm ≪≫ ((β_ B A) ⊗ᵢ Iso.refl _) ≪≫ (α_ A B _)⟩
  | trans h₁ h₂ ih₁ ih₂ =>
    obtain ⟨e₁⟩ := ih₁
    obtain ⟨e₂⟩ := ih₂
    exact ⟨e₁ ≪≫ e₂⟩

-- The eight comparisons involve several concrete-category and scalar-action transports.
/-- Invertible modules have one-dimensional fibres and are stable under pullback and tensor
product. Pullback commutes naturally with tensor products and composition, compatibly with
sections; finite tensor products are invariant under permutations of the factors; and fibres
commute with pullback and tensor product, compatibly with section values. -/
theorem invertible_pullback_tensor {X Y : Scheme.{v}} (f : X ⟶ Y) :
    let pb : ∀ {A B : Scheme.{v}} (h : A ⟶ B) (N : B.Modules) (V : B.Opens),
        Γ(N, V) → Γ((tensorPullback h).obj N, h ⁻¹ᵁ V) :=
      fun {_ _} h N V s ↦
        ((Classical.choose (exists_tensorPullbackAdjunction h)).unit.app N).val.app (op V) s
    (∀ (L : Y.Modules) [L.IsInvertible],
      (∀ y : Y, Module.rank (Y.residueField y) (residueFiber L y) = 1) ∧
      ((tensorPullback f).obj L).IsInvertible) ∧
    (∀ (L M : Y.Modules) [L.IsInvertible] [M.IsInvertible], (L ⊗ M).IsInvertible) ∧
    (∃ e : ∀ (L M : Y.Modules) [L.IsInvertible] [M.IsInvertible],
        (tensorPullback f).obj (L ⊗ M) ≅
          (tensorPullback f).obj L ⊗ (tensorPullback f).obj M,
      (∀ (L M L' M' : Y.Modules)
          [L.IsInvertible] [M.IsInvertible] [L'.IsInvertible] [M'.IsInvertible]
          (a : L ⟶ L') (b : M ⟶ M'),
        (tensorPullback f).map (a ⊗ₘ b) ≫ (e L' M').hom =
          (e L M).hom ≫ ((tensorPullback f).map a ⊗ₘ (tensorPullback f).map b)) ∧
      (∀ (L M : Y.Modules) [L.IsInvertible] [M.IsInvertible]
          (V : Y.Opens) (s : Γ(L, V)) (t : Γ(M, V)),
        (e L M).hom.app (f ⁻¹ᵁ V) (pb f (L ⊗ M) V (tmulSection s t)) =
          tmulSection (pb f L V s) (pb f M V t))) ∧
    (∀ (W : Scheme.{v}) (g : W ⟶ X) (L : Y.Modules) [L.IsInvertible],
      ∃ e : (tensorPullback g).obj ((tensorPullback f).obj L) ≅
          (tensorPullback (g ≫ f)).obj L,
        ∀ (V : Y.Opens) (s : Γ(L, V)),
          e.hom.app ((g ≫ f) ⁻¹ᵁ V) (pb g ((tensorPullback f).obj L)
            (f ⁻¹ᵁ V) (pb f L V s)) = pb (g ≫ f) L V s) ∧
    (∀ (L M : Y.Modules) [L.IsInvertible] [M.IsInvertible]
        (V : Y.Opens) (s : Γ(L, V)) (t : Γ(M, V)),
      (β_ L M).hom.app V (tmulSection s t) = tmulSection t s) ∧
    (∀ (n : ℕ) (L : Fin n → Y.Modules) [∀ i, (L i).IsInvertible]
        (π : Equiv.Perm (Fin n)),
      Nonempty ((List.ofFn L).foldr (fun A B ↦ A ⊗ B) (𝟙_ Y.Modules) ≅
        (List.ofFn (fun i ↦ L (π.symm i))).foldr (fun A B ↦ A ⊗ B) (𝟙_ Y.Modules))) ∧
    (∀ (L : Y.Modules) [L.IsInvertible] (x : X),
      ∃ e : residueFiber ((tensorPullback f).obj L) x ≅
          (ModuleCat.extendScalars (f.residueFieldMap x).hom).obj (residueFiber L (f x)),
        ∀ (V : Y.Opens) (hx : f x ∈ V) (s : Γ(L, V)),
          e.hom (residueValue (pb f L V s) x hx) =
            (1 : X.residueField x) ⊗ₜ[Y.residueField (f x), (f.residueFieldMap x).hom]
              residueValue s (f x) hx) ∧
    (∀ (L M : Y.Modules) [L.IsInvertible] [M.IsInvertible] (y : Y),
      ∃ e : residueFiber (L ⊗ M) y ≅ (residueFiber L y ⊗ residueFiber M y),
        ∀ (V : Y.Opens) (hy : y ∈ V) (s : Γ(L, V)) (t : Γ(M, V)),
          e.hom (residueValue (tmulSection s t) y hy) =
            residueValue s y hy ⊗ₜ[Y.residueField y] residueValue t y hy) := by
  classical
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L _
    constructor
    · intro y
      have := IsInvertible.sheafOfModules_isInvertible L
      obtain ⟨U, hy, _, e, he⟩ := exists_isFreeGenerator L (show y ∈ (⊤ : Y.Opens) from trivial)
      let q := LinearEquiv.ofBijective
        (LinearMap.toSpanSingleton (Y.presheaf.stalk y) (L.presheaf.stalk y)
          (L.presheaf.germ U.1 y hy e)) (stalk_generator_bijective he y hy)
      let F := ModuleCat.extendScalars (Y.residue y).hom
      let i := (F.mapIso q.symm.toModuleIso) ≪≫ (Functor.Monoidal.εIso F).symm
      exact i.toLinearEquiv.rank_eq.trans (Module.rank_self _)
    · let e := (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
        (pullbackPushforwardAdjunction f)
      exact IsInvertible.of_iso (e.app L).symm
  · intro L M _ _
    infer_instance
  · obtain ⟨e, hn, hs⟩ := module_pullback_tensor f
    refine ⟨fun L M ↦ e L M, ?_, ?_⟩
    · intro L M L' M' _ _ _ _ a b
      exact hn L M L' M' a b
    · intro L M _ _ V s t
      exact hs L M V s t
  · intro W g L _
    let af := Classical.choose (exists_tensorPullbackAdjunction f)
    let ag := Classical.choose (exists_tensorPullbackAdjunction g)
    let ac := Classical.choose (exists_tensorPullbackAdjunction (g ≫ f))
    let a := (af.comp ag).ofNatIsoRight (pushforwardComp g f)
    let e := a.leftAdjointUniq ac
    refine ⟨e.app L, ?_⟩
    intro V s
    have h := a.unit_leftAdjointUniq_hom_app ac L
    have hs := congrArg (fun t ↦ t.val.app (op V) s) h
    change _ = _ at hs
    exact hs
  · intro L M _ _ V s t
    exact braiding_hom_app_tmulSection s t
  · intro n L _ π
    exact tensorFold_perm (Equiv.Perm.ofFn_comp_perm π.symm L).symm
  · intro L _ x
    obtain ⟨e, he⟩ := exists_tensorPullback_stalk_iso f x
    let N := ModuleCat.of (Y.presheaf.stalk (f x)) (L.presheaf.stalk (f x))
    let r := (ModuleCat.extendScalars (X.residue x).hom).mapIso (e.app L)
    let c₁ := (ModuleCat.extendScalarsComp (f.stalkMap x).hom
      (X.residue x).hom).app N
    let c₂ := (ModuleCat.extendScalarsComp (Y.residue (f x)).hom
      (f.residueFieldMap x).hom).app N
    have hr : (X.residue x).hom.comp (f.stalkMap x).hom =
        (f.residueFieldMap x).hom.comp (Y.residue (f x)).hom :=
      congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap f x).symm
    let d := eqToIso (congrArg (fun q ↦ (ModuleCat.extendScalars q).obj N) hr)
    let c := r ≪≫ c₁.symm ≪≫ d ≪≫ c₂
    refine ⟨c, ?_⟩
    intro V hx s
    have h := he L V hx s
    change (e.app L).hom (((tensorPullback f).obj L).presheaf.germ
      (f ⁻¹ᵁ V) x hx _) = _ at h
    have hc₁ := ModuleCat.extendScalarsComp_hom_app_one_tmul
      (f.stalkMap x).hom (X.residue x).hom N (L.presheaf.germ V (f x) hx s)
    have hc₂ := ModuleCat.extendScalarsComp_hom_app_one_tmul
      (Y.residue (f x)).hom (f.residueFieldMap x).hom N
      (L.presheaf.germ V (f x) hx s)
    dsimp only [c, Iso.trans_hom]
    simp only [ModuleCat.comp_apply]
    change (c₂.hom) (d.hom
      (c₁.inv ((ModuleCat.extendScalars (X.residue x).hom).map (e.app L).hom
        ((1 : X.residueField x) ⊗ₜ[_, (X.residue x).hom]
          (((tensorPullback f).obj L).presheaf.germ (f ⁻¹ᵁ V) x hx _))))) = _
    rw [ModuleCat.ExtendScalars.map_tmul, h]
    change c₁.hom _ = _ at hc₁
    have hi := congrArg c₁.inv hc₁
    simp only [← ModuleCat.comp_apply, c₁.hom_inv_id, ModuleCat.id_apply] at hi
    erw [← hi]
    exact hc₂
  · intro L M _ _ y
    obtain ⟨e, he, _⟩ := SheafOfModules.stalkTensorIso Y.toRingedSpace y
    let F := ModuleCat.extendScalars (Y.residue y).hom
    let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace y
    let c := F.mapIso (e L M) ≪≫ (Functor.Monoidal.μIso F (S.obj L) (S.obj M)).symm
    refine ⟨c, ?_⟩
    intro V hy s t
    change (Functor.OplaxMonoidal.δ F (S.obj L) (S.obj M))
      ((F.map (e L M).hom) ((1 : Y.residueField y) ⊗ₜ[_, (Y.residue y).hom]
        ((L ⊗ M).presheaf.germ V y hy (tmulSection s t)))) = _
    rw [ModuleCat.ExtendScalars.map_tmul]
    have h := he L M V hy s t
    change (e L M).hom ((L ⊗ M).presheaf.germ V y hy (tmulSection s t)) = _ at h
    rw [h]
    exact ModuleCat.extendScalars_δ_tmul (Y.residue y).hom (S.obj L) (S.obj M) _ _

end AlgebraicGeometry.Scheme.Modules
