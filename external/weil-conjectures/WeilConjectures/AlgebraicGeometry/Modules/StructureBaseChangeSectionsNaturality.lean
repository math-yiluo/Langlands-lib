/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackSectionFactorization

/-! # Naturality on sections of the canonical structure-sheaf comparison

## References

* Stacks Project, Tag 02KG, the canonical tensor comparison
* Stacks Project, Tag 02KG, canonical tensor comparison, and Tag 01CA
-/

@[expose] public section

noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

private theorem comp_adjunction_homEquiv
    {X Y Z : Scheme.{u}} (g : Y ⟶ X) (v : Z ⟶ Y)
    (M : X.Modules) (N : Z.Modules)
    (b : (pullback (v ≫ g)).obj M ⟶ N) :
    (((pullbackPushforwardAdjunction g).comp
      (pullbackPushforwardAdjunction v)).homEquiv M N)
      ((pullbackComp v g).hom.app M ≫ b) ≫ (pushforwardComp v g).hom.app N =
    (pullbackPushforwardAdjunction (v ≫ g)).homEquiv M N b := by
  have hu := unit_conjugateEquiv ((pullbackPushforwardAdjunction g).comp
    (pullbackPushforwardAdjunction v)) (pullbackPushforwardAdjunction (v ≫ g))
    (pullbackComp v g).inv M
  rw [conjugateEquiv_pullbackComp_inv] at hu
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  rw [(pushforwardComp v g).hom.naturality b,
    (pushforwardComp v g).hom.naturality_assoc]
  rw [← Category.assoc, hu]
  simp [← Functor.map_comp]


/-- The canonical structure-sheaf comparisons commute with a map of base-change squares. -/
theorem structure_baseChange_sections_naturality
    {X Y A B C D : Scheme.{u}}
    (p : X ⟶ Y) (q : A ⟶ B) (t : C ⟶ D)
    (g : B ⟶ Y) (h : D ⟶ Y) (k : A ⟶ X) (l : C ⟶ X)
    (sq : k ≫ p = q ≫ g) (sq' : l ≫ p = t ≫ h)
    (v : D ⟶ B) (w : C ⟶ A)
    (vg : v ≫ g = h) (wk : w ≫ k = l) (wq : w ≫ q = t ≫ v)
    (b : (pullback g).obj ((pushforward p).obj (unit X)) ⟶
      (pushforward q).obj (unit A))
    (b' : (pullback h).obj ((pushforward p).obj (unit X)) ⟶
      (pushforward t).obj (unit C))
    (hb : b = ((pullbackPushforwardAdjunction g).homEquiv _ _).symm
      ((pushforward p).map (unitToPushforwardObjUnit k.toRingCatSheafHom) ≫
        (pushforwardComp k p).hom.app (unit A) ≫
        (pushforwardCongr sq).hom.app (unit A) ≫
        (pushforwardComp q g).inv.app (unit A)))
    (hb' : b' = ((pullbackPushforwardAdjunction h).homEquiv _ _).symm
      ((pushforward p).map (unitToPushforwardObjUnit l.toRingCatSheafHom) ≫
        (pushforwardComp l p).hom.app (unit C) ≫
        (pushforwardCongr sq').hom.app (unit C) ≫
        (pushforwardComp t h).inv.app (unit C)))
    (x : Γ((pullback g).obj ((pushforward p).obj (unit X)), ⊤))
    (a : Γ(A, ⊤)) (hx : Hom.app b ⊤ x = a) :
    Hom.app b' ⊤ (pullbackSectionFactorization g h v vg ((pushforward p).obj (unit X)) x) =
      w.appTop a := by
  subst h
  subst l
  unfold pullbackSectionFactorization
  let M := (pushforward p).obj (unit X)
  let r := ((pushforward p).map (unitToPushforwardObjUnit k.toRingCatSheafHom) ≫
    (pushforwardComp k p).hom.app (unit A) ≫
    (pushforwardCongr sq).hom.app (unit A) ≫
    (pushforwardComp q g).inv.app (unit A))
  let r' := ((pushforward p).map (unitToPushforwardObjUnit (w ≫ k).toRingCatSheafHom) ≫
    (pushforwardComp (w ≫ k) p).hom.app (unit C) ≫
    (pushforwardCongr sq').hom.app (unit C) ≫
    (pushforwardComp t (v ≫ g)).inv.app (unit C))
  let s := ((pushforward q).map (unitToPushforwardObjUnit w.toRingCatSheafHom) ≫
    (pushforwardComp w q).hom.app (unit C) ≫
    (pushforwardCongr wq).hom.app (unit C) ≫
    (pushforwardComp t v).inv.app (unit C))
  -- Compare the two restrictions before taking their adjoints.
  have coherence : r' ≫ (pushforwardComp v g).inv.app ((pushforward t).obj (unit C)) =
      r ≫ (pushforward g).map s := by
    dsimp only [r, r', s]
    ext U z
    simp only [Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
      pushforwardComp_inv_app_app, ConcreteCategory.comp_apply]
    simp only [pushforwardCongr_hom_app_app]
    have e : q ⁻¹ᵁ g ⁻¹ᵁ U = k ⁻¹ᵁ p ⁻¹ᵁ U :=
      congrArg (fun f : A ⟶ Y ↦ f ⁻¹ᵁ U) sq.symm
    have e' : t ⁻¹ᵁ v ⁻¹ᵁ g ⁻¹ᵁ U = (w ≫ k) ⁻¹ᵁ p ⁻¹ᵁ U :=
      congrArg (fun f : C ⟶ Y ↦ f ⁻¹ᵁ U) sq'.symm
    have ew : t ⁻¹ᵁ v ⁻¹ᵁ g ⁻¹ᵁ U = w ⁻¹ᵁ q ⁻¹ᵁ g ⁻¹ᵁ U :=
      congrArg (fun f : C ⟶ B ↦ f ⁻¹ᵁ (g ⁻¹ᵁ U)) wq.symm
    with_unfolding_all
      change C.presheaf.map (eqToHom e').op ((w ≫ k).app (p ⁻¹ᵁ U) z) =
        C.presheaf.map (eqToHom ew).op
          (w.app (q ⁻¹ᵁ g ⁻¹ᵁ U)
            (A.presheaf.map (eqToHom e).op (k.app (p ⁻¹ᵁ U) z)))
    have hr : (w ≫ k).app (p ⁻¹ᵁ U) ≫ C.presheaf.map (eqToHom e').op =
        k.app (p ⁻¹ᵁ U) ≫ A.presheaf.map (eqToHom e).op ≫
          w.app (q ⁻¹ᵁ g ⁻¹ᵁ U) ≫ C.presheaf.map (eqToHom ew).op := by
      rw [Scheme.Hom.comp_app, Category.assoc, w.naturality_assoc]
      rw [← Functor.map_comp]
      congr 2
    exact congrArg (fun f ↦ f z) hr
  -- The composition comparison is the mate of the pushforward comparison.
  have hc := comp_adjunction_homEquiv g v M ((pushforward t).obj (unit C)) b'
  rw [Adjunction.comp_homEquiv] at hc
  change (pullbackPushforwardAdjunction g).homEquiv _ _
    ((pullbackPushforwardAdjunction v).homEquiv _ _
      ((pullbackComp v g).hom.app M ≫ b')) ≫ _ = _ at hc
  have he : (pullbackPushforwardAdjunction g).homEquiv _ _
      ((pullbackPushforwardAdjunction v).homEquiv _ _
        ((pullbackComp v g).hom.app M ≫ b')) = r ≫ (pushforward g).map s := by
    rw [← coherence]
    apply (cancel_mono ((pushforwardComp v g).hom.app ((pushforward t).obj (unit C)))).1
    have hr' : (pullbackPushforwardAdjunction (v ≫ g)).homEquiv M _ b' = r' := by
      rw [hb']
      exact Equiv.apply_symm_apply _ _
    rw [Category.assoc, Iso.inv_hom_id_app]
    change _ = r'
    rw [hr'] at hc
    exact hc
  have hv : (pullbackPushforwardAdjunction v).homEquiv _ _
      ((pullbackComp v g).hom.app M ≫ b') = b ≫ s := by
    apply ((pullbackPushforwardAdjunction g).homEquiv _ _).injective
    rw [(pullbackPushforwardAdjunction g).homEquiv_naturality_right]
    have hr : (pullbackPushforwardAdjunction g).homEquiv M _ b = r := by
      rw [hb]
      exact Equiv.apply_symm_apply _ _
    rw [hr]
    exact he
  -- Evaluate the resulting sheaf identity on the prescribed global section.
  have heval := congrArg (fun f ↦ Hom.app f ⊤ x) hv
  rw [Adjunction.homEquiv_unit] at heval
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply] at heval
  rw [pullbackΓ_apply]
  change Hom.app b' ⊤ (Hom.app ((pullbackComp v g).hom.app M) ⊤
    (pullbackUnitApp v ((pullback g).obj M) ⊤ x)) = w.appTop a
  rw [← hx]
  refine heval.trans ?_
  dsimp only [s]
  simp only [Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    pushforwardComp_inv_app_app, ConcreteCategory.comp_apply]
  simp only [pushforwardCongr_hom_app_app]
  simp
  rfl


end AlgebraicGeometry.Scheme.Modules
