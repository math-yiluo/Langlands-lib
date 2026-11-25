/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.TwistedSiteSieveGeometry
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Module presheaves and sheaves on the internal action site

Source: the agent-formulated categorical foundation accompanying main-20261015,
sk-thm-sf-ctf-stability-direct-images, paragraph (3), returned steps 4--6;
Stacks Sites, Tags 00Z8, 00ZC, and Modules on Sites, Section 03CS for background
(blueprint: lem-sfb-twisted-module-presheaf-equivalence).

All categories, actions and coefficient objects are the existing constructions in
`InternalActionSitePresentation`, exposed by the sieve-geometry dependency. The theorem
characterizes both functors by equality of section modules and of their component functions.
`HEq` compares functions whose bundled source or target modules are propositionally equal
by the adjacent section equalities. It does not allow changing sections by an isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C] (K : Cᵒᵖ ⥤ GrpCat.{u})

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extend (R : Cᵒᵖ ⥤ RingCat.{u})
    (M : EquivariantPresheaf K R) : PresheafOfModules.{u} ((projection K).op ⋙ R) where
  obj X := M.val.obj (op X.unop.base)
  map {X Y} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.map f.unop.base.op).hom).obj
      (M.val.obj (op Y.unop.base)))
    { toFun := fun m ↦ M.action.act (op Y.unop.base) f.unop.label
        (M.val.map f.unop.base.op m)
      map_add' := by intros; simp
      map_smul' := by
        intro r m
        change M.action.act (op Y.unop.base) f.unop.label
          (M.val.map f.unop.base.op (r • m)) =
          R.map f.unop.base.op r • M.action.act (op Y.unop.base) f.unop.label
            (M.val.map f.unop.base.op m)
        rw [M.val.map_smul, map_smul] }
  map_id X := by
    ext m
    change M.action.act _ 1 (M.val.map (𝟙 _) m) = m
    simp
  map_comp {X Y Z} f g := by
    ext m
    change M.action.act _ (g.unop.label * K.map g.unop.base.op f.unop.label)
      (M.val.map (g.unop.base ≫ f.unop.base).op m) =
      M.action.act _ g.unop.label
        (M.val.map g.unop.base.op
          (M.action.act _ f.unop.label (M.val.map f.unop.base.op m)))
    rw [M.action.naturality, map_mul, Module.End.mul_apply]
    rw [op_comp, M.val.map_comp_apply]

private noncomputable def extendMap (R : Cᵒᵖ ⥤ RingCat.{u})
    {M N : EquivariantPresheaf K R} (f : M ⟶ N) : extend K R M ⟶ extend K R N where
  app X := f.val.app (op X.unop.base)
  naturality {X Y} g := by
    ext m
    change f.val.app (op Y.unop.base)
      (M.action.act (op Y.unop.base) g.unop.label (M.val.map g.unop.base.op m)) =
      N.action.act (op Y.unop.base) g.unop.label
        (N.val.map g.unop.base.op (f.val.app (op X.unop.base) m))
    rw [f.property, PresheafOfModules.naturality_apply]

private noncomputable def extendFunctor (R : Cᵒᵖ ⥤ RingCat.{u}) :
    EquivariantPresheaf K R ⥤ PresheafOfModules.{u} ((projection K).op ⋙ R) where
  obj := extend K R
  map := extendMap K R

private theorem opArrow_one_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    opArrow K (f ≫ g) 1 = opArrow K g 1 ≫ opArrow K f 1 := by
  apply Quiver.Hom.unop_inj
  change Arrow.mk (f ≫ g) 1 = Arrow.mk (f ≫ g) (1 * K.map f.op 1)
  simp

private noncomputable def restrict (R : Cᵒᵖ ⥤ RingCat.{u})
    (N : PresheafOfModules.{u} ((projection K).op ⋙ R)) : PresheafOfModules.{u} R where
  obj X := N.obj (op (Object.mk (K := K) X.unop))
  map f := N.map (opArrow K f.unop 1)
  map_id X := by
    ext m
    change N.map (𝟙 _) m = m
    simp
  map_comp f g := by
    ext m
    change N.map (opArrow K (f ≫ g).unop 1) m =
      N.map (opArrow K g.unop 1) (N.map (opArrow K f.unop 1) m)
    rw [unop_comp, opArrow_one_comp, N.map_comp_apply]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def recoverAction (R : Cᵒᵖ ⥤ RingCat.{u})
    (N : PresheafOfModules.{u} ((projection K).op ⋙ R)) : LinearAction K (restrict K R N) where
  act X :=
    { toFun := fun a ↦
        { toFun := fun m ↦ N.map (opArrow K (𝟙 X.unop) a) m
          map_add' := by
            intro x y
            exact (N.map _).hom.map_add x y
          map_smul' := by
            intro r m
            simp [projection, opArrow] }
      map_one' := by
        ext m
        change N.map (𝟙 _) m = m
        simp
      map_mul' := by
        intro a b
        ext m
        change N.map (opArrow K (𝟙 X.unop) (a * b)) m =
          N.map (opArrow K (𝟙 X.unop) a) (N.map (opArrow K (𝟙 X.unop) b) m)
        rw [← N.map_comp_apply]
        apply N.congr_map_apply
        apply Quiver.Hom.unop_inj
        change Arrow.mk _ _ = Arrow.mk _ _
        simp [opArrow] }
  naturality {X Y} f a m := by
    change N.map (opArrow K f.unop 1)
      (N.map (opArrow K (𝟙 X.unop) a) m) =
      N.map (opArrow K (𝟙 Y.unop) (K.map f a))
        (N.map (opArrow K f.unop 1) m)
    rw [← N.map_comp_apply, ← N.map_comp_apply]
    apply N.congr_map_apply
    apply Quiver.Hom.unop_inj
    change Arrow.mk _ _ = Arrow.mk _ _
    simp [opArrow]

private noncomputable def recover (R : Cᵒᵖ ⥤ RingCat.{u})
    (N : PresheafOfModules.{u} ((projection K).op ⋙ R)) : EquivariantPresheaf K R :=
  ⟨restrict K R N, recoverAction K R N⟩

private noncomputable def recoverMap (R : Cᵒᵖ ⥤ RingCat.{u})
    {N P : PresheafOfModules.{u} ((projection K).op ⋙ R)} (f : N ⟶ P) :
    recover K R N ⟶ recover K R P :=
  ⟨{ app := fun X ↦ f.app (op (Object.mk (K := K) X.unop))
     naturality := fun g ↦ f.naturality (opArrow K g.unop 1) },
    fun X a m ↦ PresheafOfModules.naturality_apply f (opArrow K (𝟙 X.unop) a) m⟩

private noncomputable def recoverFunctor (R : Cᵒᵖ ⥤ RingCat.{u}) :
    PresheafOfModules.{u} ((projection K).op ⋙ R) ⥤ EquivariantPresheaf K R where
  obj := recover K R
  map := recoverMap K R

private theorem recover_extend_val (R : Cᵒᵖ ⥤ RingCat.{u})
    (M : EquivariantPresheaf K R) : (recover K R (extend K R M)).val = M.val := by
  dsimp [recover, restrict, extend]
  congr 1
  funext X Y f
  ext m
  change M.action.act Y 1 (M.val.map f m) = M.val.map f m
  simp

private theorem action_hext {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{u} R} (h : M = N)
    {a : LinearAction K M} {b : LinearAction K N} (ha : HEq a.act b.act) : HEq a b := by
  cases h
  cases a
  cases b
  cases ha
  rfl

private theorem recover_extend (R : Cᵒᵖ ⥤ RingCat.{u})
    (M : EquivariantPresheaf K R) : recover K R (extend K R M) = M := by
  cases M with
  | mk val action =>
    dsimp [recover]
    congr 1
    · exact recover_extend_val K R ⟨val, action⟩
    · apply action_hext K (recover_extend_val K R ⟨val, action⟩)
      apply heq_of_eq
      funext X
      apply MonoidHom.ext
      intro a
      apply LinearMap.ext
      intro m
      change action.act X a (val.map (𝟙 X) m) = action.act X a m
      simp

private theorem extend_recover (R : Cᵒᵖ ⥤ RingCat.{u})
    (N : PresheafOfModules.{u} ((projection K).op ⋙ R)) :
    extend K R (recover K R N) = N := by
  dsimp [extend, recover, restrict, recoverAction]
  congr 1
  funext X Y f
  ext m
  change N.map (opArrow K (𝟙 Y.unop.base) f.unop.label)
    (N.map (opArrow K f.unop.base 1) m) = N.map f m
  rw [← N.map_comp_apply]
  apply N.congr_map_apply
  apply Quiver.Hom.unop_inj
  change Arrow.mk _ _ = f.unop
  change Arrow.mk (𝟙 Y.unop.base ≫ f.unop.base)
    (f.unop.label * K.map (𝟙 Y.unop.base).op 1) = f.unop
  simp
  rfl

private noncomputable def unitComponent (R : Cᵒᵖ ⥤ RingCat.{u})
    (M : EquivariantPresheaf K R) : M ≅ recover K R (extend K R M) where
  hom :=
    ⟨{ app := fun X ↦ 𝟙 (M.val.obj X)
       naturality := by
         intro X Y f
         ext m
         change M.val.map f m = M.action.act Y 1 (M.val.map f m)
         simp },
      by
        intro X a m
        change M.action.act X a m = M.action.act X a (M.val.map (𝟙 X) m)
        simp⟩
  inv :=
    ⟨{ app := fun X ↦ 𝟙 (M.val.obj X)
       naturality := by
         intro X Y f
         ext m
         change M.action.act Y 1 (M.val.map f m) = M.val.map f m
         simp },
      by
        intro X a m
        change M.action.act X a (M.val.map (𝟙 X) m) = M.action.act X a m
        simp⟩
  hom_inv_id := by apply Subtype.ext; ext X m; rfl
  inv_hom_id := by apply Subtype.ext; ext X m; rfl

private noncomputable def counitComponent (R : Cᵒᵖ ⥤ RingCat.{u})
    (N : PresheafOfModules.{u} ((projection K).op ⋙ R)) :
    extend K R (recover K R N) ≅ N := by
  refine PresheafOfModules.isoMk (fun X ↦ Iso.refl _) ?_
  intro X Y f
  ext m
  change N.map (opArrow K (𝟙 Y.unop.base) f.unop.label)
    (N.map (opArrow K f.unop.base 1) m) = N.map f m
  rw [← N.map_comp_apply]
  apply N.congr_map_apply
  apply Quiver.Hom.unop_inj
  change Arrow.mk (𝟙 Y.unop.base ≫ f.unop.base)
    (f.unop.label * K.map (𝟙 Y.unop.base).op 1) = f.unop
  simp
  rfl

private noncomputable def explicitEquivalence (R : Cᵒᵖ ⥤ RingCat.{u}) :
    EquivariantPresheaf K R ≌ PresheafOfModules.{u} ((projection K).op ⋙ R) where
  functor := extendFunctor K R
  inverse := recoverFunctor K R
  unitIso := NatIso.ofComponents (unitComponent K R) (by
    intro M N f
    apply Subtype.ext
    ext X m
    rfl)
  counitIso := NatIso.ofComponents (counitComponent K R) (by
    intro N P f
    ext X m
    rfl)
  functor_unitIso_comp M := by
    ext X m
    rfl

private instance extend_additive (R : Cᵒᵖ ⥤ RingCat.{u}) :
    (extendFunctor K R).Additive where
  map_add := by intros; ext X m; rfl

private instance recover_additive (R : Cᵒᵖ ⥤ RingCat.{u}) :
    (recoverFunctor K R).Additive where
  map_add := by intros; apply Subtype.ext; ext X m; rfl

set_option backward.isDefEq.respectTransparency false in
private theorem matching_sheaf_iff (R : Cᵒᵖ ⥤ RingCat.{u})
    (M : EquivariantPresheaf K R) (X : Object K) (S : Sieve X) (T : Sieve X.base)
    (hmem : ∀ (Y : Object K) (f : Y ⟶ X), S f ↔ T f.base) :
    Presieve.IsSheafFor ((extend K R M).presheaf ⋙ forget Ab) S.arrows ↔
      Presieve.IsSheafFor (M.val.presheaf ⋙ forget Ab) T.arrows := by
  constructor
  · intro h x hx
    let y : Presieve.FamilyOfElements ((extend K R M).presheaf ⋙ forget Ab) S.arrows :=
      fun Y f hf ↦ M.action.act (op Y.base) f.label (x f.base ((hmem Y f).1 hf))
    have hy : y.Compatible := by
      apply (Presieve.compatible_iff_sieveCompatible y).2
      intro Y Z f g hf
      change M.action.act (op Z.base) (g.label * K.map g.base.op f.label)
        (x (g.base ≫ f.base) _) =
        M.action.act (op Z.base) g.label
          (M.val.map g.base.op (M.action.act (op Y.base) f.label (x f.base _)))
      have ht := hx.to_sieveCompatible f.base g.base ((hmem Y f).1 hf)
      change x (g.base ≫ f.base) _ = M.val.map g.base.op (x f.base _) at ht
      rw [ht, M.action.naturality, map_mul, Module.End.mul_apply]
    obtain ⟨m, hm, hu⟩ := h y hy
    have hm' : x.IsAmalgamation m := by
      intro Y f hf
      have ht := hm (Arrow.mk f 1 : Object.mk (K := K) Y ⟶ X)
        ((hmem _ _).2 hf)
      change M.action.act (op Y) 1 (M.val.map f.op m) =
        M.action.act (op Y) 1 (x f hf) at ht
      change M.val.map f.op m = x f hf
      simpa using ht
    refine ⟨m, hm', ?_⟩
    intro n hn
    apply hu n
    intro Y f hf
    change M.action.act (op Y.base) f.label (M.val.map f.base.op n) =
      M.action.act (op Y.base) f.label (x f.base _)
    have ht := hn f.base ((hmem Y f).1 hf)
    change M.val.map f.base.op n = x f.base ((hmem Y f).1 hf) at ht
    rw [ht]
  · intro h y hy
    let x : Presieve.FamilyOfElements (M.val.presheaf ⋙ forget Ab) T.arrows :=
      fun Y f hf ↦ y (Arrow.mk f 1 : Object.mk (K := K) Y ⟶ X)
        ((hmem _ _).2 hf)
    have hx : x.Compatible := by
      apply (Presieve.compatible_iff_sieveCompatible x).2
      intro Y Z f g hf
      have ht := hy.to_sieveCompatible
        (Arrow.mk f 1 : Object.mk (K := K) Y ⟶ X)
        (Arrow.mk g 1 : Object.mk (K := K) Z ⟶ Object.mk (K := K) Y)
        ((hmem _ _).2 hf)
      change y (Arrow.mk (g ≫ f) (1 * K.map g.op 1)) _ =
        M.action.act (op Z) 1 (M.val.map g.op (x f hf)) at ht
      change x (g ≫ f) (T.downward_closed hf g) = M.val.map g.op (x f hf)
      have hk : K.map g.op (1 : K.obj (op Y)) = 1 := (K.map g.op).hom.map_one
      have he : (Arrow.mk (g ≫ f) (1 * K.map g.op 1) :
          Object.mk (K := K) Z ⟶ X) = Arrow.mk (g ≫ f) 1 := by
        congr 1
        exact (congrArg (fun a ↦ 1 * a) hk).trans (one_mul 1)
      have hycongr (a b : Object.mk (K := K) Z ⟶ X) (ha : S a) (hb : S b)
          (e : a = b) : y a ha = y b hb := by
        cases e
        rfl
      have ha := S.downward_closed ((hmem (Object.mk (K := K) Y) (Arrow.mk f 1)).2 hf)
        (Arrow.mk g 1)
      have hb := (hmem (Object.mk (K := K) Z) (Arrow.mk (g ≫ f) 1)).2 (T.downward_closed hf g)
      have hn := hycongr (Arrow.mk (g ≫ f) (1 * K.map g.op 1))
        (Arrow.mk (g ≫ f) 1) ha hb he
      exact hn.symm.trans (ht.trans (by simp))
    have hy_label (Y : Object K) (f : Y ⟶ X) (hf : S f) :
        y f hf = M.action.act (op Y.base) f.label (x f.base ((hmem Y f).1 hf)) := by
      have ht := hy.to_sieveCompatible
        (Arrow.mk f.base 1 : Y ⟶ X) (Arrow.mk (𝟙 Y.base) f.label : Y ⟶ Y)
        ((hmem Y (Arrow.mk f.base 1)).2 ((hmem Y f).1 hf))
      change y (Arrow.mk (𝟙 Y.base ≫ f.base)
        (f.label * K.map (𝟙 Y.base).op 1)) _ =
        M.action.act (op Y.base) f.label (M.val.map (𝟙 _) (x f.base ((hmem Y f).1 hf))) at ht
      have he : (Arrow.mk (𝟙 Y.base) f.label : Y ⟶ Y) ≫
          (Arrow.mk f.base 1 : Y ⟶ X) = f := by
        change Arrow.mk (𝟙 Y.base ≫ f.base)
          (f.label * K.map (𝟙 Y.base).op 1) = f
        simp
        rfl
      have hycongr (a b : Y ⟶ X) (ha : S a) (hb : S b)
          (e : a = b) : y a ha = y b hb := by
        cases e
        rfl
      have hn := hycongr _ f
        (S.downward_closed
          ((hmem Y (Arrow.mk f.base 1)).2 ((hmem Y f).1 hf))
          (Arrow.mk (𝟙 Y.base) f.label)) hf he
      exact hn.symm.trans (ht.trans (by simp))
    obtain ⟨m, hm, hu⟩ := h x hx
    have hm' : y.IsAmalgamation m := by
      intro Y f hf
      change M.action.act (op Y.base) f.label (M.val.map f.base.op m) = y f hf
      rw [hy_label Y f hf]
      have ht := hm f.base ((hmem Y f).1 hf)
      change M.val.map f.base.op m = x f.base ((hmem Y f).1 hf) at ht
      rw [ht]
    refine ⟨m, hm', ?_⟩
    intro n hn
    apply hu n
    intro Y f hf
    have ht := hn (Arrow.mk f 1 : Object.mk (K := K) Y ⟶ X) ((hmem _ _).2 hf)
    change M.action.act (op Y) 1 (M.val.map f.op n) = x f hf at ht
    change M.val.map f.op n = x f hf
    simpa using ht

private theorem extend_sheaf_iff [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings)
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (R : Cᵒᵖ ⥤ RingCat.{u}) (M : EquivariantPresheaf K R) :
    Presheaf.IsSheaf (topology K J) (extend K R M).presheaf ↔
      Presheaf.IsSheaf J.toGrothendieck M.val.presheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget Ab),
    Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget Ab),
    isSheaf_iff_isSheaf_of_type, isSheaf_iff_isSheaf_of_type]
  obtain ⟨e, h1, h2, htop, hpull, hgen, htrans, hback, hcov⟩ :=
    (sieve_geometry K J hJ hK).2.2.2.2.2
  have hmem (X : Object K) (S : Sieve X) (Y : Object K) (f : Y ⟶ X) :
      S f ↔ e X S f.base := by
    rw [← h2 X (e X S) Y f, OrderIso.symm_apply_apply]
  constructor
  · intro h X T hT
    let U : Object K := ⟨X⟩
    have hc : (e U).symm T ∈ topology K J U := (hcov U _).2 (by simpa using hT)
    apply (matching_sheaf_iff K R M U ((e U).symm T) T (h2 U T)).1 (h _ hc)
  · intro h X S hS
    exact (matching_sheaf_iff K R M X S (e X S) (hmem X S)).2
      (h _ ((hcov X S).1 hS))

private noncomputable def extendSheafFunctor [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings)
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) :
    EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck R) ⥤
      ringedSiteModules (twistedRing K J hJ R) where
  obj M := ⟨extend K _ M.obj, (extend_sheaf_iff K J hJ hK _ M.obj).2 M.property⟩
  map f := ⟨extendMap K _ f.hom⟩

private noncomputable def recoverSheafFunctor [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings)
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) :
    ringedSiteModules (twistedRing K J hJ R) ⥤
      EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck R) where
  obj N := ⟨recover K (baseRing J.toGrothendieck R).obj N.val,
    (extend_sheaf_iff K J hJ hK _
      (recover K (baseRing J.toGrothendieck R).obj N.val)).1
        (by simpa only [extend_recover] using N.isSheaf)⟩
  map f := ⟨recoverMap K _ f.val⟩

private noncomputable def explicitSheafEquivalence [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings)
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) :
    EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck R) ≌
      ringedSiteModules (twistedRing K J hJ R) where
  functor := extendSheafFunctor K J hJ hK R
  inverse := recoverSheafFunctor K J hJ hK R
  unitIso := NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ (unitComponent K _ M.obj)) (by
      intro M N f
      apply ObjectProperty.hom_ext
      apply Subtype.ext
      ext X m
      rfl)
  counitIso := NatIso.ofComponents
    (fun N ↦
      { hom := ⟨(counitComponent K (baseRing J.toGrothendieck R).obj N.val).hom⟩
        inv := ⟨(counitComponent K (baseRing J.toGrothendieck R).obj N.val).inv⟩
        hom_inv_id := by ext X m; rfl
        inv_hom_id := by ext X m; rfl }) (by
      intro N P f
      ext X m
      rfl)
  functor_unitIso_comp M := by ext X m; rfl

private instance extendSheaf_additive [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings)
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) :
    (extendSheafFunctor K J hJ hK R).Additive where
  map_add := by intros; ext X m; rfl

private instance recoverSheaf_additive [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings)
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) :
    (recoverSheafFunctor K J hJ hK R).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    ext X m
    rfl

private theorem module_hom_hext {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N P Q : PresheafOfModules.{u} R} (hM : M = P) (hN : N = Q)
    (f : M ⟶ N) (g : P ⟶ Q) (h : ∀ X, HEq (f.app X) (g.app X)) : HEq f g := by
  cases hM
  cases hN
  apply heq_of_eq
  apply PresheafOfModules.hom_ext
  intro X
  exact eq_of_heq (h X)

private theorem equivariant_hom_hext {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N P Q : EquivariantPresheaf K R} (hM : M = P) (hN : N = Q)
    (f : M ⟶ N) (g : P ⟶ Q) (h : ∀ X, HEq (f.val.app X) (g.val.app X)) :
    HEq f g := by
  cases hM
  cases hN
  apply heq_of_eq
  apply Subtype.ext
  apply PresheafOfModules.hom_ext
  intro X
  exact eq_of_heq (h X)

private noncomputable def trivialEquivariantUnit (R : Cᵒᵖ ⥤ RingCat.{u}) :
    EquivariantPresheaf K R where
  val := PresheafOfModules.unit R
  action :=
    { act := fun X ↦ 1
      naturality := by intros; rfl }

private theorem coefficient_sheaf [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings)
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) :
    Presheaf.IsSheaf (topology K J) (coefficientPresheaf K R.obj) := by
  have hbase : Presheaf.IsSheaf J.toGrothendieck
      (trivialEquivariantUnit K (baseRing J.toGrothendieck R).obj).val.presheaf := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget Ab)]
    exact (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommRingCat)).1 R.property
  have ht := (extend_sheaf_iff K J hJ hK _
    (trivialEquivariantUnit K (baseRing J.toGrothendieck R).obj)).2 hbase
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommRingCat)]
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget Ab)] at ht
  exact ht

/-- The explicit additive equivalence of module presheaves, preserving and reflecting sheaves.

Source: agent-formulated categorical foundation for main-20261015,
sk-thm-sf-ctf-stability-direct-images, paragraph (3), returned steps 4--6;
Stacks Sites 00Z8, 00ZC and Modules on Sites 03CS are background only
(blueprint: lem-sfb-twisted-module-presheaf-equivalence).

Proof: (1) Use `lem-sfb-twisted-site-sieve-geometry` to identify every covering sieve
with all labels over a base covering sieve, and factor (f,a) as (1,a) followed by (f,1).
(2) Extend P by E(P)(f,a)m = a.f*m. Naturality and the left action law give
b.g*(a.f*m) = (b g*a).(fg)*m, so this is contravariantly functorial.
(3) For a base sieve T, extend a matching family by y_(f,a) = a.x_f. Restricting to
label-one arrows is its inverse: compatibility along (1,a) forces this formula.
These assignments preserve precisely the same amalgamating sections, including uniqueness.
(4) The covering-sieve comparison and `def-weil-pbc-topos` therefore identify the two
sheaf conditions directly for the generated Grothendieck topologies in the statement.
No pretopology conversion is needed.
(5) Give R the trivial action. Its extended restrictions are exactly f*, so (4) makes
the existing coefficient presheaf a sheaf of commutative unital rings.
(6) Each extended restriction is semilinear: a.(f*r f*m) = f*r (a.f*m). A natural,
equivariant componentwise linear map commutes with these restrictions, defining E on maps.
(7) Recover restrictions N(f,1) and action N(1,a). The label-one composition law gives
functorial restrictions. Contravariance on vertical arrows gives a left action;
R_K(1,a) = id gives linearity. The two factorizations of (f,f*a) give action naturality.
A morphism of module presheaves is natural at both kinds of arrows, giving the recovered map.
(8) On P the recovered restrictions and action are the original ones. On N, factorization
gives N(1,a)N(f,1) = N(f,a). Both round trips keep every component map. Hence the
round trips are identities, with identity section components for the unit and counit.
Pointwise addition and zero of linear maps commute with the action, so both functors
are additive, using `def-weil-presheaf-modules-sheafification` for module presheaves.
(9) By (4), restrict these same inverse functors to the full subcategories of sheaves
of `situation-conventions`. Their underlying objects and maps are unchanged,
so the sheaf equivalence is additive and has exactly the stated restrictions and actions. -/
theorem module_presheaf_equivalence [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings)
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) :
    Presheaf.IsSheaf (topology K J) (coefficientPresheaf K R.obj) ∧
    ∃ e : EquivariantPresheaf K (baseRing J.toGrothendieck R).obj ≌
        PresheafOfModules.{u} (twistedRing K J hJ R).obj,
      e.functor.Additive ∧ e.inverse.Additive ∧
      (∀ (M : EquivariantPresheaf K (baseRing J.toGrothendieck R).obj) (X : C),
        (e.functor.obj M).obj (op (Object.mk (K := K) X)) = M.val.obj (op X)) ∧
      (∀ (M : EquivariantPresheaf K (baseRing J.toGrothendieck R).obj)
          (X Y : C) (f : X ⟶ Y) (a : K.obj (op X)),
        HEq (fun m ↦ (e.functor.obj M).map (opArrow K f a) m)
          (fun m ↦ M.action.act (op X) a (M.val.map f.op m))) ∧
      (∀ (M N : EquivariantPresheaf K (baseRing J.toGrothendieck R).obj)
          (f : M ⟶ N) (X : C),
        HEq (fun m ↦ (e.functor.map f).app (op (Object.mk (K := K) X)) m)
          (fun m ↦ f.val.app (op X) m)) ∧
      (∀ (N : PresheafOfModules.{u} (twistedRing K J hJ R).obj) (X : C),
        (e.inverse.obj N).val.obj (op X) = N.obj (op (Object.mk (K := K) X))) ∧
      (∀ (N : PresheafOfModules.{u} (twistedRing K J hJ R).obj)
          (X Y : C) (f : X ⟶ Y),
        HEq (fun m ↦ (e.inverse.obj N).val.map f.op m)
          (fun m ↦ N.map (opArrow K f 1) m)) ∧
      (∀ (N : PresheafOfModules.{u} (twistedRing K J hJ R).obj)
          (X : C) (a : K.obj (op X)),
        HEq (fun m ↦ (e.inverse.obj N).action.act (op X) a m)
          (fun m ↦ N.map (opArrow K (𝟙 X) a) m)) ∧
      (∀ (N P : PresheafOfModules.{u} (twistedRing K J hJ R).obj)
          (f : N ⟶ P) (X : C),
        HEq (fun m ↦ (e.inverse.map f).val.app (op X) m)
          (fun m ↦ f.app (op (Object.mk (K := K) X)) m)) ∧
      (∀ M : EquivariantPresheaf K (baseRing J.toGrothendieck R).obj,
        e.inverse.obj (e.functor.obj M) = M) ∧
      (∀ N : PresheafOfModules.{u} (twistedRing K J hJ R).obj,
        e.functor.obj (e.inverse.obj N) = N) ∧
      (∀ (M N : EquivariantPresheaf K (baseRing J.toGrothendieck R).obj) (f : M ⟶ N),
        HEq (e.inverse.map (e.functor.map f)) f) ∧
      (∀ (N P : PresheafOfModules.{u} (twistedRing K J hJ R).obj) (f : N ⟶ P),
        HEq (e.functor.map (e.inverse.map f)) f) ∧
      (∀ (M : EquivariantPresheaf K (baseRing J.toGrothendieck R).obj) (X : C),
        HEq (fun m ↦ (e.unitIso.hom.app M).val.app (op X) m)
          (fun m : M.val.obj (op X) ↦ m)) ∧
      (∀ (N : PresheafOfModules.{u} (twistedRing K J hJ R).obj) (X : C),
        HEq (fun m ↦ (e.counitIso.hom.app N).app (op (Object.mk (K := K) X)) m)
          (fun m : N.obj (op (Object.mk (K := K) X)) ↦ m)) ∧
      (∀ M : EquivariantPresheaf K (baseRing J.toGrothendieck R).obj,
        Presheaf.IsSheaf (topology K J) (e.functor.obj M).presheaf ↔
          Presheaf.IsSheaf J.toGrothendieck M.val.presheaf) ∧
      ∃ es : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck R) ≌
          ringedSiteModules (twistedRing K J hJ R),
        es.functor.Additive ∧ es.inverse.Additive ∧
        (∀ M : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck R),
          (es.functor.obj M).val = e.functor.obj M.obj) ∧
        (∀ (M N : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck R))
            (f : M ⟶ N),
          HEq (es.functor.map f).val (e.functor.map f.hom)) ∧
        (∀ N : ringedSiteModules (twistedRing K J hJ R),
          (es.inverse.obj N).obj = e.inverse.obj N.val) ∧
        (∀ (N P : ringedSiteModules (twistedRing K J hJ R)) (f : N ⟶ P),
          HEq (es.inverse.map f).hom (e.inverse.map f.val)) := by
  refine ⟨coefficient_sheaf K J hJ hK R, explicitEquivalence K _, ?_⟩
  refine ⟨extend_additive K _, recover_additive K _, ?_⟩
  refine ⟨(fun M X ↦ rfl), (fun M X Y f a ↦ HEq.rfl),
    (fun M N f X ↦ HEq.rfl), (fun N X ↦ rfl), (fun N X Y f ↦ HEq.rfl),
    (fun N X a ↦ HEq.rfl), (fun N P f X ↦ HEq.rfl),
    recover_extend K _, extend_recover K (baseRing J.toGrothendieck R).obj, ?_⟩
  refine ⟨?_, ?_, (fun M X ↦ HEq.rfl), (fun N X ↦ HEq.rfl),
    extend_sheaf_iff K J hJ hK _, explicitSheafEquivalence K J hJ hK R,
    extendSheaf_additive K J hJ hK R, recoverSheaf_additive K J hJ hK R,
    (fun M ↦ rfl), (fun M N f ↦ HEq.rfl),
    (fun N ↦ rfl), (fun N P f ↦ HEq.rfl)⟩
  · intro M N f
    apply equivariant_hom_hext K (recover_extend K _ M) (recover_extend K _ N)
    intro X
    rfl
  · intro N P f
    apply module_hom_hext (extend_recover K (baseRing J.toGrothendieck R).obj N)
      (extend_recover K (baseRing J.toGrothendieck R).obj P)
    intro X
    rfl

end CategoryTheory.InternalActionSite
