/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Limits.Creates

/-!
# Limits and colimits of module objects

Let `A` be a monoid object in a monoidal category `C`, acting on `C` by the tensor product. The
forgetful functor `Mod.forget A : Mod C A ⥤ C` creates all limits: the limit of the underlying
objects carries the action `A ⊗ lim Mⱼ ⟶ lim (A ⊗ Mⱼ) ⟶ lim Mⱼ`. It creates the colimits of
the shapes whose colimits are preserved by `A ⊗ -`: the colimit then carries the action
`A ⊗ colim Mⱼ ≅ colim (A ⊗ Mⱼ) ⟶ colim Mⱼ`.

## Main results

- `CategoryTheory.Mod.createsLimit`: `Mod.forget A` creates limits.
- `CategoryTheory.Mod.createsColimit`: `Mod.forget A` creates the colimits preserved by
  `tensorLeft A`.
-/

@[expose] public section

universe w w' v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (A : C) [MonObj A]

variable {A} {J : Type*} [Category J] (K : J ⥤ Mod C A)

instance (j : J) : ModObj A ((K ⋙ forget A).obj j) :=
  inferInstanceAs (ModObj A (K.obj j).X)

instance {j j' : J} (f : j ⟶ j') : IsModHom A ((K ⋙ forget A).map f) :=
  inferInstanceAs (IsModHom A (K.map f).hom)

section Limits

variable {c : Cone (K ⋙ forget A)} (hc : IsLimit c)

/-- The action of `A` on the limit of the underlying objects of a diagram of `A`-modules. -/
noncomputable def limitSMul : A ⊗ c.pt ⟶ c.pt :=
  hc.lift
    { pt := A ⊗ c.pt
      π :=
        { app j := A ◁ c.π.app j ≫ act ((K ⋙ forget A).obj j)
          naturality j j' f := by
            have h : c.π.app j' = c.π.app j ≫ (K ⋙ forget A).map f := by
              simpa using c.π.naturality f
            change 𝟙 _ ≫ A ◁ c.π.app j' ≫ act ((K ⋙ forget A).obj j') =
              (A ◁ c.π.app j ≫ act ((K ⋙ forget A).obj j)) ≫ (K ⋙ forget A).map f
            rw [Category.id_comp, Category.assoc, act_comp, ← whiskerLeft_comp_assoc, ← h] } }

@[reassoc (attr := simp)]
lemma limitSMul_π (j : J) :
    limitSMul K hc ≫ c.π.app j = A ◁ c.π.app j ≫ act ((K ⋙ forget A).obj j) :=
  hc.fac _ j

/-- The `A`-module structure on the limit of the underlying objects. -/
@[implicit_reducible]
noncomputable def limitModObj : ModObj A c.pt :=
  .mk' A (limitSMul K hc)
    (hc.hom_ext fun j ↦ by
      simp only [Category.assoc, limitSMul_π]
      rw [← whisker_exchange_assoc, one_act, leftUnitor_naturality])
    (hc.hom_ext fun j ↦ by
      simp only [Category.assoc, limitSMul_π]
      rw [← whisker_exchange_assoc, mul_act, ← whiskerLeft_comp_assoc, limitSMul_π,
        associator_naturality_right_assoc, whiskerLeft_comp_assoc])

/-- The lift of a limit cone of the underlying objects to a cone of `A`-modules. -/
noncomputable def liftedLimitCone : Cone K :=
  letI := limitModObj K hc
  { pt := ⟨c.pt⟩
    π :=
      { app j := homMk (M := ⟨c.pt⟩) (c.π.app j) (limitSMul_π K hc j)
        naturality _ _ f := Mod.hom_ext _ _ (c.π.naturality f) } }

/-- The morphism into the lifted limit cone, on underlying objects. -/
noncomputable def limitLift (s : Cone K) : s.pt.X ⟶ c.pt :=
  hc.lift ((forget A).mapCone s)

@[reassoc (attr := simp)]
lemma limitLift_π (s : Cone K) (j : J) : limitLift K hc s ≫ c.π.app j = (s.π.app j).hom :=
  hc.fac ((forget A).mapCone s) j

/-- The lifted cone is a limit cone. -/
noncomputable def isLimitLiftedLimitCone : IsLimit (liftedLimitCone K hc) :=
  letI := limitModObj K hc
  { lift s := homMk (N := ⟨c.pt⟩) (limitLift K hc s) (hc.hom_ext fun j ↦ by
      change (act s.pt.X ≫ limitLift K hc s) ≫ c.π.app j =
        (A ◁ limitLift K hc s ≫ limitSMul K hc) ≫ c.π.app j
      rw [Category.assoc, Category.assoc, limitSMul_π, ← whiskerLeft_comp_assoc,
        limitLift_π]
      exact act_hom (s.π.app j))
    fac s j := Mod.hom_ext _ _ (limitLift_π K hc s j)
    uniq s m hm := Mod.hom_ext _ _ (hc.hom_ext fun j ↦
      (congrArg Mod.Hom.hom (hm j)).trans (limitLift_π K hc s j).symm) }

/-- The forgetful functor from `A`-modules creates limits. -/
noncomputable instance createsLimit : CreatesLimit K (forget A) :=
  createsLimitOfReflectsIso fun c hc ↦
    { liftedCone := liftedLimitCone K hc
      validLift := Cone.ext (Iso.refl _) fun _ ↦ by
        change c.π.app _ = 𝟙 _ ≫ c.π.app _
        rw [Category.id_comp]
      makesLimit := isLimitLiftedLimitCone K hc }

variable (J) in
noncomputable instance : CreatesLimitsOfShape J (forget (D := C) A) where

variable (J) in
instance [HasLimitsOfShape J C] : HasLimitsOfShape J (Mod C A) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (forget A)

variable (J) in
instance [HasLimitsOfShape J C] : PreservesLimitsOfShape J (forget (D := C) A) :=
  inferInstance

noncomputable instance : CreatesLimitsOfSize.{v, v} (forget (D := C) A) where
  CreatesLimitsOfShape := inferInstance

end Limits

section Colimits

variable [PreservesColimitsOfShape J (tensorLeft A)]
variable {c : Cocone (K ⋙ forget A)} (hc : IsColimit c)

/-- The tensor product with `A` of a colimit cocone is a colimit cocone. -/
noncomputable def isColimitTensorLeft : IsColimit ((tensorLeft A).mapCocone c) :=
  isColimitOfPreserves _ hc

/-- The tensor product with `A ⊗ A` of a colimit cocone is a colimit cocone. -/
noncomputable def isColimitTensorLeftTensorLeft :
    IsColimit ((tensorLeft A).mapCocone ((tensorLeft A).mapCocone c)) :=
  isColimitOfPreserves _ (isColimitTensorLeft K hc)

/-- The action of `A` on the colimit of the underlying objects of a diagram of `A`-modules. -/
noncomputable def colimitSMul : A ⊗ c.pt ⟶ c.pt :=
  (isColimitTensorLeft K hc).desc
    { pt := c.pt
      ι :=
        { app j := act ((K ⋙ forget A).obj j) ≫ c.ι.app j
          naturality j j' f := by
            have h : c.ι.app j = (K ⋙ forget A).map f ≫ c.ι.app j' := by
              simpa using (c.ι.naturality f).symm
            change A ◁ (K ⋙ forget A).map f ≫ act ((K ⋙ forget A).obj j') ≫ c.ι.app j' =
              (act ((K ⋙ forget A).obj j) ≫ c.ι.app j) ≫ 𝟙 _
            rw [Category.comp_id, h, act_comp_assoc] } }

@[reassoc (attr := simp)]
lemma ι_colimitSMul (j : J) :
    A ◁ c.ι.app j ≫ colimitSMul K hc = act ((K ⋙ forget A).obj j) ≫ c.ι.app j :=
  (isColimitTensorLeft K hc).fac _ j

/-- The `A`-module structure on the colimit of the underlying objects. -/
@[implicit_reducible]
noncomputable def colimitModObj : ModObj A c.pt :=
  .mk' A (colimitSMul K hc)
    (by
      rw [← cancel_epi (λ_ c.pt).inv, Iso.inv_hom_id]
      refine hc.hom_ext fun j ↦ ?_
      rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, ι_colimitSMul, one_act_assoc,
        Iso.inv_hom_id_assoc, Category.comp_id])
    (by
      rw [← cancel_epi (α_ A A c.pt).inv, Iso.inv_hom_id_assoc]
      refine (isColimitTensorLeftTensorLeft K hc).hom_ext fun j ↦ ?_
      change A ◁ A ◁ c.ι.app j ≫ (α_ A A c.pt).inv ≫ μ ▷ c.pt ≫ colimitSMul K hc =
        A ◁ A ◁ c.ι.app j ≫ A ◁ colimitSMul K hc ≫ colimitSMul K hc
      erw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ι_colimitSMul,
        mul_act_assoc, Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc, ι_colimitSMul,
        whiskerLeft_comp_assoc, ι_colimitSMul])

/-- The lift of a colimit cocone of the underlying objects to a cocone of `A`-modules. -/
noncomputable def liftedColimitCocone : Cocone K :=
  letI := colimitModObj K hc
  { pt := ⟨c.pt⟩
    ι :=
      { app j := homMk (N := ⟨c.pt⟩) (c.ι.app j) (ι_colimitSMul K hc j).symm
        naturality _ _ f := Mod.hom_ext _ _ (c.ι.naturality f) } }

omit [PreservesColimitsOfShape J (tensorLeft A)] in
/-- The morphism out of the lifted colimit cocone, on underlying objects. -/
noncomputable def colimitDesc (s : Cocone K) : c.pt ⟶ s.pt.X :=
  hc.desc ((forget A).mapCocone s)

omit [PreservesColimitsOfShape J (tensorLeft A)] in
@[reassoc (attr := simp)]
lemma ι_colimitDesc (s : Cocone K) (j : J) : c.ι.app j ≫ colimitDesc K hc s = (s.ι.app j).hom :=
  hc.fac ((forget A).mapCocone s) j

/-- The lifted cocone is a colimit cocone. -/
noncomputable def isColimitLiftedColimitCocone : IsColimit (liftedColimitCocone K hc) :=
  letI := colimitModObj K hc
  { desc s := homMk (M := ⟨c.pt⟩) (colimitDesc K hc s)
      ((isColimitTensorLeft K hc).hom_ext fun j ↦ by
        change A ◁ c.ι.app j ≫ colimitSMul K hc ≫ colimitDesc K hc s =
          A ◁ c.ι.app j ≫ A ◁ colimitDesc K hc s ≫ act s.pt.X
        rw [ι_colimitSMul_assoc, ι_colimitDesc, ← whiskerLeft_comp_assoc, ι_colimitDesc]
        exact act_hom (s.ι.app j))
    fac s j := Mod.hom_ext _ _ (ι_colimitDesc K hc s j)
    uniq s m hm := Mod.hom_ext _ _ (hc.hom_ext fun j ↦
      (congrArg Mod.Hom.hom (hm j)).trans (ι_colimitDesc K hc s j).symm) }

/-- The forgetful functor from `A`-modules creates the colimits preserved by `A ⊗ -`. -/
noncomputable instance createsColimit : CreatesColimit K (forget A) :=
  createsColimitOfReflectsIso fun c hc ↦
    { liftedCocone := liftedColimitCocone K hc
      validLift := Cocone.ext (Iso.refl _) fun _ ↦ by
        change c.ι.app _ ≫ 𝟙 _ = c.ι.app _
        rw [Category.comp_id]
      makesColimit := isColimitLiftedColimitCocone K hc }

end Colimits

variable (J) in
noncomputable instance [PreservesColimitsOfShape J (tensorLeft A)] :
    CreatesColimitsOfShape J (forget (D := C) A) where

variable (J) in
instance [HasColimitsOfShape J C] [PreservesColimitsOfShape J (tensorLeft A)] :
    HasColimitsOfShape J (Mod C A) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (forget A)

variable (J) in
instance [HasColimitsOfShape J C] [PreservesColimitsOfShape J (tensorLeft A)] :
    PreservesColimitsOfShape J (forget (D := C) A) :=
  inferInstance

noncomputable instance [PreservesColimitsOfSize.{w, w'} (tensorLeft A)] :
    CreatesColimitsOfSize.{w, w'} (forget (D := C) A) where
  CreatesColimitsOfShape := inferInstance

instance [HasColimitsOfSize.{w, w'} C] [PreservesColimitsOfSize.{w, w'} (tensorLeft A)] :
    PreservesColimitsOfSize.{w, w'} (forget (D := C) A) where
  preservesColimitsOfShape := inferInstance

end CategoryTheory.Mod
