/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage

/-! # Pure-tensor data for a ringed-topos tensor comparison

The structure records the normalization used by Stacks Project, Tag 03EL.
(auxiliary; not a blueprint node).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
universe uC vC uD vD

namespace SheafOfModules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ChangeOfRings

variable {E : Type uC} [Category.{vC} E] [EssentiallySmall.{u} E]
  {J : GrothendieckTopology E}

/-- The local pure tensor in the existing localization tensor, with independent site sizes.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
noncomputable def ringedComparisonPure (A : Sheaf J CommRingCat.{u})
    (M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A))
    (W : Eᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory.{vC, uC, u} A).tensorObj M N).val.obj W :=
  (tensorObjIsoSheafification.{vC, uC, u} M N).inv.val.app W
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A).obj)).unit.app
        (M.val ⊗ N.val)).app W (m ⊗ₜ[A.obj.obj W] n))

/-- A scalar-extension pure section is its presheaf tensor followed by sheafification.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
noncomputable def ringedComparisonScalarSection {A B : Sheaf J CommRingCat.{u}} (c : A ⟶ B)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A))
    (W : Eᵒᵖ) (s : B.obj.obj W) (m : M.val.obj W) :
    (changeOfRings.{vC, uC, u} c M).val.obj W :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B).obj)).unit.app
      (changeOfRingsPresheaf.{vC, uC, u} c M)).app W (s ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m))

end SheafOfModules

namespace SheafOfModules
attribute [local irreducible] monoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

open scoped ChangeOfRings

/-- The type of scalar insertions on underlying sheaves, with independent site sizes.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
def RingedComparisonInsertion :=
  ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj RI) ⋙ sheafCompose JD
    (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.modules.obj M)) ⟶
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose JD
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (L.obj M))

/-- The type of tensor comparison isomorphisms, without any normalization omitted.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
def RingedComparisonTensor :=
  ∀ M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
    L.obj ((monoidalCategory R).tensorObj M N) ≅
      (monoidalCategory S).tensorObj (L.obj M) (L.obj N)

/-- Simultaneous naturality of the tensor comparison in both modules.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
def ringedComparisonNaturality (mu : RingedComparisonTensor R S L) : Prop :=
  ∀ {M M' N N' : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)} (f : M ⟶ M') (g : N ⟶ N'),
    L.map ((monoidalCategory R).tensorHom f g) ≫ (mu M' N').hom =
      (mu M N).hom ≫ (monoidalCategory S).tensorHom (L.map f) (L.map g)

/-- The scalar insertion normalization, factored to keep generated record declarations compact.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
def ringedComparisonInsertionCondition
    (q : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj RI) ⋙ sheafCompose JD
    (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.modules.obj M)) ⟶
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose JD
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (L.obj M))) : Prop :=
  ∀ (M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      (W : Dᵒᵖ) (m : (I.modules.obj M).val.obj W),
    (q M).hom.app W m = (eqToHom (hobj M).symm).val.app W
      (ringedComparisonScalarSection c (I.modules.obj M) W 1 m)

/-- The full generalized pure-tensor normalization for a specified insertion and comparison.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
def ringedComparisonPureCondition
    (q : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj RI) ⋙ sheafCompose JD
    (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.modules.obj M)) ⟶
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose JD
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (L.obj M)))
    (mu : ∀ M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
    L.obj ((monoidalCategory R).tensorObj M N) ≅
      (monoidalCategory S).tensorObj (L.obj M) (L.obj N)) : Prop :=
  ∀ (M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) (Z : Sheaf JC (Type u))
    (x : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj M))
    (y : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj N))
    (z : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj
        ((monoidalCategory R).tensorObj M N))),
    (∀ (W : Cᵒᵖ) (t : Z.obj.obj W), z.hom.app W t =
      ringedComparisonPure R M N W (x.hom.app W t) (y.hom.app W t)) →
    ∀ (W : Dᵒᵖ) (t : (uInv.obj Z).obj.obj W),
      (uInv.map z ≫ I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M N) ≫
        q ((monoidalCategory R).tensorObj M N) ≫
          (toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose JD
            (CategoryTheory.forget AddCommGrpCat.{u})).map (mu M N).hom).hom.app W t =
      ringedComparisonPure S (L.obj M) (L.obj N) W
        ((uInv.map x ≫ I.moduleUnderlying.inv.app M ≫ q M).hom.app W t)
        ((uInv.map y ≫ I.moduleUnderlying.inv.app N ≫ q N).hom.app W t)

end SheafOfModules

namespace SheafOfModules
set_option backward.isDefEq.respectTransparency false
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

open scoped ChangeOfRings

/-- The ordinary tensor comparison with its pure-tensor characterization.
The maps q insert 1 in scalar extension; the generalized-element equation fixes
mu on the inverse images of all pure tensors, hence on their sheafification.
Source: Stacks, Modules on Sites, 03EL
(auxiliary; not a blueprint node). -/
structure CanonicalRingedTensorComparison where
  /-- Scalar-extension insertion, as a map of underlying sheaves of sets. -/
  q : RingedComparisonInsertion R S RI uInv I L
  /-- Insertion is specifically m mapped to 1 tensor m. -/
  q_one : ringedComparisonInsertionCondition R S RI uInv I c L hobj q
  /-- Tensor preservation with the orientation of 07A4. -/
  mu : RingedComparisonTensor R S L
  /-- Naturality in both variables. -/
  naturality : ringedComparisonNaturality R S L mu
  /-- Canonical generalized pure-tensor formula, rather than an arbitrary tensor iso. -/
  pure : ringedComparisonPureCondition R S RI uInv I L q mu

end SheafOfModules

namespace SheafOfModules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

open scoped ChangeOfRings

-- These auxiliary generated lemmas are unused for comparison data.
set_option genSizeOf false in
set_option genCtorIdx false in
set_option genInjectivity false in
/-- The ordinary tensor comparison with its pure-tensor characterization.
The maps q insert 1 in scalar extension; the generalized-element equation fixes
mu on the inverse images of all pure tensors, hence on their sheafification.
Source: Stacks, Modules on Sites, 03EL
(auxiliary; not a blueprint node). -/
structure CanonicalRingedTensorComparisonOnSmallSites where
  /-- Scalar-extension insertion, as a map of underlying sheaves of sets. -/
  q : RingedComparisonInsertion R S RI uInv I L
  /-- Insertion is specifically m mapped to 1 tensor m. -/
  q_one : ringedComparisonInsertionCondition R S RI uInv I c L hobj q
  /-- Tensor preservation with the orientation of 07A4. -/
  mu : RingedComparisonTensor R S L
  /-- Naturality in both variables. -/
  naturality : ringedComparisonNaturality R S L mu
  /-- Canonical generalized pure-tensor formula, rather than an arbitrary tensor iso. -/
  pure : ringedComparisonPureCondition R S RI uInv I L q mu

end SheafOfModules
