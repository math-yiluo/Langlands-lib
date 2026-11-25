/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.Construction.TwistedActionCategory
public import WeilConjectures.CategoryTheory.IntegerShiftFromOne
public import Mathlib.CategoryTheory.Shift.Opposite

/-! # Coefficients on the integer-labelled category

Source: the coefficient part of step 3 of lem-sf-twisted-action-site-core.
The given generator is extended using the source library's proved integer-shift
extension theorem. No data are selected from an unproved existence statement.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite.Construction

variable {C : Type u} [SmallCategory C] (s : C ≌ C)

/-- The identity action on the value category.
Source: the constant shift by identity functors
(blueprint: lem-sf-twisted-action-coefficient). -/
def trivialShiftCore (A : Type v) [Category.{w} A] : ShiftMkCore A ℤ where
  F _ := 𝟭 A
  zero := Iso.refl _
  add _ _ := Iso.refl _
  assoc_hom_app := by intros; simp
  zero_add_hom_app := by intros; simp
  add_zero_hom_app := by intros; simp

/-- The opposite shift retains the integer label.
Source: Mathlib's naive opposite shift
(blueprint: lem-sf-twisted-action-coefficient). -/
@[instance_reducible] noncomputable def opShift : HasShift Cᵒᵖ ℤ :=
  letI := shift s
  hasShiftMk Cᵒᵖ ℤ (HasShift.mkShiftCoreOp C ℤ)

variable (J : GrothendieckTopology C)
    [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u})
    (a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R)

/-- The comparison at positive one is forced by the given negative generator.
Source: apply the chosen cancellation comparison and the inverse of a
(blueprint: lem-sf-twisted-action-coefficient). -/
noncomputable def positiveComparison : s.functor.op ⋙ R.obj ≅ R.obj := by
  let b : s.functor ⋙ s.inverse ≅ 𝟭 C := by
    change (s ^ (1 : ℤ)).functor ⋙ (s ^ (-1 : ℤ)).functor ≅ (s ^ ((-1 : ℤ) + 1)).functor
    exact powerComp s (-1) 1
  exact isoWhiskerLeft s.functor.op ((sheafToPresheaf J CommRingCat).mapIso a.symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (NatIso.op b.symm) R.obj ≪≫ R.obj.leftUnitor

/-- A coherent comparison, chosen from a fully proved extension theorem.
Source: `Functor.exists_commShift_of_one`
(blueprint: lem-sf-twisted-action-coefficient). -/
@[instance_reducible] noncomputable def coefficientCommShift :
    letI := opShift s
    letI := hasShiftMk CommRingCat.{u} ℤ (trivialShiftCore CommRingCat.{u})
    R.obj.CommShift ℤ := by
  letI := opShift s
  letI := hasShiftMk CommRingCat.{u} ℤ (trivialShiftCore CommRingCat.{u})
  exact Classical.choose (R.obj.exists_commShift_of_one (positiveComparison s J R a))

/-- The coherent comparison between each integer translate of R and R itself.
Source: integer iteration of the positive comparison
(blueprint: lem-sf-twisted-action-coefficient). -/
noncomputable def coefficientComparison (n : ℤ) : (s ^ n).functor.op ⋙ R.obj ≅ R.obj :=
  letI := opShift s
  letI := hasShiftMk CommRingCat.{u} ℤ (trivialShiftCore CommRingCat.{u})
  letI := coefficientCommShift s J R a
  R.obj.commShiftIso n

omit [s.functor.IsContinuous J J] in
/-- Its positive generator is the comparison from a.
Source: the normalization of `exists_commShift_of_one`
(blueprint: lem-sf-twisted-action-coefficient). -/
theorem coefficientComparison_one :
    coefficientComparison s J R a 1 = positiveComparison s J R a := by
  let := opShift s
  let := hasShiftMk CommRingCat.{u} ℤ (trivialShiftCore CommRingCat.{u})
  exact Classical.choose_spec (R.obj.exists_commShift_of_one (positiveComparison s J R a))

omit [s.functor.IsContinuous J J] in
/-- Its zero generator is the identity.
Source: the zero axiom of a coherent shift comparison
(blueprint: lem-sf-twisted-action-coefficient). -/
theorem coefficientComparison_zero : coefficientComparison s J R a 0 = Iso.refl R.obj := by
  let := shift s
  let := opShift s
  let := hasShiftMk CommRingCat.{u} ℤ (trivialShiftCore CommRingCat.{u})
  let := coefficientCommShift s J R a
  change R.obj.commShiftIso 0 = _
  rw [R.obj.commShiftIso_zero]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [Functor.CommShift.isoZero, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    ShiftMkCore.shiftFunctorZero_eq, HasShift.mkShiftCoreOp, shift_zero,
    trivialShiftCore, Iso.symm_hom, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  exact R.obj.map_id X

omit [s.functor.IsContinuous J J] in
/-- The scalar transport respects concatenation of integer-labelled arrows.
Source: the addition axiom of a coherent shift comparison
(blueprint: lem-sf-twisted-action-coefficient). -/
theorem coefficientComparison_add (n m : ℤ) (Z : C) :
    (coefficientComparison s J R a (n + m)).inv.app (op Z) ≫
      R.obj.map ((powerComp s n m).hom.app Z).op =
        (coefficientComparison s J R a m).inv.app (op Z) ≫
          (coefficientComparison s J R a n).inv.app (op ((s ^ m).functor.obj Z)) := by
  let := shift s
  let := opShift s
  let := hasShiftMk CommRingCat.{u} ℤ (trivialShiftCore CommRingCat.{u})
  let := coefficientCommShift s J R a
  have h := congrArg (fun e ↦ e.inv.app (op Z))
    (R.obj.commShiftIso_add' (add_comm m n))
  simp only [Functor.CommShift.isoAdd'_inv_app] at h
  simp only [coefficientComparison]
  rw [h]
  dsimp only [powerComp, shiftFunctorAdd', ShiftMkCore.shiftFunctorAdd_eq,
    HasShift.mkShiftCoreOp, trivialShiftCore, Iso.trans_hom, Iso.trans_inv,
    NatTrans.comp_app, Iso.symm_hom, Iso.symm_inv]
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_refl,
    Iso.refl_hom, NatTrans.id_app, NatIso.op_hom, NatTrans.op_app, Category.assoc,
    ← R.obj.map_comp]
  simp only [op_comp, eqToHom_op, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp only [← op_comp, Iso.inv_hom_id_app, op_id]
  change 𝟙 _ ≫ 𝟙 _ ≫ (R.obj.commShiftIso m).inv.app (op Z) ≫
    (R.obj.commShiftIso n).inv.app (op ((s ^ m).functor.obj Z)) ≫ R.obj.map (𝟙 _) = _
  rw [R.obj.map_id]
  simp only [Category.id_comp]
  change (R.obj.commShiftIso m).inv.app (op Z) ≫
    (R.obj.commShiftIso n).inv.app (op ((s ^ m).functor.obj Z)) ≫ 𝟙 _ = _
  rw [← Category.assoc]
  exact Category.comp_id _

omit [s.functor.IsContinuous J J] in
/-- The originally prescribed minus-one ring map is recovered exactly.
Source: the addition law at -1 and 1, followed by cancellation of a
(blueprint: lem-sf-twisted-action-coefficient). -/
theorem coefficientComparison_neg_one_inv :
    (coefficientComparison s J R a (-1)).inv = a.inv.hom := by
  apply ((whiskeringLeft Cᵒᵖ Cᵒᵖ CommRingCat).obj s.functor.op).map_injective
  apply NatTrans.ext
  funext X
  change (coefficientComparison s J R a (-1)).inv.app (s.functor.op.obj X) =
    a.inv.hom.app (s.functor.op.obj X)
  rw [← cancel_epi ((coefficientComparison s J R a 1).inv.app X)]
  have h := coefficientComparison_add s J R a (-1) 1 X.unop
  change (coefficientComparison s J R a 0).inv.app X ≫
    R.obj.map ((powerComp s (-1) 1).hom.app X.unop).op =
      (coefficientComparison s J R a 1).inv.app X ≫
        (coefficientComparison s J R a (-1)).inv.app (s.functor.op.obj X) at h
  rw [coefficientComparison_zero] at h
  simp only [Iso.refl_inv, NatTrans.id_app, Category.id_comp] at h
  rw [← h, coefficientComparison_one]
  simp only [positiveComparison, Iso.trans_inv, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, NatIso.op_inv, NatTrans.op_app, Iso.symm_inv,
    Functor.mapIso_inv, Category.id_comp, Category.assoc]
  have ha := NatTrans.congr_app ((sheafToPresheaf J CommRingCat).congr_map a.hom_inv_id)
    (s.functor.op.obj X)
  change a.hom.hom.app (s.functor.op.obj X) ≫ a.inv.hom.app (s.functor.op.obj X) = 𝟙 _ at ha
  change R.obj.map ((powerComp s (-1) 1).hom.app X.unop).op =
    R.obj.map ((powerComp s (-1) 1).hom.app X.unop).op ≫
      a.hom.hom.app (s.functor.op.obj X) ≫ a.inv.hom.app (s.functor.op.obj X)
  rw [ha]
  exact (Category.comp_id _).symm

/-- The coefficient arrow map is an actual composite of ring homomorphisms.
Source: semilinear extension of R to labelled arrows
(blueprint: lem-sf-twisted-action-coefficient). -/
noncomputable def coefficientMap {X Y : Object C}
    (f : Σ n : ℤ, X.base ⟶ (s ^ n).functor.obj Y.base) :
    R.obj.obj (op Y.base) ⟶ R.obj.obj (op X.base) :=
  (coefficientComparison s J R a f.1).inv.app (op Y.base) ≫ R.obj.map f.2.op

omit [s.functor.IsContinuous J J] in
/-- Ring transport reverses the explicitly specified arrow composition.
Source: naturality and the addition identity for the coefficient comparisons
(blueprint: lem-sf-twisted-action-coefficient). -/
theorem coefficientMap_comp {X Y Z : Object C}
    (f : Σ n : ℤ, X.base ⟶ (s ^ n).functor.obj Y.base)
    (g : Σ m : ℤ, Y.base ⟶ (s ^ m).functor.obj Z.base) :
    coefficientMap s J R a (X := X) (Y := Z)
      ⟨f.1 + g.1, f.2 ≫ (s ^ f.1).functor.map g.2 ≫
        (powerComp s f.1 g.1).hom.app Z.base⟩ =
      coefficientMap s J R a (X := Y) (Y := Z) g ≫
        coefficientMap s J R a (X := X) (Y := Y) f := by
  obtain ⟨n, f⟩ := f
  obtain ⟨m, g⟩ := g
  simp only [coefficientMap, op_comp, R.obj.map_comp, Category.assoc]
  rw [← Category.assoc, coefficientComparison_add]
  simp only [Category.assoc]
  have hn := (coefficientComparison s J R a n).inv.naturality g.op
  change R.obj.map g.op ≫ (coefficientComparison s J R a n).inv.app (op Y.base) =
    (coefficientComparison s J R a n).inv.app (op ((s ^ m).functor.obj Z.base)) ≫
      R.obj.map ((s ^ n).functor.map g).op at hn
  rw [← Category.assoc _ _ (R.obj.map f.op), ← hn, Category.assoc]

/-- The presheaf of commutative rings on the labelled category.
Source: the coherent comparisons and contravariant functoriality of R
(blueprint: lem-sf-twisted-action-coefficient). -/
noncomputable def coefficientPresheaf :
    letI := category s
    (Object C)ᵒᵖ ⥤ CommRingCat.{u} := by
  letI := shift s
  letI := category s
  refine {
    obj X := R.obj.obj (op X.unop.base)
    map {X Y} f := coefficientMap s J R a (X := Y.unop) (Y := X.unop) f.unop.hom
    map_id := ?_
    map_comp := ?_ }
  · intro X
    change coefficientMap s J R a ((arrows s X.unop.base X.unop.base) (𝟙 _)) = _
    rw [arrows_id]
    simp only [coefficientMap, coefficientComparison_zero, Iso.refl_inv,
      NatTrans.id_app, Category.id_comp, op_id]
    exact R.obj.map_id _
  · intro X Y Z f g
    exact coefficientMap_comp s J R a g.unop.hom f.unop.hom

omit [s.functor.IsContinuous J J] in
/-- The coefficient map on a degree-zero arrow is the original restriction map.
Source: the zero comparison
(blueprint: lem-sf-twisted-action-coefficient). -/
theorem coefficientPresheaf_map_zero {X Y : C} (f : X ⟶ Y) :
    letI := category s
    (coefficientPresheaf s J R a).map ((inclusion s).map f).op = R.obj.map f.op := by
  let := category s
  change coefficientMap s J R a (arrows s X Y ((inclusion s).map f)) = _
  rw [arrows_inclusion]
  simp [coefficientMap, coefficientComparison_zero]

/-- Restriction of the constructed presheaf is naturally the original presheaf R.
Source: the degree-zero normalization
(blueprint: lem-sf-twisted-action-coefficient). -/
noncomputable def coefficientPresheafRestriction :
    letI := category s
    (inclusion s).op ⋙ coefficientPresheaf s J R a ≅ R.obj := by
  letI := category s
  refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
  intro X Y f
  change (coefficientPresheaf s J R a).map ((inclusion s).map f.unop).op ≫ 𝟙 _ =
    𝟙 _ ≫ R.obj.map f
  simp only [Category.comp_id, Category.id_comp]
  exact coefficientPresheaf_map_zero s J R a f.unop

omit [s.functor.IsContinuous J J] in
/-- The coefficient restriction at minus one is exactly the supplied generator.
Source: the minus-one comparison and functoriality of the original ring presheaf
(blueprint: lem-sf-twisted-action-coefficient). -/
theorem coefficientPresheaf_generator (X : C) :
    letI := category s
    (coefficientPresheaf s J R a).map
      (((arrows s (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩).op) = a.inv.hom.app (op X) := by
  let := category s
  change (coefficientComparison s J R a (-1)).inv.app (op X) ≫ R.obj.map (𝟙 _).op = _
  rw [coefficientComparison_neg_one_inv]
  simp

end CategoryTheory.TwistedActionRingedSite.Construction
