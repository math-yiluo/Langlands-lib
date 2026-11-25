/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms

/-!
# Algebraic transport of unit-normalized site composition and identity

Source: Stacks Project, Sites, Tags 03CB, 00VE, 00WX, 00WH and 00YV;
Modules on Sites, Tag 03D2 (auxiliary; not a blueprint node).

The composite inverse image is the specified comma-colimit/sheafification construction.
Its comparison is obtained from the specified adjunctions, without choosing another unit.
The predicates below spell out the algebraic clauses using the recorded presentations;
they do not choose new ring or module structures.
-/

@[expose] public section

universe uC vC uD vD uE vE w s

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- The ring and module clauses for a comparison of algebraic inverse-image presentations.
The ring isomorphism and additive natural isomorphism have precisely the prescribed
underlying maps; semilinearity is required on every section. Isomorphisms of ring sheaves
preserve zero, one, addition and multiplication; additive sheaf isomorphisms preserve zero
and addition. The natural-isomorphism type includes naturality on all module morphisms.
Source: Stacks Project, Sites, Tag 00YV, and Modules on Sites, Tag 03D2
(auxiliary; not a blueprint node). -/
def SiteAlgebraicComparison
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
    [K.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
    [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
    [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
    {L₀ L₁ : Sheaf J (Type s) ⥤ Sheaf K (Type s)} (γ : L₀ ⟶ L₁) : Prop :=
  ∀ (R : Sheaf J CommRingCat.{s}) (R₀ R₁ : Sheaf K CommRingCat.{s})
    (A₀ : SheafOfModules.AlgebraicInverseImageOfUniverses L₀ R R₀)
    (A₁ : SheafOfModules.AlgebraicInverseImageOfUniverses L₁ R R₁),
    ∃ eR : R₀ ≅ R₁,
      (sheafCompose K (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})).map
          eR.hom =
        A₀.ringUnderlying.inv ≫ γ.app _ ≫ A₁.ringUnderlying.hom ∧
      ∃ eM : A₀.modules ⋙ SheafOfModules.toSheaf _ ≅
          A₁.modules ⋙ SheafOfModules.toSheaf _,
        (∀ M : ringedSiteModules.{s} ((sheafCompose J
            (forget₂ CommRingCat.{s} RingCat.{s})).obj R),
          (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{s} ⋙
              uliftFunctor.{s, s})).map (eM.hom.app M) =
            A₀.moduleUnderlying.hom.app M ≫ γ.app _ ≫ A₁.moduleUnderlying.inv.app M) ∧
        (∀ (M : ringedSiteModules.{s} ((sheafCompose J
            (forget₂ CommRingCat.{s} RingCat.{s})).obj R))
          (V : Dᵒᵖ) (a : R₀.obj.obj V) (x : (A₀.modules.obj M).val.obj V),
          (eM.hom.app M).hom.app V (a • x) =
            (@id (R₁.obj.obj V) (eR.hom.hom.app V a)) •
              (@id ((A₁.modules.obj M).val.obj V) ((eM.hom.app M).hom.app V x)))

noncomputable section Transport

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

private theorem pair_sections (F : Sheaf J (Type s) ⥤ Sheaf K (Type s))
    [PreservesFiniteLimits F] (X Y : Sheaf J (Type s)) (V : Dᵒᵖ)
    (x : (F.obj X).obj.obj V) (y : (F.obj Y).obj.obj V) :
    ∃ z : (F.obj (X ⨯ Y)).obj.obj V,
      (F.map (prod.fst : X ⨯ Y ⟶ X)).hom.app V z = x ∧
        (F.map (prod.snd : X ⨯ Y ⟶ Y)).hom.app V z = y := by
  let E := F ⋙ sheafToPresheaf K (Type s) ⋙ (evaluation Dᵒᵖ (Type s)).obj V
  let h := isLimitOfHasBinaryProductOfPreservesLimit E X Y
  let c : BinaryFan (E.obj X) (E.obj Y) :=
    BinaryFan.mk (↾fun _ : PUnit.{s + 1} ↦ x) (↾fun _ : PUnit.{s + 1} ↦ y)
  let z := h.lift c
  refine ⟨z PUnit.unit, ?_, ?_⟩
  · exact congrArg (fun k : PUnit.{s + 1} ⟶ E.obj X ↦ k PUnit.unit)
      (h.fac c ⟨WalkingPair.left⟩)
  · exact congrArg (fun k : PUnit.{s + 1} ⟶ E.obj Y ↦ k PUnit.unit)
      (h.fac c ⟨WalkingPair.right⟩)

private def sectionMap {X Y : Sheaf J (Type s)}
    (f : ∀ V, X.obj.obj V → Y.obj.obj V)
    (hf : ∀ {V W} (i : V ⟶ W) (x : X.obj.obj V),
      Y.obj.map i (f V x) = f W (X.obj.map i x)) : X ⟶ Y :=
  ⟨{ app V := ↾(f V)
     naturality := by
       intro V W i
       ext x
       exact (hf i x).symm }⟩

private theorem nat_section
    {F G : Sheaf J (Type s) ⥤ Sheaf K (Type s)} (γ : F ⟶ G)
    {X Y : Sheaf J (Type s)} (f : X ⟶ Y) (V : Dᵒᵖ) (x : (F.obj X).obj.obj V) :
    (γ.app Y).hom.app V ((F.map f).hom.app V x) =
      (G.map f).hom.app V ((γ.app X).hom.app V x) :=
  congrArg (fun k ↦ k.hom.app V x) (γ.naturality f)

private def compareMap
    {F G : Sheaf J (Type s) ⥤ Sheaf K (Type s)} (γ : F ⟶ G)
    {X : Sheaf J (Type s)} {X₀ X₁ : Sheaf K (Type s)}
    (e₀ : F.obj X ≅ X₀) (e₁ : G.obj X ≅ X₁) : X₀ ⟶ X₁ :=
  e₀.inv ≫ γ.app X ≫ e₁.hom

private theorem compareMap_image
    {F G : Sheaf J (Type s) ⥤ Sheaf K (Type s)} (γ : F ⟶ G)
    {X : Sheaf J (Type s)} {X₀ X₁ : Sheaf K (Type s)}
    (e₀ : F.obj X ≅ X₀) (e₁ : G.obj X ≅ X₁)
    (V : Dᵒᵖ) (x : (F.obj X).obj.obj V) :
    (compareMap γ e₀ e₁).hom.app V (e₀.hom.hom.app V x) =
      e₁.hom.hom.app V ((γ.app X).hom.app V x) := by
  change e₁.hom.hom.app V ((γ.app X).hom.app V
    (e₀.inv.hom.app V (e₀.hom.hom.app V x))) = _
  have h := congrArg (fun k ↦ k.hom.app V x) e₀.hom_inv_id
  change e₀.inv.hom.app V (e₀.hom.hom.app V x) = x at h
  rw [h]

private theorem compare_binary
    {F G : Sheaf J (Type s) ⥤ Sheaf K (Type s)} [PreservesFiniteLimits F]
    (γ : F ⟶ G) {X Y Z : Sheaf J (Type s)}
    {X₀ Y₀ Z₀ X₁ Y₁ Z₁ : Sheaf K (Type s)}
    (ex₀ : F.obj X ≅ X₀) (ey₀ : F.obj Y ≅ Y₀) (ez₀ : F.obj Z ≅ Z₀)
    (ex₁ : G.obj X ≅ X₁) (ey₁ : G.obj Y ≅ Y₁) (ez₁ : G.obj Z ≅ Z₁)
    (t : X ⨯ Y ⟶ Z)
    (o₀ : ∀ V, X₀.obj.obj V → Y₀.obj.obj V → Z₀.obj.obj V)
    (o₁ : ∀ V, X₁.obj.obj V → Y₁.obj.obj V → Z₁.obj.obj V)
    (h₀ : ∀ V (z : (F.obj (X ⨯ Y)).obj.obj V),
      ez₀.hom.hom.app V ((F.map t).hom.app V z) =
        o₀ V (ex₀.hom.hom.app V ((F.map (prod.fst : X ⨯ Y ⟶ X)).hom.app V z))
          (ey₀.hom.hom.app V ((F.map (prod.snd : X ⨯ Y ⟶ Y)).hom.app V z)))
    (h₁ : ∀ V (z : (G.obj (X ⨯ Y)).obj.obj V),
      ez₁.hom.hom.app V ((G.map t).hom.app V z) =
        o₁ V (ex₁.hom.hom.app V ((G.map (prod.fst : X ⨯ Y ⟶ X)).hom.app V z))
          (ey₁.hom.hom.app V ((G.map (prod.snd : X ⨯ Y ⟶ Y)).hom.app V z)))
    (V : Dᵒᵖ) (x : X₀.obj.obj V) (y : Y₀.obj.obj V) :
    (compareMap γ ez₀ ez₁).hom.app V (o₀ V x y) =
      o₁ V ((compareMap γ ex₀ ex₁).hom.app V x)
        ((compareMap γ ey₀ ey₁).hom.app V y) := by
  obtain ⟨z, hx, hy⟩ := pair_sections F X Y V (ex₀.inv.hom.app V x)
    (ey₀.inv.hom.app V y)
  have hx' : ex₀.hom.hom.app V ((F.map (prod.fst : X ⨯ Y ⟶ X)).hom.app V z) = x := by
    rw [hx]
    exact congrArg (fun k ↦ k.hom.app V x) ex₀.inv_hom_id
  have hy' : ey₀.hom.hom.app V ((F.map (prod.snd : X ⨯ Y ⟶ Y)).hom.app V z) = y := by
    rw [hy]
    exact congrArg (fun k ↦ k.hom.app V y) ey₀.inv_hom_id
  rw [← hx', ← hy', ← h₀ V z, compareMap_image, nat_section, h₁]
  rw [compareMap_image, compareMap_image, nat_section, nat_section]

private theorem compare_constant
    {F G : Sheaf J (Type s) ⥤ Sheaf K (Type s)} (γ : F ⟶ G)
    {X : Sheaf J (Type s)} {X₀ X₁ : Sheaf K (Type s)}
    (e₀ : F.obj X ≅ X₀) (e₁ : G.obj X ≅ X₁) (t : X ⟶ X)
    (n₀ : ∀ V, X₀.obj.obj V) (n₁ : ∀ V, X₁.obj.obj V)
    (h₀ : ∀ V (z : (F.obj X).obj.obj V),
      e₀.hom.hom.app V ((F.map t).hom.app V z) = n₀ V)
    (h₁ : ∀ V (z : (G.obj X).obj.obj V),
      e₁.hom.hom.app V ((G.map t).hom.app V z) = n₁ V) (V : Dᵒᵖ) :
    (compareMap γ e₀ e₁).hom.app V (n₀ V) = n₁ V := by
  rw [← h₀ V (e₀.inv.hom.app V (n₀ V)), compareMap_image, nat_section, h₁]

end Transport

noncomputable section AlgebraicTransport

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]

private abbrev ringSets (R : Sheaf J CommRingCat.{s}) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})).obj R

private abbrev moduleSets {R : Sheaf J CommRingCat.{s}}
    (M : ringedSiteModules.{s} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  ((SheafOfModules.toSheaf _ ⋙ sheafCompose J
    (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})).obj M)

private def binaryMap {X Y Z : Sheaf J (Type s)}
    (o : ∀ V, X.obj.obj V → Y.obj.obj V → Z.obj.obj V)
    (ho : ∀ {V W} (i : V ⟶ W) (x : X.obj.obj V) (y : Y.obj.obj V),
      Z.obj.map i (o V x y) = o W (X.obj.map i x) (Y.obj.map i y)) : X ⨯ Y ⟶ Z :=
  sectionMap (fun V z ↦ o V ((prod.fst : X ⨯ Y ⟶ X).hom.app V z)
    ((prod.snd : X ⨯ Y ⟶ Y).hom.app V z))
    (by
      intro V W i z
      rw [ho]
      congr 1
      · exact (congrArg (fun k ↦ k z) ((prod.fst : X ⨯ Y ⟶ X).hom.naturality i)).symm
      · exact (congrArg (fun k ↦ k z) ((prod.snd : X ⨯ Y ⟶ Y).hom.naturality i)).symm)

private def ringAddMap (R : Sheaf J CommRingCat.{s}) :
    ringSets R ⨯ ringSets R ⟶ ringSets R :=
  binaryMap (fun _ a b ↦ ULift.up (a.down + b.down)) (by
    intro V W i a b
    apply ULift.ext
    exact map_add (R.obj.map i).hom a.down b.down)

private def ringMulMap (R : Sheaf J CommRingCat.{s}) :
    ringSets R ⨯ ringSets R ⟶ ringSets R :=
  binaryMap (fun _ a b ↦ ULift.up (a.down * b.down)) (by
    intro V W i a b
    apply ULift.ext
    exact map_mul (R.obj.map i).hom a.down b.down)

private def ringConstMap (R : Sheaf J CommRingCat.{s}) (n : ℕ) :
    ringSets R ⟶ ringSets R :=
  sectionMap (fun V _ ↦ ULift.up (n : R.obj.obj V)) (by
    intro V W i x
    apply ULift.ext
    exact map_natCast (R.obj.map i).hom n)

private def moduleAddMap {R : Sheaf J CommRingCat.{s}}
    (M : ringedSiteModules.{s} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    moduleSets M ⨯ moduleSets M ⟶ moduleSets M :=
  binaryMap (fun _ a b ↦ ULift.up (a.down + b.down)) (by
    intro V W i a b
    apply ULift.ext
    exact map_add (M.val.map i).hom a.down b.down)

private def moduleSMulMap {R : Sheaf J CommRingCat.{s}}
    (M : ringedSiteModules.{s} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ringSets R ⨯ moduleSets M ⟶ moduleSets M :=
  binaryMap (fun V a b ↦ ULift.up
    ((@id (R.obj.obj V) a.down) • (@id (M.val.obj V) b.down))) (by
    intro V W i a b
    apply ULift.ext
    exact M.val.map_smul i a.down b.down)

end AlgebraicTransport

noncomputable section Lift

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
  {F G : Sheaf J (Type s) ⥤ Sheaf K (Type s)} [PreservesFiniteLimits F]
  (γ : F ⟶ G) {R : Sheaf J CommRingCat.{s}} {R₀ R₁ : Sheaf K CommRingCat.{s}}
  (A₀ : SheafOfModules.AlgebraicInverseImageOfUniverses F R R₀)
  (A₁ : SheafOfModules.AlgebraicInverseImageOfUniverses G R R₁)

private theorem ring_compare_add (V : Dᵒᵖ) (a b : R₀.obj.obj V) :
    ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up (a + b))).down =
      ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up a)).down +
        ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up b)).down := by
  apply congrArg ULift.down
    (compare_binary γ A₀.ringUnderlying A₀.ringUnderlying A₀.ringUnderlying
      A₁.ringUnderlying A₁.ringUnderlying A₁.ringUnderlying (ringAddMap R)
      (fun _ a b ↦ ULift.up (a.down + b.down))
      (fun _ a b ↦ ULift.up (a.down + b.down)) ?_ ?_ V (ULift.up a) (ULift.up b))
  · intro V z
    apply ULift.ext
    exact A₀.ringAdd _ _ _ _ (fun _ _ ↦ rfl) V z
  · intro V z
    apply ULift.ext
    exact A₁.ringAdd _ _ _ _ (fun _ _ ↦ rfl) V z

private theorem ring_compare_mul (V : Dᵒᵖ) (a b : R₀.obj.obj V) :
    ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up (a * b))).down =
      ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up a)).down *
        ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up b)).down := by
  apply congrArg ULift.down
    (compare_binary γ A₀.ringUnderlying A₀.ringUnderlying A₀.ringUnderlying
      A₁.ringUnderlying A₁.ringUnderlying A₁.ringUnderlying (ringMulMap R)
      (fun _ a b ↦ ULift.up (a.down * b.down))
      (fun _ a b ↦ ULift.up (a.down * b.down)) ?_ ?_ V (ULift.up a) (ULift.up b))
  · intro V z
    apply ULift.ext
    exact A₀.ringMul _ _ _ _ (fun _ _ ↦ rfl) V z
  · intro V z
    apply ULift.ext
    exact A₁.ringMul _ _ _ _ (fun _ _ ↦ rfl) V z

omit [PreservesFiniteLimits F] in
private theorem ring_compare_zero (V : Dᵒᵖ) :
    ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up 0)).down = 0 := by
  apply congrArg ULift.down
    (compare_constant γ A₀.ringUnderlying A₁.ringUnderlying (ringConstMap R 0)
      (fun _ ↦ ULift.up 0) (fun _ ↦ ULift.up 0) ?_ ?_ V)
  · intro V z
    apply ULift.ext
    exact A₀.ringZero _ _ (fun _ _ ↦ by simp [ringConstMap, sectionMap]) V z
  · intro V z
    apply ULift.ext
    exact A₁.ringZero _ _ (fun _ _ ↦ by simp [ringConstMap, sectionMap]) V z

omit [PreservesFiniteLimits F] in
private theorem ring_compare_one (V : Dᵒᵖ) :
    ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up 1)).down = 1 := by
  apply congrArg ULift.down
    (compare_constant γ A₀.ringUnderlying A₁.ringUnderlying (ringConstMap R 1)
      (fun _ ↦ ULift.up 1) (fun _ ↦ ULift.up 1) ?_ ?_ V)
  · intro V z
    apply ULift.ext
    exact A₀.ringOne _ _ (fun _ _ ↦ by simp [ringConstMap, sectionMap]) V z
  · intro V z
    apply ULift.ext
    exact A₁.ringOne _ _ (fun _ _ ↦ by simp [ringConstMap, sectionMap]) V z

private def ringComparisonMap : R₀ ⟶ R₁ :=
  ⟨{ app V := CommRingCat.ofHom
       { toFun a := ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V
           (ULift.up a)).down
         map_one' := ring_compare_one γ A₀ A₁ V
         map_mul' := ring_compare_mul γ A₀ A₁ V
         map_zero' := ring_compare_zero γ A₀ A₁ V
         map_add' := ring_compare_add γ A₀ A₁ V }
     naturality := by
       intro V W i
       ext a
       exact congrArg ULift.down (congrArg (fun k ↦ k (ULift.up a))
         ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.naturality i)) }⟩

private theorem ringComparisonMap_underlying :
    (sheafCompose K (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})).map
      (ringComparisonMap γ A₀ A₁) = compareMap γ A₀.ringUnderlying A₁.ringUnderlying := by
  ext V a
  rfl

private theorem module_compare_add
    (M : ringedSiteModules.{s} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : Dᵒᵖ) (a b : (A₀.modules.obj M).val.obj V) :
    ((compareMap γ (A₀.moduleUnderlying.app M).symm
      (A₁.moduleUnderlying.app M).symm).hom.app V (ULift.up (a + b))).down =
    ((compareMap γ (A₀.moduleUnderlying.app M).symm
      (A₁.moduleUnderlying.app M).symm).hom.app V (ULift.up a)).down +
    ((compareMap γ (A₀.moduleUnderlying.app M).symm
      (A₁.moduleUnderlying.app M).symm).hom.app V (ULift.up b)).down := by
  apply congrArg ULift.down
    (compare_binary γ (A₀.moduleUnderlying.app M).symm (A₀.moduleUnderlying.app M).symm
      (A₀.moduleUnderlying.app M).symm (A₁.moduleUnderlying.app M).symm
      (A₁.moduleUnderlying.app M).symm (A₁.moduleUnderlying.app M).symm (moduleAddMap M)
      (fun _ a b ↦ ULift.up (a.down + b.down))
      (fun _ a b ↦ ULift.up (a.down + b.down)) ?_ ?_ V (ULift.up a) (ULift.up b))
  · intro V z
    apply ULift.ext
    exact A₀.moduleAdd M _ _ _ _ (fun _ _ ↦ rfl) V z
  · intro V z
    apply ULift.ext
    exact A₁.moduleAdd M _ _ _ _ (fun _ _ ↦ rfl) V z

private theorem module_compare_smul
    (M : ringedSiteModules.{s} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : Dᵒᵖ) (a : R₀.obj.obj V) (b : (A₀.modules.obj M).val.obj V) :
    ((compareMap γ (A₀.moduleUnderlying.app M).symm
      (A₁.moduleUnderlying.app M).symm).hom.app V (ULift.up (a • b))).down =
    (@id (R₁.obj.obj V)
      ((compareMap γ A₀.ringUnderlying A₁.ringUnderlying).hom.app V (ULift.up a)).down) •
      (@id ((A₁.modules.obj M).val.obj V)
        ((compareMap γ (A₀.moduleUnderlying.app M).symm
          (A₁.moduleUnderlying.app M).symm).hom.app V (ULift.up b)).down) := by
  apply congrArg ULift.down
    (compare_binary γ A₀.ringUnderlying (A₀.moduleUnderlying.app M).symm
      (A₀.moduleUnderlying.app M).symm A₁.ringUnderlying
      (A₁.moduleUnderlying.app M).symm (A₁.moduleUnderlying.app M).symm (moduleSMulMap M)
      (fun V a b ↦ ULift.up
        ((@id (R₀.obj.obj V) a.down) • (@id ((A₀.modules.obj M).val.obj V) b.down)))
      (fun V a b ↦ ULift.up
        ((@id (R₁.obj.obj V) a.down) • (@id ((A₁.modules.obj M).val.obj V) b.down)))
      ?_ ?_ V (ULift.up a) (ULift.up b))
  · intro V z
    apply ULift.ext
    exact A₀.moduleSMul M _ _ _ _ (fun _ _ ↦ rfl) V z
  · intro V z
    apply ULift.ext
    exact A₁.moduleSMul M _ _ _ _ (fun _ _ ↦ rfl) V z

end Lift

noncomputable section FinishTransport

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
  {F G : Sheaf J (Type s) ⥤ Sheaf K (Type s)} [PreservesFiniteLimits F]
  (γ : F ≅ G) {R : Sheaf J CommRingCat.{s}} {R₀ R₁ : Sheaf K CommRingCat.{s}}
  (A₀ : SheafOfModules.AlgebraicInverseImageOfUniverses F R R₀)
  (A₁ : SheafOfModules.AlgebraicInverseImageOfUniverses G R R₁)

private def moduleComparisonApp
    (M : ringedSiteModules.{s} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (SheafOfModules.toSheaf _).obj (A₀.modules.obj M) ⟶
      (SheafOfModules.toSheaf _).obj (A₁.modules.obj M) :=
  ⟨{ app V := AddCommGrpCat.ofHom (AddMonoidHom.mk'
       (fun a ↦ ((compareMap γ.hom (A₀.moduleUnderlying.app M).symm
         (A₁.moduleUnderlying.app M).symm).hom.app V (ULift.up a)).down)
       (module_compare_add γ.hom A₀ A₁ M V))
     naturality := by
       intro V W i
       ext a
       exact congrArg ULift.down (congrArg (fun k ↦ k (ULift.up a))
         ((compareMap γ.hom (A₀.moduleUnderlying.app M).symm
           (A₁.moduleUnderlying.app M).symm).hom.naturality i)) }⟩

private theorem moduleComparisonApp_underlying
    (M : ringedSiteModules.{s} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})).map
      (moduleComparisonApp γ A₀ A₁ M) =
    compareMap γ.hom (A₀.moduleUnderlying.app M).symm
      (A₁.moduleUnderlying.app M).symm := by
  ext V a
  rfl

private theorem algebraicComparison : SiteAlgebraicComparison γ.hom := by
  intro R R₀ R₁ A₀ A₁
  let er := A₀.ringUnderlying.symm ≪≫ γ.app _ ≪≫ A₁.ringUnderlying
  have : IsIso ((sheafCompose K
      (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})).map
        (ringComparisonMap γ.hom A₀ A₁)) := by
    rw [ringComparisonMap_underlying]
    change IsIso er.hom
    infer_instance
  have : IsIso (ringComparisonMap γ.hom A₀ A₁) :=
    isIso_of_reflects_iso _ (sheafCompose K
      (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s}))
  refine ⟨asIso (ringComparisonMap γ.hom A₀ A₁),
    ringComparisonMap_underlying γ.hom A₀ A₁, ?_⟩
  let em := A₀.moduleUnderlying ≪≫ Functor.isoWhiskerLeft
    (SheafOfModules.toSheaf _ ⋙ sheafCompose J
      (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})) γ ≪≫
        A₁.moduleUnderlying.symm
  let τ : A₀.modules ⋙ SheafOfModules.toSheaf _ ⟶
      A₁.modules ⋙ SheafOfModules.toSheaf _ :=
    { app := moduleComparisonApp γ A₀ A₁
      naturality := by
        intro M N f
        apply (sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})).map_injective
        simp only [Functor.map_comp, moduleComparisonApp_underlying]
        simpa only [em, compareMap, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
          NatTrans.comp_app,
          Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.app_hom,
          Iso.app_inv, Functor.comp_map, Category.assoc] using em.hom.naturality f }
  have (M : ringedSiteModules.{s}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) : IsIso (τ.app M) := by
    have : IsIso ((sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})).map (τ.app M)) := by
      change IsIso ((sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})).map
          (moduleComparisonApp γ A₀ A₁ M))
      rw [moduleComparisonApp_underlying]
      change IsIso (em.hom.app M)
      infer_instance
    exact isIso_of_reflects_iso _ (sheafCompose K
      (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s}))
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  refine ⟨asIso τ, ?_, ?_⟩
  · intro M
    exact moduleComparisonApp_underlying γ A₀ A₁ M
  · intro M V a x
    exact module_compare_smul γ.hom A₀ A₁ M V a x

end FinishTransport

end CategoryTheory
