import Langlands.Geometry.FormalGroup.DeligneSheafBaseChange
import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Coherent ordinary inverse image of Deligne coefficient sheaves -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory TopologicalSpace

section Adjunctions

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

private theorem adjunction_comp_assoc
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' : C ⥤ D} {R'' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'') :
    (a.comp b).comp c = a.comp (b.comp c) := by
  apply Adjunction.ext
  ext X
  simp only [Adjunction.comp_unit_app, Functor.comp_obj, Functor.comp_map,
    Functor.map_comp, Category.assoc]

private theorem adjunction_id_comp {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R) :
    Adjunction.id.comp a = a := by
  apply Adjunction.ext
  ext X
  simp only [Adjunction.comp_unit_app, Adjunction.id_unit, NatTrans.id_app,
    Functor.id_obj, Functor.id_map, Category.id_comp]

private theorem adjunction_comp_id {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R) :
    a.comp Adjunction.id = a := by
  apply Adjunction.ext
  ext X
  simp only [Adjunction.comp_unit_app, Adjunction.id_unit, NatTrans.id_app,
    Functor.id_obj]
  change a.unit.app X ≫ R.map (𝟙 (L.obj X)) = a.unit.app X
  rw [R.map_id]
  exact Category.comp_id (a.unit.app X)

private theorem leftAdjointUniq_whiskerLeft
    {L : A ⥤ B} {R : B ⥤ A} {L₁ L₂ : B ⥤ C} {R' : C ⥤ B}
    (a : L ⊣ R) (b : L₁ ⊣ R') (c : L₂ ⊣ R') :
    Functor.isoWhiskerLeft L (b.leftAdjointUniq c) =
      (a.comp b).leftAdjointUniq (a.comp c) := by
  apply Iso.ext
  apply (conjugateEquiv (a.comp c) (a.comp b)).injective
  simp only [Functor.isoWhiskerLeft_hom, conjugateEquiv_whiskerLeft]
  simp [Adjunction.leftAdjointUniq]

private theorem leftAdjointUniq_whiskerRight
    {L₁ L₂ : A ⥤ B} {R : B ⥤ A} {L : B ⥤ C} {R' : C ⥤ B}
    (a : L₁ ⊣ R) (b : L₂ ⊣ R) (c : L ⊣ R') :
    Functor.isoWhiskerRight (a.leftAdjointUniq b) L =
      (a.comp c).leftAdjointUniq (b.comp c) := by
  apply Iso.ext
  apply (conjugateEquiv (b.comp c) (a.comp c)).injective
  simp only [Functor.isoWhiskerRight_hom, conjugateEquiv_whiskerRight]
  simp [Adjunction.leftAdjointUniq]

private theorem leftAdjointUniq_trans
    {L₁ L₂ L₃ : A ⥤ B} {R : B ⥤ A}
    (a : L₁ ⊣ R) (b : L₂ ⊣ R) (c : L₃ ⊣ R) :
    a.leftAdjointUniq b ≪≫ b.leftAdjointUniq c = a.leftAdjointUniq c :=
  Iso.ext (Adjunction.leftAdjointUniq_trans a b c)

end Adjunctions

variable {O R : Type u} [CommRing O] [CommRing R]
  {W X Y Z : TopCat.{u}}

/-- Ordinary inverse image along the identity has its canonical adjunction comparison. -/
def inverseImageIdIso (O : Type u) [CommRing O] (X : TopCat.{u}) :
    TopCat.Sheaf.pullback (ModuleCat.{u} O) (𝟙 X) ≅ 𝟭 _ :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) (𝟙 X)).leftAdjointUniq
    Adjunction.id

/-- Ordinary iterated inverse image has its canonical composite-base comparison. -/
def inverseImageCompIso (O : Type u) [CommRing O] (f : X ⟶ Y) (g : W ⟶ X) :
    TopCat.Sheaf.pullback (ModuleCat.{u} O) f ⋙
        TopCat.Sheaf.pullback (ModuleCat.{u} O) g ≅
      TopCat.Sheaf.pullback (ModuleCat.{u} O) (g ≫ f) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) g)).leftAdjointUniq
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) (g ≫ f))

/-- The ordinary inverse-image composition comparison is associative. -/
theorem inverseImage_assoc (O : Type u) [CommRing O]
    (f : Y ⟶ Z) (g : X ⟶ Y) (h : W ⟶ X) :
    Functor.isoWhiskerRight (inverseImageCompIso O f g)
        (TopCat.Sheaf.pullback (ModuleCat.{u} O) h) ≪≫
        inverseImageCompIso O (g ≫ f) h =
      Functor.isoWhiskerLeft (TopCat.Sheaf.pullback (ModuleCat.{u} O) f)
        (inverseImageCompIso O g h) ≪≫ inverseImageCompIso O f (h ≫ g) := by
  let a := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f
  let b := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) g
  let c := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) h
  let ab := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) (g ≫ f)
  let bc := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) (h ≫ g)
  let abc := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) (h ≫ g ≫ f)
  change Functor.isoWhiskerRight ((a.comp b).leftAdjointUniq ab) _ ≪≫
      (ab.comp c).leftAdjointUniq abc =
    Functor.isoWhiskerLeft _ ((b.comp c).leftAdjointUniq bc) ≪≫
      (a.comp bc).leftAdjointUniq abc
  simp only [leftAdjointUniq_whiskerRight (a.comp b) ab c,
    leftAdjointUniq_whiskerLeft a (b.comp c) bc, leftAdjointUniq_trans,
    adjunction_comp_assoc]

/-- Identity on the original base is a unit for ordinary inverse image. -/
theorem inverseImage_id_comp (O : Type u) [CommRing O] (f : X ⟶ Y) :
    inverseImageCompIso O (𝟙 Y) f =
      Functor.isoWhiskerRight (inverseImageIdIso O Y)
        (TopCat.Sheaf.pullback (ModuleCat.{u} O) f) := by
  let a := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) (𝟙 Y)
  let b := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f
  change (a.comp b).leftAdjointUniq b =
    Functor.isoWhiskerRight (a.leftAdjointUniq Adjunction.id) _
  simpa only [adjunction_id_comp] using
    (leftAdjointUniq_whiskerRight a Adjunction.id b).symm

/-- Identity on the new base is a unit for ordinary inverse image. -/
theorem inverseImage_comp_id (O : Type u) [CommRing O] (f : X ⟶ Y) :
    inverseImageCompIso O f (𝟙 X) =
      Functor.isoWhiskerLeft (TopCat.Sheaf.pullback (ModuleCat.{u} O) f)
        (inverseImageIdIso O X) := by
  let a := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f
  let b := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) (𝟙 X)
  change (a.comp b).leftAdjointUniq a =
    Functor.isoWhiskerLeft _ (b.leftAdjointUniq Adjunction.id)
  simpa only [adjunction_comp_id] using
    (leftAdjointUniq_whiskerLeft a b Adjunction.id).symm

/-- The restriction-of-scalars comparison agrees with identity inverse image. -/
theorem inverseImageRestrictionIso_id (ρ : O →+* R) (X : TopCat.{u}) :
    inverseImageRestrictionIso ρ (𝟙 X) ≪≫
        Functor.isoWhiskerRight (inverseImageIdIso R X) (coefficientRestriction ρ X) =
      Functor.isoWhiskerLeft (coefficientRestriction ρ X) (inverseImageIdIso O X) := by
  let a := coefficientRestrictionAdjunction ρ X
  let b := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) (𝟙 X)
  let c := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) (𝟙 X)
  change (a.comp b).leftAdjointUniq (c.comp a) ≪≫
      Functor.isoWhiskerRight (c.leftAdjointUniq Adjunction.id) _ =
    Functor.isoWhiskerLeft _ (b.leftAdjointUniq Adjunction.id)
  calc
    _ = (a.comp b).leftAdjointUniq (c.comp a) ≪≫
        (c.comp a).leftAdjointUniq (Adjunction.id.comp a) :=
      congrArg (fun e => (a.comp b).leftAdjointUniq (c.comp a) ≪≫ e)
        (leftAdjointUniq_whiskerRight c Adjunction.id a)
    _ = (a.comp b).leftAdjointUniq a := by
      rw [adjunction_id_comp, leftAdjointUniq_trans]
    _ = _ := by
      simpa only [adjunction_comp_id] using
        (leftAdjointUniq_whiskerLeft a b Adjunction.id).symm

/-- Restriction of coefficient scalars commutes coherently with iterated inverse image. -/
theorem inverseImageRestrictionIso_comp (ρ : O →+* R) (f : X ⟶ Y) (g : W ⟶ X) :
    Functor.isoWhiskerLeft (coefficientRestriction ρ Y) (inverseImageCompIso O f g) ≪≫
        inverseImageRestrictionIso ρ (g ≫ f) =
      Functor.isoWhiskerRight (inverseImageRestrictionIso ρ f)
          (TopCat.Sheaf.pullback (ModuleCat.{u} O) g) ≪≫
        Functor.isoWhiskerLeft (TopCat.Sheaf.pullback (ModuleCat.{u} R) f)
          (inverseImageRestrictionIso ρ g) ≪≫
        Functor.isoWhiskerRight (inverseImageCompIso R f g) (coefficientRestriction ρ W) := by
  let qY := coefficientRestrictionAdjunction ρ Y
  let qX := coefficientRestrictionAdjunction ρ X
  let qW := coefficientRestrictionAdjunction ρ W
  let a := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f
  let b := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) g
  let c := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) (g ≫ f)
  let a' := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) f
  let b' := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) g
  let c' := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) (g ≫ f)
  change Functor.isoWhiskerLeft (coefficientRestriction ρ Y) ((a.comp b).leftAdjointUniq c) ≪≫
      (qY.comp c).leftAdjointUniq (c'.comp qW) =
    Functor.isoWhiskerRight ((qY.comp a).leftAdjointUniq (a'.comp qX))
        (TopCat.Sheaf.pullback (ModuleCat.{u} O) g) ≪≫
      Functor.isoWhiskerLeft (TopCat.Sheaf.pullback (ModuleCat.{u} R) f)
        ((qX.comp b).leftAdjointUniq (b'.comp qW)) ≪≫
      Functor.isoWhiskerRight ((a'.comp b').leftAdjointUniq c') (coefficientRestriction ρ W)
  simp only [leftAdjointUniq_whiskerLeft qY (a.comp b) c,
    leftAdjointUniq_whiskerRight (qY.comp a) (a'.comp qX) b,
    leftAdjointUniq_whiskerLeft a' (qX.comp b) (b'.comp qW),
    leftAdjointUniq_whiskerRight (a'.comp b') c' qW,
    adjunction_comp_assoc, leftAdjointUniq_trans]

/-- The coefficient-extension comparison agrees with identity inverse image. -/
theorem inverseImageExtensionIso_id (ρ : O →+* R) (X : TopCat.{u}) :
    inverseImageExtensionIso ρ (𝟙 X) ≪≫
        Functor.isoWhiskerRight (inverseImageIdIso O X) (coefficientExtension ρ X) =
      Functor.isoWhiskerLeft (coefficientExtension ρ X) (inverseImageIdIso R X) := by
  let a := coefficientExtensionAdjunction ρ X
  let b := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) (𝟙 X)
  let c := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) (𝟙 X)
  change (a.comp b).leftAdjointUniq (c.comp a) ≪≫
      Functor.isoWhiskerRight (c.leftAdjointUniq Adjunction.id) _ =
    Functor.isoWhiskerLeft _ (b.leftAdjointUniq Adjunction.id)
  calc
    _ = (a.comp b).leftAdjointUniq (c.comp a) ≪≫
        (c.comp a).leftAdjointUniq (Adjunction.id.comp a) :=
      congrArg (fun e => (a.comp b).leftAdjointUniq (c.comp a) ≪≫ e)
        (leftAdjointUniq_whiskerRight c Adjunction.id a)
    _ = (a.comp b).leftAdjointUniq a := by
      rw [adjunction_id_comp, leftAdjointUniq_trans]
    _ = _ := by
      simpa only [adjunction_comp_id] using
        (leftAdjointUniq_whiskerLeft a b Adjunction.id).symm

/-- Extension of coefficient scalars commutes coherently with iterated inverse image. -/
theorem inverseImageExtensionIso_comp (ρ : O →+* R) (f : X ⟶ Y) (g : W ⟶ X) :
    Functor.isoWhiskerLeft (coefficientExtension ρ Y) (inverseImageCompIso R f g) ≪≫
        inverseImageExtensionIso ρ (g ≫ f) =
      Functor.isoWhiskerRight (inverseImageExtensionIso ρ f)
          (TopCat.Sheaf.pullback (ModuleCat.{u} R) g) ≪≫
        Functor.isoWhiskerLeft (TopCat.Sheaf.pullback (ModuleCat.{u} O) f)
          (inverseImageExtensionIso ρ g) ≪≫
        Functor.isoWhiskerRight (inverseImageCompIso O f g) (coefficientExtension ρ W) := by
  let qY := coefficientExtensionAdjunction ρ Y
  let qX := coefficientExtensionAdjunction ρ X
  let qW := coefficientExtensionAdjunction ρ W
  let a := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) f
  let b := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) g
  let c := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) (g ≫ f)
  let a' := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f
  let b' := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) g
  let c' := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) (g ≫ f)
  change Functor.isoWhiskerLeft (coefficientExtension ρ Y) ((a.comp b).leftAdjointUniq c) ≪≫
      (qY.comp c).leftAdjointUniq (c'.comp qW) =
    Functor.isoWhiskerRight ((qY.comp a).leftAdjointUniq (a'.comp qX))
        (TopCat.Sheaf.pullback (ModuleCat.{u} R) g) ≪≫
      Functor.isoWhiskerLeft (TopCat.Sheaf.pullback (ModuleCat.{u} O) f)
        ((qX.comp b).leftAdjointUniq (b'.comp qW)) ≪≫
      Functor.isoWhiskerRight ((a'.comp b').leftAdjointUniq c') (coefficientExtension ρ W)
  simp only [leftAdjointUniq_whiskerLeft qY (a.comp b) c,
    leftAdjointUniq_whiskerRight (qY.comp a) (a'.comp qX) b,
    leftAdjointUniq_whiskerLeft a' (qX.comp b) (b'.comp qW),
    leftAdjointUniq_whiskerRight (a'.comp b') c' qW,
    adjunction_comp_assoc, leftAdjointUniq_trans]

/-- The constant-sheaf comparison agrees with identity inverse image. -/
theorem inverseImageConstantIso_id (O : Type u) [CommRing O] (X : TopCat.{u}) :
    inverseImageConstantIso (O := O) (𝟙 X) =
      Functor.isoWhiskerLeft
        (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} O))
        (inverseImageIdIso O X) := by
  let a := constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{u} O) (topOpenIsTerminal X)
  let b := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) (𝟙 X)
  change (a.comp b).leftAdjointUniq a =
    Functor.isoWhiskerLeft _ (b.leftAdjointUniq Adjunction.id)
  simpa only [adjunction_comp_id] using
    (leftAdjointUniq_whiskerLeft a b Adjunction.id).symm

/-- The constant-sheaf comparison agrees with composite inverse image. -/
theorem inverseImageConstantIso_comp (O : Type u) [CommRing O]
    (f : X ⟶ Y) (g : W ⟶ X) :
    Functor.isoWhiskerLeft
        (constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{u} O))
        (inverseImageCompIso O f g) ≪≫ inverseImageConstantIso (O := O) (g ≫ f) =
      Functor.isoWhiskerRight (inverseImageConstantIso (O := O) f)
          (TopCat.Sheaf.pullback (ModuleCat.{u} O) g) ≪≫
        inverseImageConstantIso (O := O) g := by
  let qY := constantSheafAdj (Opens.grothendieckTopology Y) (ModuleCat.{u} O) (topOpenIsTerminal Y)
  let qX := constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{u} O) (topOpenIsTerminal X)
  let qW := constantSheafAdj (Opens.grothendieckTopology W) (ModuleCat.{u} O) (topOpenIsTerminal W)
  let a := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f
  let b := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) g
  let c := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) (g ≫ f)
  change Functor.isoWhiskerLeft _ ((a.comp b).leftAdjointUniq c) ≪≫
      (qY.comp c).leftAdjointUniq qW =
    Functor.isoWhiskerRight ((qY.comp a).leftAdjointUniq qX) _ ≪≫
      (qX.comp b).leftAdjointUniq qW
  simp only [leftAdjointUniq_whiskerLeft qY (a.comp b) c,
    leftAdjointUniq_whiskerRight (qY.comp a) qX b,
    adjunction_comp_assoc, leftAdjointUniq_trans]

variable {F : Type u} [Field F] [Algebra O F]

/-- Rationalization has the same identity coherence as coefficient extension. -/
theorem inverseImageRationalIso_id (X : TopCat.{u}) :
    inverseImageRationalIso (F := F) (𝟙 X) ≪≫
        Functor.isoWhiskerRight (inverseImageIdIso O X) (rationalSheafFunctor F X) =
      Functor.isoWhiskerLeft (rationalSheafFunctor F X) (inverseImageIdIso F X) :=
  inverseImageExtensionIso_id (algebraMap O F) X

/-- Rationalization has the same composition coherence as coefficient extension. -/
theorem inverseImageRationalIso_comp (f : X ⟶ Y) (g : W ⟶ X) :
    Functor.isoWhiskerLeft (rationalSheafFunctor F Y) (inverseImageCompIso F f g) ≪≫
        inverseImageRationalIso (F := F) (g ≫ f) =
      Functor.isoWhiskerRight (inverseImageRationalIso (F := F) f)
          (TopCat.Sheaf.pullback (ModuleCat.{u} F) g) ≪≫
        Functor.isoWhiskerLeft (TopCat.Sheaf.pullback (ModuleCat.{u} O) f)
          (inverseImageRationalIso (F := F) g) ≪≫
        Functor.isoWhiskerRight (inverseImageCompIso O f g) (rationalSheafFunctor F W) :=
  inverseImageExtensionIso_comp (algebraMap O F) f g

end Langlands.DeligneFormalSpace
