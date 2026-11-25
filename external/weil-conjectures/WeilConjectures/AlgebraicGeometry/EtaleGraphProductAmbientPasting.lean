/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphProductAmbientGeometry
import WeilConjectures.AlgebraicGeometry.EtaleGraphAmbientSourcePasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphAmbientSquarePasting

/-! # Proper ambient projection pasting

Source: Stacks Tag 0F7J, the final comparison of diagrams A--F.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

private theorem paste_source_and_square
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    {Fs Ft : C ⥤ D} {L : C ⥤ E} {I : D ⥤ D} {Z : D ⥤ E}
    {Q : E ⥤ D} {G₀ : D ⥤ H} {G : E ⥤ H} {Hs Ht : C ⥤ H}
    (n : I ≅ 𝟭 D) (af : Fs ≅ Ft) (c : I ≅ Z ⋙ Q)
    (a : Fs ≅ L ⋙ Q) (b : Ft ⋙ Z ≅ L)
    (t : Q ⋙ G₀ ≅ G) (r : Fs ⋙ G₀ ≅ Hs) (h : Hs ≅ Ht)
    (s : L ⋙ G ≅ Ht)
    (hl : Functor.isoWhiskerLeft Fs n ≪≫ Functor.rightUnitor Fs ≪≫ a =
      Functor.isoWhiskerRight af I ≪≫ Functor.isoWhiskerLeft Ft c ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight b Q)
    (hs : r ≪≫ h = Functor.isoWhiskerRight a G₀ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L t ≪≫ s) :
    (Functor.isoWhiskerLeft Fs
        (Functor.isoWhiskerRight n G₀ ≪≫ Functor.leftUnitor G₀)).hom ≫ r.hom ≫ h.hom =
      Functor.whiskerRight af.hom (I ⋙ G₀) ≫
        Functor.whiskerLeft Ft
          (Functor.isoWhiskerRight c G₀ ≪≫ Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft Z t).hom ≫
        ((Functor.associator Ft Z G).symm ≪≫
          Functor.isoWhiskerRight b G ≪≫ s).hom := by
  apply NatTrans.ext
  funext M
  have hl' := congrArg (fun e ↦ e.hom.app M) hl
  have hs' := congrArg (fun e ↦ e.hom.app M) hs
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_hom_app, Category.id_comp, Category.comp_id,
    Category.assoc] at hl' hs'
  simp only [Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id,
    Category.assoc] at hl' hs'
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.comp_map, Functor.map_comp,
    Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
  simp only [Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id,
    Category.assoc]
  rw [hs', ← G₀.map_comp_assoc, hl']
  simp only [Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Functor.comp_obj, Category.assoc] using
    congrArg (fun m ↦ G₀.map (I.map (af.hom.app M)) ≫
      G₀.map (c.hom.app (Ft.obj M)) ≫ m ≫ s.hom.app M)
      (t.hom.naturality (b.hom.app M))

private theorem diagram_factor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : EtaleGraphInterchangeDiagram f g) :
    etaleGraphDiagramInterchange A d =
      Functor.isoWhiskerLeft (d.sourcePresentation.functor A)
        (Functor.isoWhiskerRight (rightDerivedLowerStarIdIso A Y)
          (D((d.i)_!open[ModuleCat.{u + 1} A]) ⋙ R((d.q)_*[ModuleCat.{u + 1} A])) ≪≫
          Functor.leftUnitor _) ≪≫
        EtaleGraphInterchangeDiagram.ProductRow.rawSquare A d := by
  rfl

private theorem middle_factor_First
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) :
    EtaleGraphPresentation.ProductRow.ambientLambda
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) false A =
      Functor.isoWhiskerRight
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
          (EtaleGraphInterchangeDiagram.ProductRow.First.G d₁ d₂).a
          (EtaleGraphPresentation.ProductRow.q
            (EtaleGraphPresentation.ofCompactification d₁.compactification)
            (EtaleGraphPresentation.ofCompactification d₂.compactification) false) (𝟙 Y)
          (EtaleGraphPresentation.ProductRow.z_q
            (EtaleGraphPresentation.ofCompactification d₁.compactification)
            (EtaleGraphPresentation.ofCompactification d₂.compactification) false)).symm)
        (D(((EtaleGraphInterchangeDiagram.ProductRow.First.d d₁ d₂).i)_!open[
            ModuleCat.{u + 1} A]) ⋙
          R(((EtaleGraphInterchangeDiagram.ProductRow.First.d d₁ d₂).q)_*[
            ModuleCat.{u + 1} A])) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (EtaleGraphInterchangeDiagram.ProductRow.First.middleTail d₁ d₂ A) := by
  rfl

private theorem middle_factor_Second
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) :
    EtaleGraphPresentation.ProductRow.ambientLambda
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) true A =
      Functor.isoWhiskerRight
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
          (EtaleGraphInterchangeDiagram.ProductRow.Second.G d₁ d₂).a
          (EtaleGraphPresentation.ProductRow.q
            (EtaleGraphPresentation.ofCompactification d₁.compactification)
            (EtaleGraphPresentation.ofCompactification d₂.compactification) true) (𝟙 Y)
          (EtaleGraphPresentation.ProductRow.z_q
            (EtaleGraphPresentation.ofCompactification d₁.compactification)
            (EtaleGraphPresentation.ofCompactification d₂.compactification) true)).symm)
        (D(((EtaleGraphInterchangeDiagram.ProductRow.Second.d d₁ d₂).i)_!open[
            ModuleCat.{u + 1} A]) ⋙
          R(((EtaleGraphInterchangeDiagram.ProductRow.Second.d d₁ d₂).q)_*[
            ModuleCat.{u + 1} A])) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (EtaleGraphInterchangeDiagram.ProductRow.Second.middleTail d₁ d₂ A) := by
  rfl

/-- Changing the three proper ambient schemes commutes with the supplied square exchange.
This is the proper-projection part of the product grid, before shrinking any supporting open.
Source: Stacks Tag 0F7J, final A--F calculation, with vertical exchange pasting as in
Tag 0F7C (auxiliary; not a blueprint node).

Proof: write the selected side as n and the other as m. The intermediate ambient
neighborhood N is V_n times_Z P_m, its source open is W_n times_Z P_m, and its
middle open is Y times_Z T_m. The maps BV and BW from products over Y are proper:
their composites with the projections to V_n and W_n are proper and those projections
are separated. Their square with the two e opens commutes by the projection equations.
The square with k_n and the product of p is Q, and the square comparing it with the
original supplied square commutes by the same equations. Expand the three ambientLambda
words: each consists only of the proper compositor and a Cartesian side exchange.
Vertical pasting in the proper projection squares identifies the two ways to traverse
the rectangle containing the original square and Q. Paste the B square on the source
side and invert its exchange, moving it past the proper compositor by naturality.
The graph equations z_f BW = z_h and BV R = F.p z_g identify the remaining proper
compositors. Their associativity gives exactly liftInterchange then squareInterchange.
No graph shrinking triangle, product intersection inclusion, or comparison between the
two selected sides enters this calculation. The argument also works for empty opens
and identity maps. All exchanges are the fixed normalized family, rather than chosen
isomorphisms of functors with the same endpoints. -/
theorem etaleGraphProductAmbientPasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) (second : Bool) :
    (match second with
    | false =>
      let af := EtaleGraphPresentation.ProductRow.ambientLambda
        d₁.sourcePresentation d₂.sourcePresentation false A
      let ag := EtaleGraphPresentation.ProductRow.ambientLambda
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) false A
      let ah := EtaleGraphPresentation.ProductRow.ambientLambda
        d₁.compositePresentation d₂.compositePresentation false A
      (etaleGraphDiagramInterchange A d₁).hom ≫ ah.hom =
        Functor.whiskerRight af.hom
            ((EtaleGraphPresentation.ofCompactification d₁.compactification).functor A) ≫
          Functor.whiskerLeft
            ((EtaleGraphInterchangeDiagram.ProductRow.First.F d₁ d₂).functor A) ag.hom ≫
          (EtaleGraphInterchangeDiagram.ProductRow.First.interchange d₁ d₂ A).hom
    | true =>
      let af := EtaleGraphPresentation.ProductRow.ambientLambda
        d₁.sourcePresentation d₂.sourcePresentation true A
      let ag := EtaleGraphPresentation.ProductRow.ambientLambda
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) true A
      let ah := EtaleGraphPresentation.ProductRow.ambientLambda
        d₁.compositePresentation d₂.compositePresentation true A
      (etaleGraphDiagramInterchange A d₂).hom ≫ ah.hom =
        Functor.whiskerRight af.hom
            ((EtaleGraphPresentation.ofCompactification d₂.compactification).functor A) ≫
          Functor.whiskerLeft
            ((EtaleGraphInterchangeDiagram.ProductRow.Second.F d₁ d₂).functor A) ag.hom ≫
          (EtaleGraphInterchangeDiagram.ProductRow.Second.interchange d₁ d₂ A).hom
    ) := by
  cases second
  · have hl := etaleGraphAmbientSourcePasting A d₁ d₂ false
    have hs := etaleGraphAmbientSquarePasting A d₁ d₂ false
    have result := paste_source_and_square
      (Fs := d₁.sourcePresentation.functor A)
      (Ft := (EtaleGraphInterchangeDiagram.ProductRow.First.F d₁ d₂).functor A)
      (G₀ := D((d₁.i)_!open[ModuleCat.{u + 1} A]) ⋙
        R((d₁.q)_*[ModuleCat.{u + 1} A]))
      (rightDerivedLowerStarIdIso A Y)
      (EtaleGraphPresentation.ProductRow.ambientLambda
        d₁.sourcePresentation d₂.sourcePresentation false A)
      ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (EtaleGraphInterchangeDiagram.ProductRow.First.G d₁ d₂).a
        (EtaleGraphPresentation.ProductRow.q
          (EtaleGraphPresentation.ofCompactification d₁.compactification)
          (EtaleGraphPresentation.ofCompactification d₂.compactification) false) (𝟙 Y)
        (EtaleGraphPresentation.ProductRow.z_q
          (EtaleGraphPresentation.ofCompactification d₁.compactification)
          (EtaleGraphPresentation.ofCompactification d₂.compactification) false)).symm)
      (EtaleGraphInterchangeDiagram.ProductRow.First.sourceTransport d₁ d₂ A)
      (EtaleGraphInterchangeDiagram.ProductRow.First.liftInterchange d₁ d₂ A)
      (EtaleGraphInterchangeDiagram.ProductRow.First.middleTail d₁ d₂ A)
      (EtaleGraphInterchangeDiagram.ProductRow.rawSquare A d₁)
      (EtaleGraphPresentation.ProductRow.ambientLambda
        d₁.compositePresentation d₂.compositePresentation false A)
      (EtaleGraphInterchangeDiagram.ProductRow.First.squareInterchange d₁ d₂ A)
      hl hs
    simp only [diagram_factor, middle_factor_First,
      EtaleGraphInterchangeDiagram.ProductRow.First.interchange,
      Iso.trans_hom, Category.assoc]
    dsimp only [EtaleGraphPresentation.functor, EtaleGraphPresentation.ofCompactification,
      EtaleGraphInterchangeDiagram.compactification,
      EtaleGraphInterchangeDiagram.ProductRow.First.d] at result ⊢
    simpa only [Iso.trans_hom, Category.assoc] using result
  · have hl := etaleGraphAmbientSourcePasting A d₁ d₂ true
    have hs := etaleGraphAmbientSquarePasting A d₁ d₂ true
    have result := paste_source_and_square
      (Fs := d₂.sourcePresentation.functor A)
      (Ft := (EtaleGraphInterchangeDiagram.ProductRow.Second.F d₁ d₂).functor A)
      (G₀ := D((d₂.i)_!open[ModuleCat.{u + 1} A]) ⋙
        R((d₂.q)_*[ModuleCat.{u + 1} A]))
      (rightDerivedLowerStarIdIso A Y)
      (EtaleGraphPresentation.ProductRow.ambientLambda
        d₁.sourcePresentation d₂.sourcePresentation true A)
      ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (EtaleGraphInterchangeDiagram.ProductRow.Second.G d₁ d₂).a
        (EtaleGraphPresentation.ProductRow.q
          (EtaleGraphPresentation.ofCompactification d₁.compactification)
          (EtaleGraphPresentation.ofCompactification d₂.compactification) true) (𝟙 Y)
        (EtaleGraphPresentation.ProductRow.z_q
          (EtaleGraphPresentation.ofCompactification d₁.compactification)
          (EtaleGraphPresentation.ofCompactification d₂.compactification) true)).symm)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.sourceTransport d₁ d₂ A)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.liftInterchange d₁ d₂ A)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.middleTail d₁ d₂ A)
      (EtaleGraphInterchangeDiagram.ProductRow.rawSquare A d₂)
      (EtaleGraphPresentation.ProductRow.ambientLambda
        d₁.compositePresentation d₂.compositePresentation true A)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.squareInterchange d₁ d₂ A)
      hl hs
    simp only [diagram_factor, middle_factor_Second,
      EtaleGraphInterchangeDiagram.ProductRow.Second.interchange,
      Iso.trans_hom, Category.assoc]
    dsimp only [EtaleGraphPresentation.functor, EtaleGraphPresentation.ofCompactification,
      EtaleGraphInterchangeDiagram.compactification,
      EtaleGraphInterchangeDiagram.ProductRow.Second.d] at result ⊢
    simpa only [Iso.trans_hom, Category.assoc] using result

end AlgebraicGeometry.Etale
