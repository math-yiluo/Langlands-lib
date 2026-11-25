/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.EtaleGlobalSectionSquare
import WeilConjectures.AlgebraicGeometry.EtaleGeometricSectionTwoPullbacks

/-! # Cech compatibility over one connected geometric fibre

Source: Stacks Project, Tag 0A3H, final paragraph.
(blueprint: lem-weil-pbc-etale-cech-sections-connected-geometric-fibre).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

local notation "L" => Scheme.etaleSetPullback
local notation "I[" X "]" => Scheme.Etale.mk (𝟙 X)
set_option quotPrecheck false in
local notation "η[" X "," Y "]" e =>
  Adjunction.unit
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ e) _
      (Scheme.smallGrothendieckTopology @Etale X)
      (Scheme.smallGrothendieckTopology @Etale Y))
set_option quotPrecheck false in
local notation "R[" X "," Y "," e "," G "]" =>
  (((η[X,Y] e).app G).hom.app (op I[X]) ≫
    ((L e).obj G).obj.map
      (MorphismProperty.Over.homMk
        (pullback.lift e (𝟙 Y)
          ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp) :
        I[Y] ⟶ (MorphismProperty.Over.pullback @Etale ⊤ e).obj I[X]).op)

set_option backward.isDefEq.respectTransparency false in
/-- The two Cech pullbacks agree after restriction to one connected geometric fibre.
Only that fibre is assumed connected; no assertion of equality on the whole Cech
scheme is made.

Source: Stacks Project, Tag 0A3H, final paragraph.
(blueprint: lem-weil-pbc-etale-cech-sections-connected-geometric-fibre).

Proof:
1. Put U = T ×_S Spec Ω, with projections p and h. Define the two maps
   v_i : E → U as the pullback lifts of (d ≫ pr_i, w), where w : E → Spec Ω
   is the second projection. The pullback equations give v_i ≫ p = d ≫ pr_i
   and v_i ≫ h = w.
2. Apply etaleSet_globalSection_square to each of these commutative squares.
   It identifies each restricted Cech section, after applying the composition
   isomorphism for g and d, with the pullback along v_i of the common section
   obtained by restricting a along p and comparing p ≫ f with h ≫ q.
3. Apply etaleSet_geometricSection_two_pullbacks on connected U to identify
   these two pullbacks. It uses etaleGeometricFibreConstantSections and its
   naturality, without any connectedness or nonemptiness assumption on E.
4. The composition comparison for g and d is an isomorphism, so its component
   on global sections is injective. Cancel it to obtain the displayed equality. -/
theorem etaleSet_cech_sections_agree_on_connected_geometric_fibre
    {S T : Scheme.{u}} (f : T ⟶ S)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (q : Spec (.of Ω) ⟶ S)
    [ConnectedSpace (pullback f q : Scheme.{u})]
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (a : ((L f).obj F).obj.obj (op I[T])) :
    let D := pullback f f
    let g := pullback.fst f f ≫ f
    let E := pullback g q
    let d := pullback.fst g q
    let G := (L g).obj F
    R[D,E,d,G]
      (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
          S T (pullback f f) f (pullback.fst f f)).hom.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 (pullback f f))))
        (((Scheme.etaleSetPullback (pullback.fst f f)).obj
            ((Scheme.etaleSetPullback f).obj F)).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift (pullback.fst f f) (𝟙 (pullback f f))
              ((Category.comp_id _).trans (Category.id_comp _).symm))
            (by simp) :
            Scheme.Etale.mk (𝟙 (pullback f f)) ⟶
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst f f)).obj
                (Scheme.Etale.mk (𝟙 T))).op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst f f)) _
            (T.smallGrothendieckTopology @Etale)
            ((pullback f f).smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback f).obj F)).hom.app
            (op (Scheme.Etale.mk (𝟙 T))) a))) =
    R[D,E,d,G]
      (Eq.mp (congrArg (fun k : pullback f f ⟶ S ↦
          ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op (Scheme.Etale.mk (𝟙 (pullback f f)))))
          (pullback.condition (f := f) (g := f)).symm)
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
            S T (pullback f f) f (pullback.snd f f)).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 (pullback f f))))
          (((Scheme.etaleSetPullback (pullback.snd f f)).obj
              ((Scheme.etaleSetPullback f).obj F)).obj.map
            (MorphismProperty.Over.homMk
              (pullback.lift (pullback.snd f f) (𝟙 (pullback f f))
                ((Category.comp_id _).trans (Category.id_comp _).symm))
              (by simp) :
              Scheme.Etale.mk (𝟙 (pullback f f)) ⟶
                (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd f f)).obj
                  (Scheme.Etale.mk (𝟙 T))).op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd f f)) _
              (T.smallGrothendieckTopology @Etale)
              ((pullback f f).smallGrothendieckTopology @Etale)).unit.app
                ((Scheme.etaleSetPullback f).obj F)).hom.app
              (op (Scheme.Etale.mk (𝟙 T))) a)))) := by
  classical
  let U := pullback f q
  let p : U ⟶ T := pullback.fst f q
  let h : U ⟶ Spec (.of Ω) := pullback.snd f q
  let D := pullback f f
  let k₁ : D ⟶ T := pullback.fst f f
  let k₂ : D ⟶ T := pullback.snd f f
  let g := k₁ ≫ f
  let E := pullback g q
  let d : E ⟶ D := pullback.fst g q
  let w : E ⟶ Spec (.of Ω) := pullback.snd g q
  have hp : p ≫ f = h ≫ q := pullback.condition
  have hk : k₂ ≫ f = g := (pullback.condition (f := f) (g := f)).symm
  have ht : w ≫ q = d ≫ g := (pullback.condition (f := g) (g := q)).symm
  let v₁ : E ⟶ U := pullback.lift (d ≫ k₁) w (by
    rw [Category.assoc]
    exact ht.symm)
  let v₂ : E ⟶ U := pullback.lift (d ≫ k₂) w (by
    rw [Category.assoc, hk]
    exact ht.symm)
  have hw₁ : v₁ ≫ h = w := by simp [v₁, h]
  have hw₂ : v₂ ≫ h = w := by simp [v₂, h]
  have hs₁ : d ≫ k₁ = v₁ ≫ p := by simp [v₁, p]
  have hs₂ : d ≫ k₂ = v₂ ≫ p := by simp [v₂, p]
  have H₁ := etaleSet_globalSection_square f k₁ d p v₁ g (h ≫ q) (d ≫ g)
    rfl hp rfl (by rw [← Category.assoc, hw₁, ht]) hs₁ F a
  have H₂ := etaleSet_globalSection_square f k₂ d p v₂ g (h ≫ q) (d ≫ g)
    hk hp rfl (by rw [← Category.assoc, hw₂, ht]) hs₂ F a
  have Hc := etaleSet_geometricSection_two_pullbacks Ω q h w v₁ v₂ hw₁ hw₂
    (d ≫ g) ht F
    (Eq.mp (congrArg (fun j : U ⟶ S =>
      ((L j).obj F).obj.obj (op I[U])) hp)
      (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
        S T U f p).hom.app F).hom.app (op I[U])
          (R[T,U,p,(L f).obj F] a)))
  have H := H₁.trans (Hc.trans H₂.symm)
  have hi : Function.Injective
      (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
        _ _ _ g d).hom.app F).hom.app (op I[E])) :=
    ((CategoryTheory.isIso_iff_bijective _).1 inferInstance).1
  apply hi
  exact H

end AlgebraicGeometry
