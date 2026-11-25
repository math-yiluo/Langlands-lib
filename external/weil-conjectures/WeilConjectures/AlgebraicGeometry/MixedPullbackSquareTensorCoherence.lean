/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionTensorKFlat

/-! # Tensor coherence of the canonical pullback square
Source: Stacks Project, cohomology.tex, Tags 079U and 08HY;
duality.tex, Tag 0AA8, final comparison diagrams.
(blueprint: lem-sc-mixed-pullback-square-tensor-coherence).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

attribute [local irreducible] mixedHomTensorPullbackIso schemeDerivedTensorMonoidal

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Canonical square comparison, made from the fixed composition comparisons.
Source: Stacks Project, Remark 08HY
(blueprint: lem-sc-mixed-pullback-square-tensor-coherence). -/
def mixedPullbackSquareComparison
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    derivedPullback g ⋙ derivedPullback (pullback.snd f g) ≅
      derivedPullback f ⋙ derivedPullback (pullback.fst f g) :=
  let c : ∀ {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W),
      derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
    fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) a b
  c (pullback.snd f g) g ≪≫
    eqToIso (congrArg (fun k : pullback f g ⟶ Y => derivedPullback k)
      pullback.condition.symm) ≪≫ (c (pullback.fst f g) f).symm

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private def composite_tensor_iso
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E)
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (s : tensor D ⋙ G ≅ G.prod G ⋙ tensor E) :
    tensor C ⋙ (F ⋙ G) ≅ (F ⋙ G).prod (F ⋙ G) ⋙ tensor E :=
  Functor.isoWhiskerRight t G ≪≫ Functor.isoWhiskerLeft (F.prod F) s

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem tensor_compatible_of_iso
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F G : C ⥤ D}
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (s : tensor C ⋙ G ≅ G.prod G ⋙ tensor D) (c : F ≅ G)
    {P₀ N₀ P N : C} (eP : P₀ ≅ P) (eN : N₀ ≅ N)
    (h : t.hom.app (P₀, N₀) ≫ (c.hom.app P₀ ⊗ₘ c.hom.app N₀) =
      c.hom.app (P₀ ⊗ N₀) ≫ s.hom.app (P₀, N₀)) :
    t.hom.app (P, N) ≫ (c.hom.app P ⊗ₘ c.hom.app N) =
      c.hom.app (P ⊗ N) ≫ s.hom.app (P, N) := by
  let a : tensor C ⋙ F ⟶ G.prod G ⋙ tensor D :=
    t.hom ≫ Functor.whiskerRight (NatTrans.prod c.hom c.hom) _
  let b : tensor C ⋙ F ⟶ G.prod G ⋙ tensor D :=
    Functor.whiskerLeft _ c.hom ≫ s.hom
  let e : (P₀, N₀) ≅ (P, N) :=
    { hom := (eP.hom, eN.hom)
      inv := (eP.inv, eN.inv)
      hom_inv_id := by ext <;> simp
      inv_hom_id := by ext <;> simp }
  change a.app (P₀, N₀) = b.app (P₀, N₀) at h
  change a.app (P, N) = b.app (P, N)
  apply (cancel_epi ((tensor C ⋙ F).mapIso e).hom).1
  change (tensor C ⋙ F).map e.hom ≫ a.app (P, N) =
    (tensor C ⋙ F).map e.hom ≫ b.app (P, N)
  rw [a.naturality, b.naturality, h]

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem tensor_compatible_trans
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F G H : C ⥤ D}
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (s : tensor C ⋙ G ≅ G.prod G ⋙ tensor D)
    (r : tensor C ⋙ H ≅ H.prod H ⋙ tensor D)
    (c : F ≅ G) (d : G ≅ H) (P N : C)
    (hc : t.hom.app (P, N) ≫ (c.hom.app P ⊗ₘ c.hom.app N) =
      c.hom.app (P ⊗ N) ≫ s.hom.app (P, N))
    (hd : s.hom.app (P, N) ≫ (d.hom.app P ⊗ₘ d.hom.app N) =
      d.hom.app (P ⊗ N) ≫ r.hom.app (P, N)) :
    t.hom.app (P, N) ≫ ((c ≪≫ d).hom.app P ⊗ₘ (c ≪≫ d).hom.app N) =
      (c ≪≫ d).hom.app (P ⊗ N) ≫ r.hom.app (P, N) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, ← tensorHom_comp_tensorHom, Category.assoc]
  rw [reassoc_of% hc, hd]

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem tensor_compatible_symm
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F G : C ⥤ D}
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (s : tensor C ⋙ G ≅ G.prod G ⋙ tensor D)
    (c : F ≅ G) (P N : C)
    (hc : t.hom.app (P, N) ≫ (c.hom.app P ⊗ₘ c.hom.app N) =
      c.hom.app (P ⊗ N) ≫ s.hom.app (P, N)) :
    s.hom.app (P, N) ≫ (c.inv.app P ⊗ₘ c.inv.app N) =
      c.inv.app (P ⊗ N) ≫ t.hom.app (P, N) := by
  apply (cancel_epi (c.hom.app (P ⊗ N))).1
  rw [← reassoc_of% hc]
  rw [tensorHom_comp_tensorHom]
  simp only [Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  rw [id_tensorHom_id (F.obj P) (F.obj N)]
  exact Category.comp_id (t.hom.app (P, N))

private theorem equality_tensor {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (P N : schemeDerivedCategory Y) :
    (mixedHomTensorPullbackIso f).hom.app (P, N) ≫
        ((eqToIso (congrArg (fun k : X ⟶ Y ↦ derivedPullback k) h)).hom.app P ⊗ₘ
          (eqToIso (congrArg (fun k : X ⟶ Y ↦ derivedPullback k) h)).hom.app N) =
      (eqToIso (congrArg (fun k : X ⟶ Y ↦ derivedPullback k) h)).hom.app (P ⊗ N) ≫
        (mixedHomTensorPullbackIso g).hom.app (P, N) := by
  subst g
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rw [id_tensorHom_id ((derivedPullback f).obj P) ((derivedPullback f).obj N)]
  exact Category.comp_id ((mixedHomTensorPullbackIso f).hom.app (P, N))

private theorem composition_tensor
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P N : schemeDerivedCategory Z) :
    let c : ∀ {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W),
        derivedPullback.{u, w} b ⋙ derivedPullback.{u, w} a ≅
        derivedPullback.{u, w} (a ≫ b) :=
      fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) a b
    (derivedPullback f).map ((mixedHomTensorPullbackIso g).hom.app (P, N)) ≫
      (mixedHomTensorPullbackIso f).hom.app
        ((derivedPullback g).obj P, (derivedPullback g).obj N) ≫
      ((c f g).hom.app P ⊗ₘ (c f g).hom.app N) =
    (c f g).hom.app (P ⊗ N) ≫
      (mixedHomTensorPullbackIso (f ≫ g)).hom.app (P, N) := by
  classical
  let cs := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
  let c := cs f g
  let t := composite_tensor_iso (derivedPullback.{u, w} g) (derivedPullback.{u, w} f)
    (mixedHomTensorPullbackIso g) (mixedHomTensorPullbackIso f)
  let p := Classical.choice (SingleComplexBaseChange.nonempty_coordinates.{u, w} g P
    ((derivedPullback.{u, w} g).obj P) (𝟙 _))
  let n := Classical.choice (SingleComplexBaseChange.nonempty_coordinates.{u, w} g N
    ((derivedPullback.{u, w} g).obj N) (𝟙 _))
  have h₀ := derivedPullbackComposition_tensor_kFlat f g p.P n.P p.isKFlat n.isKFlat
  have h := tensor_compatible_of_iso t (mixedHomTensorPullbackIso (f ≫ g)) c p.e n.e
    (by simpa only [t, composite_tensor_iso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj,
      Functor.prod_obj, tensor_obj, Category.assoc] using h₀)
  simpa only [t, composite_tensor_iso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj,
    Functor.prod_obj, tensor_obj, Category.assoc] using h

/-- Tensor coherence of the canonical square comparison.
Source: Stacks Project, cohomology.tex, Lemma 079U and Remark 08HY;
duality.tex, Tag 0AA8, final comparison diagrams.
(blueprint: lem-sc-mixed-pullback-square-tensor-coherence).

Proof: choose K-flat representatives of P and Q. Their tensor and successive
pullbacks are K-flat. The normalization equations identify all four tensorators with
ordinary pullback tensor comparisons, and the two composition comparisons with the
mates of ordinary direct-image composition. Both ordinary paths carry a pure tensor
to the tensor of the same pulled-back sections. Localize this equality and cancel
only the invertible K-flat derived counits. Naturality and resolution isomorphisms
transport the result to arbitrary P and Q. Equality of the scheme composites supplies
the canonical equality transport. No base-change morphism is cancelled. -/
theorem mixedPullbackSquareComparison_tensor
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (P Q : schemeDerivedCategory Y) :
    (derivedPullback (pullback.snd f g)).map
        ((mixedHomTensorPullbackIso g).hom.app (P, Q)) ≫
      (mixedHomTensorPullbackIso (pullback.snd f g)).hom.app
        ((derivedPullback g).obj P, (derivedPullback g).obj Q) ≫
      ((mixedPullbackSquareComparison f g).hom.app P ⊗ₘ
        (mixedPullbackSquareComparison f g).hom.app Q) =
    (mixedPullbackSquareComparison f g).hom.app (P ⊗ Q) ≫
      (derivedPullback (pullback.fst f g)).map
        ((mixedHomTensorPullbackIso f).hom.app (P, Q)) ≫
      (mixedHomTensorPullbackIso (pullback.fst f g)).hom.app
        ((derivedPullback f).obj P, (derivedPullback f).obj Q) := by
  classical
  let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
  let a := c (pullback.snd f g) g
  let b := c (pullback.fst f g) f
  let e := eqToIso (congrArg (fun k : pullback f g ⟶ Y ↦ derivedPullback.{u, w} k)
    pullback.condition.symm)
  let t₁ := composite_tensor_iso (derivedPullback.{u, w} g)
    (derivedPullback.{u, w} (pullback.snd f g))
    (mixedHomTensorPullbackIso g) (mixedHomTensorPullbackIso (pullback.snd f g))
  let t₂ := composite_tensor_iso (derivedPullback.{u, w} f)
    (derivedPullback.{u, w} (pullback.fst f g))
    (mixedHomTensorPullbackIso f) (mixedHomTensorPullbackIso (pullback.fst f g))
  have h₁ := composition_tensor (pullback.snd f g) g P Q
  have h₂ := composition_tensor (pullback.fst f g) f P Q
  have he := equality_tensor (pullback.condition (f := f) (g := g)).symm P Q
  have hi := tensor_compatible_symm t₂ (mixedHomTensorPullbackIso _) b P Q
    (by simpa only [t₂, composite_tensor_iso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj,
      Functor.prod_obj, tensor_obj, Category.assoc] using h₂)
  have ht := tensor_compatible_trans t₁ (mixedHomTensorPullbackIso _)
    (mixedHomTensorPullbackIso _) a e P Q
    (by simpa only [t₁, composite_tensor_iso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj,
      Functor.prod_obj, tensor_obj, Category.assoc] using h₁) he
  have h := tensor_compatible_trans t₁ (mixedHomTensorPullbackIso _) t₂
    (a ≪≫ e) b.symm P Q ht hi
  have hcomp : mixedPullbackSquareComparison f g = (a ≪≫ e) ≪≫ b.symm := by
    change a ≪≫ (e ≪≫ b.symm) = (a ≪≫ e) ≪≫ b.symm
    exact (Iso.trans_assoc a e b.symm).symm
  rw [hcomp]
  simpa only [t₁, t₂, composite_tensor_iso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj,
    Functor.prod_obj, tensor_obj, Category.assoc] using h

end AlgebraicGeometry
