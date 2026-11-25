/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProetaleConstantSplitDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.LocalProperties

/-! # Representing a sheaf from effective pro-etale descent

Source: blueprint `lemma-lattices-lisse-e-sheaves`, proof (2)
(blueprint: lem-sfb-proetale-effective-sheaf-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

private theorem iso_of_compatible_slice
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F H : Sheaf J (Type (u + 2))) (V : C)
    (hV : J.CoversTop (fun _ : PUnit.{u + 2} ↦ V))
    (k : H.over V ≅ F.over V)
    (hk : ∀ (W : C) (a b : W ⟶ V),
      (J.overMapPullback (Type (u + 2)) a).map k.hom =
        (J.overMapPullback (Type (u + 2)) b).map k.hom) : Nonempty (H ≅ F) := by
  let x : Presheaf.FamilyOfElementsOnObjects (sheafHom H F).obj
      (fun _ : PUnit.{u + 2} ↦ V) := fun _ ↦ k.hom
  have hx : x.IsCompatible := fun W _ _ a b ↦ hk W a b
  obtain ⟨s, hs, _⟩ := hx.existsUnique_section hV (sheafHom H F).property
  let f : H ⟶ F := sheafHomSectionsEquiv H F s
  have hf : (J.overPullback (Type (u + 2)) V).map f = k.hom := by
    rw [← sheafHomSectionsEquiv_symm_apply_coe_apply]
    change ((sheafHomSectionsEquiv H F).symm ((sheafHomSectionsEquiv H F) s)).1
      (op V) = _
    rw [Equiv.symm_apply_apply]
    exact hs PUnit.unit
  have : IsIso f := Sheaf.isIso_of_coversTop hV (fun _ ↦ by rw [hf]; infer_instance)
  exact ⟨asIso f⟩

private theorem iso_of_compatible_equiv
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F H : Sheaf J (Type (u + 2))) (V : C)
    (hV : J.CoversTop (fun _ : PUnit.{u + 2} ↦ V))
    (e : ∀ W : Over V, H.obj.obj (op W.left) ≃ F.obj.obj (op W.left))
    (hnat : ∀ (W W' : Over V) (g : W' ⟶ W) (x : H.obj.obj (op W.left)),
      e W' (H.obj.map g.left.op x) = F.obj.map g.left.op (e W x))
    (hcompat : ∀ (W : C) (a b : W ⟶ V) (x : H.obj.obj (op W)),
      e (Over.mk a) x = e (Over.mk b) x) : Nonempty (H ≅ F) := by
  let k : (H.over V).obj ≅ (F.over V).obj :=
    NatIso.ofComponents (fun W ↦ Equiv.toIso (e W.unop)) (by
      intro W W' g
      ext x
      exact hnat W.unop W'.unop g.unop x)
  let k' : H.over V ≅ F.over V :=
    { hom := ObjectProperty.homMk k.hom
      inv := ObjectProperty.homMk k.inv
      hom_inv_id := by ext; simp
      inv_hom_id := by ext; simp }
  apply iso_of_compatible_slice J F H V hV k'
  intro W a b
  apply Sheaf.hom_ext
  ext A x
  exact hcompat A.unop.left (A.unop.hom ≫ a) (A.unop.hom ≫ b) x

/-- Explicit equivalence between points of an étale object and points in the
pro-etale slice after a pullback square. Source: blueprint proof (2).
(blueprint: lem-sfb-proetale-effective-sheaf-descent, step 2). -/
noncomputable def effectivePointEquiv {X V T : Scheme.{u}}
    (p : V ⟶ X) [WeaklyEtale p] (t : T ⟶ V) (Z : X.Etale)
    (q : T ⟶ Z.left) (hq : IsPullback q t Z.hom p)
    (W : Over (Scheme.ProEt.mk p)) :
    (W.left ⟶ (Scheme.toProEt X).obj Z) ≃
      ((proetaleSliceToOver p).obj W ⟶ Over.mk t) where
  toFun a := Over.homMk
    (hq.lift a.left W.hom.left
      ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w W.hom).symm))
    (hq.lift_snd _ _ _)
  invFun f := MorphismProperty.Over.homMk (f.left ≫ q) (by
    change f.left ≫ q ≫ Z.hom = W.left.hom
    calc
      (f.left ≫ q) ≫ Z.hom = f.left ≫ (q ≫ Z.hom) := Category.assoc _ _ _
      _ = f.left ≫ (t ≫ p) := congrArg (fun z ↦ f.left ≫ z) hq.w
      _ = (f.left ≫ t) ≫ p := (Category.assoc _ _ _).symm
      _ = ((proetaleSliceToOver p).obj W).hom ≫ p :=
        congrArg (fun z ↦ z ≫ p) (Over.w f)
      _ = W.left.hom := by
        exact MorphismProperty.Over.w W.hom)
  left_inv a := MorphismProperty.Over.Hom.ext (hq.lift_fst _ _ _)
  right_inv f := Over.OverMorphism.ext (hq.hom_ext
    (hq.lift_fst _ _ _) ((hq.lift_snd _ _ _).trans (Over.w f).symm))

private theorem effectivePointEquiv_comp_q {X V T : Scheme.{u}}
    (p : V ⟶ X) [WeaklyEtale p] (t : T ⟶ V) (Z : X.Etale)
    (q : T ⟶ Z.left) (hq : IsPullback q t Z.hom p)
    (W : Over (Scheme.ProEt.mk p)) (a : W.left ⟶ (Scheme.toProEt X).obj Z) :
    (effectivePointEquiv p t Z q hq W a).left ≫ q = a.left :=
  hq.lift_fst _ _ _

/-- Naturality of the pullback-point equivalence. Source: blueprint proof (2).
(blueprint: lem-sfb-proetale-effective-point-naturality). -/
theorem effectivePointEquiv_naturality {X V T : Scheme.{u}}
    (p : V ⟶ X) [WeaklyEtale p] (t : T ⟶ V) (Z : X.Etale)
    (q : T ⟶ Z.left) (hq : IsPullback q t Z.hom p)
    (W W' : Over (Scheme.ProEt.mk p)) (g : W' ⟶ W)
    (a : W.left ⟶ (Scheme.toProEt X).obj Z) :
    effectivePointEquiv p t Z q hq W' (g.left ≫ a) =
      (proetaleSliceToOver p).map g ≫ effectivePointEquiv p t Z q hq W a := by
  apply Over.OverMorphism.ext
  change hq.lift _ _ _ = _
  apply hq.hom_ext
  · rw [hq.lift_fst]
    change g.left.left ≫ a.left =
      (g.left.left ≫ hq.lift a.left W.hom.left _) ≫ q
    simp only [Category.assoc, hq.lift_fst]
  · change hq.lift (g.left ≫ a).left W'.hom.left _ ≫ t =
      (g.left.left ≫ hq.lift a.left W.hom.left _) ≫ t
    simp only [hq.lift_snd, Category.assoc]
    exact (congrArg (fun z ↦ z.left) g.w).symm


/-- The pullback-point equivalence intertwines descent transport with the second
projection. Source: blueprint proof (2).
(blueprint: lem-sfb-proetale-effective-point-transport). -/
theorem effectivePointEquiv_transport {X V T : Scheme.{u}}
    (p : V ⟶ X) [WeaklyEtale p] (t : T ⟶ V) (Z : X.Etale)
    (q : T ⟶ Z.left) (hq : IsPullback q t Z.hom p)
    (D : Over.DescentDatum p (Over.mk t))
    (hD : ∀ {A : Scheme.{u}} (a b : A ⟶ V) (h : a ≫ p = b ≫ p)
      (f : Over.mk a ⟶ Over.mk t), (D.transport a b h f).left ≫ q = f.left ≫ q)
    (W : X.ProEt) (a b : W ⟶ Scheme.ProEt.mk p)
    (s : W ⟶ (Scheme.toProEt X).obj Z) :
    D.transport a.left b.left
        ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
        (effectivePointEquiv p t Z q hq (Over.mk a) s) =
      effectivePointEquiv p t Z q hq (Over.mk b) s := by
  apply Over.OverMorphism.ext
  apply hq.hom_ext
  · rw [hD, effectivePointEquiv_comp_q, effectivePointEquiv_comp_q]
  · calc
      (D.transport a.left b.left
          ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
          (effectivePointEquiv p t Z q hq (Over.mk a) s)).left ≫ t = b.left :=
        (D.transport a.left b.left
          ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
          (effectivePointEquiv p t Z q hq (Over.mk a) s)).w
      _ = (effectivePointEquiv p t Z q hq (Over.mk b) s).left ≫ t :=
        (effectivePointEquiv p t Z q hq (Over.mk b) s).w.symm

/-- Effective pro-etale descent represents the sheaf by the descended etale object.
Source: blueprint `lemma-lattices-lisse-e-sheaves`, proof (2).

Proof. The pro-etale topology is subcanonical, so the lifted Yoneda presheaf `H` of `Z`
is a sheaf. On the slice over `V` the pullback square gives `effectivePointEquiv`;
composed with `rho` it is a natural bijection `H(W) ≃ F(W)`
(`effectivePointEquiv_naturality`, `hnat`). For two `V`-structures `a, b` on one test
object, `effectivePointEquiv_transport` and `hcompat` show the bijections agree, so the
local isomorphism glues in the sheaf `sheafHom H F` over the cover `hcover`; the glued
morphism restricts to an isomorphism, hence is one (`Sheaf.isIso_of_coversTop`). Full
faithfulness of `Scheme.ProEt.forget X` identifies `H` with the stated lifted Hom presheaf.
(blueprint: lem-sfb-proetale-effective-sheaf-descent). -/
theorem representable_of_effective_proetale_descent {X V T : Scheme.{u}}
    (p : V ⟶ X) [WeaklyEtale p]
    (t : T ⟶ V) (Z : X.Etale) (q : T ⟶ Z.left)
    (hq : IsPullback q t Z.hom p)
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
    (rho : ∀ W : Over (Scheme.ProEt.mk p),
      ((proetaleSliceToOver p).obj W ⟶ Over.mk t) ≃ F.obj.obj (op W.left))
    (hnat : ∀ (W W' : Over (Scheme.ProEt.mk p)) (g : W' ⟶ W)
      (f : (proetaleSliceToOver p).obj W ⟶ Over.mk t),
      rho W' ((proetaleSliceToOver p).map g ≫ f) =
        F.obj.map g.left.op (rho W f))
    (D : Over.DescentDatum p (Over.mk t))
    (hD : ∀ {A : Scheme.{u}} (a b : A ⟶ V) (h : a ≫ p = b ≫ p)
      (f : Over.mk a ⟶ Over.mk t), (D.transport a b h f).left ≫ q = f.left ≫ q)
    (hcompat : ∀ (W : X.ProEt) (a b : W ⟶ Scheme.ProEt.mk p)
      (f : Over.mk a.left ⟶ Over.mk t),
      rho (Over.mk b) (D.transport a.left b.left
        ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm) f) =
          rho (Over.mk a) f)
    (hcover : (Scheme.ProEt.topology X).CoversTop
      (fun _ : PUnit.{u + 2} ↦ Scheme.ProEt.mk p)) :
    Nonempty (F.obj ≅ (Scheme.ProEt.forget X).op ⋙
      yoneda.obj ((Scheme.Etale.forget X).obj Z) ⋙ uliftFunctor.{u + 2}) := by
  let H := (Scheme.ProEt.topology X).uliftYoneda.{u + 2}.obj ((Scheme.toProEt X).obj Z)
  let e (W : Over (Scheme.ProEt.mk p)) :
      (H.over (Scheme.ProEt.mk p)).obj.obj (op W) ≃
        (F.over (Scheme.ProEt.mk p)).obj.obj (op W) := by
    exact (Equiv.ulift.trans (effectivePointEquiv p t Z q hq W)).trans (rho W)
  obtain ⟨i⟩ := iso_of_compatible_equiv (Scheme.ProEt.topology X) F H
    (Scheme.ProEt.mk p) hcover e (by
      intro W W' g x
      change rho W' (effectivePointEquiv p t Z q hq W'
        (g.left ≫ x.down)) = _
      rw [effectivePointEquiv_naturality p t Z q hq W W' g]
      exact hnat W W' g _) (by
      intro W a b x
      exact (hcompat W a b _).symm.trans
        (congrArg (rho (Over.mk b))
          (effectivePointEquiv_transport p t Z q hq D hD W a b x.down)))
  let c : H.obj ≅ (Scheme.ProEt.forget X).op ⋙
      yoneda.obj ((Scheme.Etale.forget X).obj Z) ⋙ uliftFunctor.{u + 2} := by
    let e' (W : X.ProEt) :
        ULift.{u + 2} (W ⟶ (Scheme.toProEt X).obj Z) ≃
        ULift.{u + 2} ((Scheme.ProEt.forget X).obj W ⟶
          (Scheme.Etale.forget X).obj Z) :=
      (Equiv.ulift.trans
        (Functor.FullyFaithful.ofFullyFaithful (Scheme.ProEt.forget X)).homEquiv).trans
          Equiv.ulift.symm
    exact NatIso.ofComponents (fun W ↦ Equiv.toIso (e' W.unop)) (by
      intro W W' g
      ext x
      rfl)
  exact ⟨(sheafToPresheaf _ _).mapIso i.symm ≪≫ c⟩

end AlgebraicGeometry.ProEtale
