/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SimplicialHomObject
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Hom objects and simplicial pushouts

Source: Stacks Project, Lemma 017N (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u₁ w₁ t₁

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.Scheme

private abbrev liftedSSet.{v, t} (S : SSet.{t}) := S ⋙ uliftFunctor.{v}

private abbrev familyTarget {X : Scheme.{u₁}}
    (K : SimplicialObject (FormalCoproduct.{w₁} X.Etale))
    (W : FormalCoproduct.{w₁} X.Etale) := K ⋙ coyoneda.obj (op W) ⋙ uliftFunctor.{t₁}

private def familyToNatTrans {X : Scheme.{u₁}}
    {K : SimplicialObject (FormalCoproduct.{w₁} X.Etale)} {S : SSet.{t₁}}
    {W : FormalCoproduct.{w₁} X.Etale} (f : SimplicialHomFamily K S W) :
    liftedSSet.{max u₁ w₁} S ⟶ familyTarget.{u₁, w₁, t₁} K W where
  app n := TypeCat.ofHom (fun s ↦ ⟨f.val n.unop.len s.down⟩)
  naturality {m n} φ := by
    ext s
    exact ULift.ext (f.property n.unop.len m.unop.len φ.unop s.down).symm

private def natTransToFamily {X : Scheme.{u₁}}
    {K : SimplicialObject (FormalCoproduct.{w₁} X.Etale)} {S : SSet.{t₁}}
    {W : FormalCoproduct.{w₁} X.Etale}
    (f : liftedSSet.{max u₁ w₁} S ⟶ familyTarget.{u₁, w₁, t₁} K W) :
    SimplicialHomFamily K S W :=
  ⟨fun n s ↦ (f.app (op ⦋n⦌) ⟨s⟩).down, by
    intro m n φ s
    exact (congrArg ULift.down (ConcreteCategory.congr_hom (f.naturality φ.op) ⟨s⟩)).symm⟩

private lemma familyToNatTrans_injective {X : Scheme.{u₁}}
    {K : SimplicialObject (FormalCoproduct.{w₁} X.Etale)} {S : SSet.{t₁}}
    {W : FormalCoproduct.{w₁} X.Etale} :
    Function.Injective (familyToNatTrans (K := K) (S := S) (W := W)) := by
  intro f g h
  apply Subtype.ext
  funext n s
  exact congrArg ULift.down (ConcreteCategory.congr_hom (congr_app h (op ⦋n⦌)) ⟨s⟩)

private theorem glueFamilies {X : Scheme.{u₁}}
    {K : SimplicialObject (FormalCoproduct.{w₁} X.Etale)}
    {A B C D : SSet.{t₁}} {p : A ⟶ B} {q : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hpush : CategoryTheory.IsPushout p q i j) {W : FormalCoproduct.{w₁} X.Etale}
    (fB : SimplicialHomFamily K B W) (fC : SimplicialHomFamily K C W)
    (hagree : ∀ n s, fB.val n (p.app (op ⦋n⦌) s) = fC.val n (q.app (op ⦋n⦌) s)) :
    ∃ fD : SimplicialHomFamily K D W,
      (∀ n s, fD.val n (i.app (op ⦋n⦌) s) = fB.val n s) ∧
      (∀ n s, fD.val n (j.app (op ⦋n⦌) s) = fC.val n s) := by
  let L := (Functor.whiskeringRight SimplexCategoryᵒᵖ (Type t₁) (Type (max u₁ w₁ t₁))).obj
    uliftFunctor.{max u₁ w₁}
  have hL := L.map_isPushout hpush
  have hw : L.map p ≫ familyToNatTrans fB = L.map q ≫ familyToNatTrans fC := by
    ext n s
    exact ULift.ext (hagree n.unop.len s.down)
  let d := hL.desc (familyToNatTrans fB) (familyToNatTrans fC) hw
  refine ⟨natTransToFamily d, ?_, ?_⟩
  · intro n s
    exact congrArg ULift.down (ConcreteCategory.congr_hom
      (congr_app (hL.inl_desc (familyToNatTrans fB) (familyToNatTrans fC) hw)
        (op ⦋n⦌)) ⟨s⟩)
  · intro n s
    exact congrArg ULift.down (ConcreteCategory.congr_hom
      (congr_app (hL.inr_desc (familyToNatTrans fB) (familyToNatTrans fC) hw)
        (op ⦋n⦌)) ⟨s⟩)

private theorem family_pushout_ext {X : Scheme.{u₁}}
    {K : SimplicialObject (FormalCoproduct.{w₁} X.Etale)}
    {A B C D : SSet.{t₁}} {p : A ⟶ B} {q : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hpush : CategoryTheory.IsPushout p q i j) {W : FormalCoproduct.{w₁} X.Etale}
    {f g : SimplicialHomFamily K D W}
    (hi : ∀ n s, f.val n (i.app (op ⦋n⦌) s) = g.val n (i.app (op ⦋n⦌) s))
    (hj : ∀ n s, f.val n (j.app (op ⦋n⦌) s) = g.val n (j.app (op ⦋n⦌) s)) : f = g := by
  let L := (Functor.whiskeringRight SimplexCategoryᵒᵖ (Type t₁) (Type (max u₁ w₁ t₁))).obj
    uliftFunctor.{max u₁ w₁}
  have hL := L.map_isPushout hpush
  apply familyToNatTrans_injective
  apply hL.hom_ext
  · ext n s
    exact ULift.ext (hi n.unop.len s.down)
  · ext n s
    exact ULift.ext (hj n.unop.len s.down)

private lemma representedFamily_hom_ext {X : Scheme.{u₁}}
    {K : SimplicialObject (FormalCoproduct.{w₁} X.Etale)} {S : SSet.{t₁}}
    {H W : FormalCoproduct.{w₁} X.Etale} {u : SimplicialHomFamily K S H}
    (hu : (simplicialHomFamilyFunctor K S).IsRepresentedBy u) {f g : W ⟶ H}
    (h : ∀ n s, f ≫ u.val n s = g ≫ u.val n s) : f = g := by
  apply hu.map_bijective.injective
  apply Subtype.ext
  exact funext fun n ↦ funext fun s ↦ h n s

private lemma representedFamily_exists {X : Scheme.{u₁}}
    {K : SimplicialObject (FormalCoproduct.{w₁} X.Etale)} {S : SSet.{t₁}}
    {H W : FormalCoproduct.{w₁} X.Etale} {u : SimplicialHomFamily K S H}
    (hu : (simplicialHomFamilyFunctor K S).IsRepresentedBy u) (f : SimplicialHomFamily K S W) :
    ∃ g : W ⟶ H, ∀ n s, g ≫ u.val n s = f.val n s := by
  obtain ⟨g, hg⟩ := hu.map_bijective.surjective f
  refine ⟨g, fun n s ↦ ?_⟩
  exact congrFun (congrFun (congrArg Subtype.val hg) n) s

set_option linter.unusedVariables false in
/-- Hom objects turn admissible simplicial pushouts into pullbacks.
The representing pairs are arbitrary fixed choices from def-weil-pbc-simplicial-hom-object;
the equations specify their unique induced morphisms, without another Hom-object definition.
Source: Stacks Project, Lemma 017N (auxiliary; not a blueprint node).

Proof: (1) Form the fibre product of the two restriction morphisms using
lem-weil-pbc-semi-representable-finite-limits. (2) By the degreewise pushout of
 def-weil-pbc-simplicial-set, D-families over any W are exactly B- and C-families agreeing
on A; the operators preserve the glued family. (3) The representing bijections of
 def-weil-pbc-simplicial-hom-object and def-weil-pbc-representing-object identify this with
pairs of morphisms to HB and HC agreeing in HA. The fibre-product universal property
and Yoneda identify HD with that fibre product, with projections iStar and jStar. -/
theorem simplicialHomObject_pushout_isPullback {X : Scheme.{u₁}}
    {K : SimplicialObject (FormalCoproduct.{w₁} X.Etale)}
    {A B C D : SSet.{t₁}} [A.Finite] [B.Finite] [C.Finite] [D.Finite]
    (hAfin : ∀ n : ℕ, Finite (A.obj (op ⦋n⦌)))
    (hAne : ∀ n : ℕ, Nonempty (A.obj (op ⦋n⦌)))
    (hBfin : ∀ n : ℕ, Finite (B.obj (op ⦋n⦌)))
    (hBne : ∀ n : ℕ, Nonempty (B.obj (op ⦋n⦌)))
    (hCfin : ∀ n : ℕ, Finite (C.obj (op ⦋n⦌)))
    (hCne : ∀ n : ℕ, Nonempty (C.obj (op ⦋n⦌)))
    (hDfin : ∀ n : ℕ, Finite (D.obj (op ⦋n⦌)))
    (hDne : ∀ n : ℕ, Nonempty (D.obj (op ⦋n⦌)))
    (p : A ⟶ B) (q : A ⟶ C) (i : B ⟶ D) (j : C ⟶ D)
    (hpush : CategoryTheory.IsPushout p q i j)
    {HA : FormalCoproduct.{w₁} X.Etale}
    (uA : SimplicialHomFamily K A HA)
    (huA : (simplicialHomFamilyFunctor K A).IsRepresentedBy uA)
    {HB HC HD : FormalCoproduct.{w₁} X.Etale}
    (uB : SimplicialHomFamily K B HB) (uC : SimplicialHomFamily K C HC)
    (uD : SimplicialHomFamily K D HD)
    (huB : (simplicialHomFamilyFunctor K B).IsRepresentedBy uB)
    (huC : (simplicialHomFamilyFunctor K C).IsRepresentedBy uC)
    (huD : (simplicialHomFamilyFunctor K D).IsRepresentedBy uD)
    (iStar : HD ⟶ HB) (jStar : HD ⟶ HC)
    (hi : ∀ n s, iStar ≫ uB.val n s = uD.val n (i.app (op ⦋n⦌) s))
    (hj : ∀ n s, jStar ≫ uC.val n s = uD.val n (j.app (op ⦋n⦌) s))
    (pStar : HB ⟶ HA) (qStar : HC ⟶ HA)
    (hp : ∀ n s, pStar ≫ uA.val n s = uB.val n (p.app (op ⦋n⦌) s))
    (hq : ∀ n s, qStar ≫ uA.val n s = uC.val n (q.app (op ⦋n⦌) s)) :
    CategoryTheory.IsPullback iStar jStar pStar qStar := by
  have hcomm : iStar ≫ pStar = jStar ≫ qStar := by
    apply representedFamily_hom_ext huA
    intro n s
    calc
      (iStar ≫ pStar) ≫ uA.val n s =
          iStar ≫ (pStar ≫ uA.val n s) := Category.assoc _ _ _
      _ = iStar ≫ uB.val n (p.app (op ⦋n⦌) s) := by rw [hp]
      _ = uD.val n (i.app (op ⦋n⦌) (p.app (op ⦋n⦌) s)) := hi _ _
      _ = uD.val n (j.app (op ⦋n⦌) (q.app (op ⦋n⦌) s)) := by
        exact congrArg (fun f ↦ uD.val n (f s)) (congr_app hpush.w (op ⦋n⦌))
      _ = jStar ≫ uC.val n (q.app (op ⦋n⦌) s) := (hj _ _).symm
      _ = jStar ≫ (qStar ≫ uA.val n s) := by rw [hq]
      _ = (jStar ≫ qStar) ≫ uA.val n s := (Category.assoc _ _ _).symm
  refine CategoryTheory.IsPullback.mk' hcomm ?_ ?_
  · intro W f g h₁ h₂
    apply huD.map_bijective.injective
    apply family_pushout_ext hpush
    · intro n s
      change f ≫ uD.val n (i.app (op ⦋n⦌) s) = g ≫ uD.val n (i.app (op ⦋n⦌) s)
      simpa only [Category.assoc, hi] using congrArg (fun a ↦ a ≫ uB.val n s) h₁
    · intro n s
      change f ≫ uD.val n (j.app (op ⦋n⦌) s) = g ≫ uD.val n (j.app (op ⦋n⦌) s)
      simpa only [Category.assoc, hj] using congrArg (fun a ↦ a ≫ uC.val n s) h₂
  · intro W a b hab
    have hagree : ∀ n s, (uB.precomp a).val n (p.app (op ⦋n⦌) s) =
        (uC.precomp b).val n (q.app (op ⦋n⦌) s) := by
      intro n s
      change a ≫ uB.val n (p.app (op ⦋n⦌) s) = b ≫ uC.val n (q.app (op ⦋n⦌) s)
      simpa only [Category.assoc, hp, hq] using congrArg (fun f ↦ f ≫ uA.val n s) hab
    obtain ⟨f, hfB, hfC⟩ := glueFamilies hpush (uB.precomp a) (uC.precomp b) hagree
    obtain ⟨l, hl⟩ := representedFamily_exists huD f
    refine ⟨l, representedFamily_hom_ext huB ?_, representedFamily_hom_ext huC ?_⟩
    · intro n s
      rw [Category.assoc, hi, hl]
      exact hfB n s
    · intro n s
      rw [Category.assoc, hj, hl]
      exact hfC n s

set_option linter.unusedVariables false in
/-- If the common simplicial set is empty, the Hom object of the pushout is a product.
The equations specify the unique induced morphisms of the fixed representing pairs.
Source: Stacks Project, Lemma 017N (auxiliary; not a blueprint node).

Proof: (4) In the family bijection of Lemma 017N, agreement over the empty A is vacuous.
The degreewise pushout is the coproduct, so D-families are arbitrary pairs of B- and
C-families (def-weil-pbc-simplicial-set). Transport this through the representing
bijections (def-weil-pbc-simplicial-hom-object and def-weil-pbc-representing-object).
Finite limits give a product, equivalently a fibre product over the final object
(lem-weil-pbc-semi-representable-finite-limits). Its universal property identifies HD
with that product, with the specified projections iStar and jStar. -/
theorem simplicialHomObject_pushout_empty_isProduct {X : Scheme.{u₁}}
    {K : SimplicialObject (FormalCoproduct.{w₁} X.Etale)}
    {A B C D : SSet.{t₁}} [B.Finite] [C.Finite] [D.Finite]
    (hAempty : ∀ n : ℕ, IsEmpty (A.obj (op ⦋n⦌)))
    (hBfin : ∀ n : ℕ, Finite (B.obj (op ⦋n⦌)))
    (hBne : ∀ n : ℕ, Nonempty (B.obj (op ⦋n⦌)))
    (hCfin : ∀ n : ℕ, Finite (C.obj (op ⦋n⦌)))
    (hCne : ∀ n : ℕ, Nonempty (C.obj (op ⦋n⦌)))
    (hDfin : ∀ n : ℕ, Finite (D.obj (op ⦋n⦌)))
    (hDne : ∀ n : ℕ, Nonempty (D.obj (op ⦋n⦌)))
    (p : A ⟶ B) (q : A ⟶ C) (i : B ⟶ D) (j : C ⟶ D)
    (hpush : CategoryTheory.IsPushout p q i j)
    {HB HC HD : FormalCoproduct.{w₁} X.Etale}
    (uB : SimplicialHomFamily K B HB) (uC : SimplicialHomFamily K C HC)
    (uD : SimplicialHomFamily K D HD)
    (huB : (simplicialHomFamilyFunctor K B).IsRepresentedBy uB)
    (huC : (simplicialHomFamilyFunctor K C).IsRepresentedBy uC)
    (huD : (simplicialHomFamilyFunctor K D).IsRepresentedBy uD)
    (iStar : HD ⟶ HB) (jStar : HD ⟶ HC)
    (hi : ∀ n s, iStar ≫ uB.val n s = uD.val n (i.app (op ⦋n⦌) s))
    (hj : ∀ n s, jStar ≫ uC.val n s = uD.val n (j.app (op ⦋n⦌) s)) :
    Nonempty (IsLimit (BinaryFan.mk iStar jStar)) := by
  have hex : ∀ {W : FormalCoproduct.{w₁} X.Etale} (a : W ⟶ HB) (b : W ⟶ HC),
      ∃ l : W ⟶ HD, l ≫ iStar = a ∧ l ≫ jStar = b := by
    intro W a b
    obtain ⟨f, hfB, hfC⟩ := glueFamilies hpush (uB.precomp a) (uC.precomp b)
      (fun n s ↦ False.elim ((hAempty n).false s))
    obtain ⟨l, hl⟩ := representedFamily_exists huD f
    refine ⟨l, representedFamily_hom_ext huB ?_, representedFamily_hom_ext huC ?_⟩
    · intro n s
      rw [Category.assoc, hi, hl]
      exact hfB n s
    · intro n s
      rw [Category.assoc, hj, hl]
      exact hfC n s
  have hext : ∀ {W : FormalCoproduct.{w₁} X.Etale} {f g : W ⟶ HD},
      f ≫ iStar = g ≫ iStar → f ≫ jStar = g ≫ jStar → f = g := by
    intro W f g h₁ h₂
    apply huD.map_bijective.injective
    apply family_pushout_ext hpush
    · intro n s
      change f ≫ uD.val n (i.app (op ⦋n⦌) s) = g ≫ uD.val n (i.app (op ⦋n⦌) s)
      simpa only [Category.assoc, hi] using congrArg (fun a ↦ a ≫ uB.val n s) h₁
    · intro n s
      change f ≫ uD.val n (j.app (op ⦋n⦌) s) = g ≫ uD.val n (j.app (op ⦋n⦌) s)
      simpa only [Category.assoc, hj] using congrArg (fun a ↦ a ≫ uC.val n s) h₂
  refine ⟨BinaryFan.isLimitMk (fun s ↦ (hex s.fst s.snd).choose)
    (fun s ↦ (hex s.fst s.snd).choose_spec.1)
    (fun s ↦ (hex s.fst s.snd).choose_spec.2) ?_⟩
  intro s m h₁ h₂
  exact hext (h₁.trans (hex s.fst s.snd).choose_spec.1.symm)
    (h₂.trans (hex s.fst s.snd).choose_spec.2.symm)

end AlgebraicGeometry.Scheme
