/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import WeilConjectures.CategoryTheory.SiteSystemStrictificationObstruction
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Refutation of the finite-precoverage strictification interface

Source: Mathlib's indexed `Precoverage.IsStableUnderBaseChange` axiom and the
strictification interface sourced from Stacks Project, Categories, Tag 004A.
(blueprint: lem-weil-pbc-site-system-strictification-refuted).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private abbrev StrictificationPoint := Codiscrete PUnit

private instance : Subsingleton StrictificationPoint :=
  ⟨by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩; rfl⟩

private instance : Finite StrictificationPoint := Finite.of_equiv PUnit codiscreteEquiv.symm

private instance (X Y : StrictificationPoint) (f : X ⟶ Y) : IsIso f := by
  change IsIso (Codiscrete.iso X Y).hom
  infer_instance

private instance (X Y Z : StrictificationPoint) (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPullback f g :=
  (IsPullback.of_vert_isIso (fst := 𝟙 X) (snd := (Codiscrete.iso X Y).hom)
    (f := f) (g := g) ⟨Subsingleton.elim _ _⟩).hasPullback

private instance : HasPullbacks StrictificationPoint :=
  hasPullbacks_of_hasLimit_cospan StrictificationPoint

private instance : (⊤ : Precoverage StrictificationPoint).HasIsos :=
  ⟨fun _ ↦ trivial⟩

private instance : (⊤ : Precoverage StrictificationPoint).IsStableUnderComposition := by
  constructor
  intros
  trivial

private instance : (⊤ : Precoverage StrictificationPoint).IsStableUnderBaseChange := by
  constructor
  intros
  trivial

private theorem strictification_identity_comparison
    {A B : StrictificationPoint ⥤ StrictificationPoint} (h : A = B) :
    HEq (eqToIso h) (Iso.refl B) := by
  cases h
  rfl

private theorem strictification_preserves_pullback
    {X Y Z : StrictificationPoint} (f : X ⟶ Z) (g : Y ⟶ Z) :
    PreservesLimit (cospan f g) (𝟭 StrictificationPoint) := by infer_instance

set_option linter.style.haveILetI false in
set_option linter.unusedVariables false in
/-- Source: Mathlib `Precoverage.IsStableUnderBaseChange`, applied to the finite-site
strictification interface sourced from Stacks Project, Categories, Tag 004A.
(blueprint: lem-weil-pbc-site-system-strictification-refuted).

Proof: specialize the interface to I = WithTop Nat and the constant one-object
category, with the top precoverage. Every presieve there has at most one arrow,
so all its coverings are finite; all site axioms and pullback hypotheses hold.
Take every U to be the identity, with equality comparisons. Identity sheaf
pullbacks preserve finite limits and colimits. Let D be the codiscrete category
on I and let v_i be constant at i. The unique natural isomorphisms into a
codiscrete category give delta and satisfy its normalization and cocycle.
The asserted conclusion supplies F, Q, e and v' with the two strict coefficient
equalities. Apply site_system_strictification_obstruction: all transition images
at the largest index have distinct coefficient labels but are isomorphic, so
indexed base change makes an infinite covering. This contradicts finiteness.
The displayed negated proposition is the strictification signature at universe zero;
no assumptions of that signature are dropped in constructing the example. -/
theorem site_system_strictification_data_refuted : ¬ (∀
    (I : Type 0) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (C : I → Cat.{0, 0}) (P : ∀ i : I, Precoverage (C i))
    [∀ i, (P i).HasIsos] [∀ i, (P i).IsStableUnderComposition]
    [∀ i, (P i).IsStableUnderBaseChange] [∀ i, (P i).HasPullbacks]
    (hfinite : ∀ (i : I) (X : C i) (R : Presieve X), R ∈ P i X → Finite R.uncurry)
    (U : ∀ (i j : I), i ≤ j → C i ⥤ C j)
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
      U i j h ⋙ U j k h' ≅ U i k (h.trans h'))
    (hgammaLeft : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
    (hgammaRight : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i k k h le_rfl) (Iso.refl (U i k h)))
    (hgamma : ∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (X : C i),
      (gamma j k l h' h'').hom.app ((U i j h).obj X) ≫
          (gamma i j l h (h'.trans h'')).hom.app X =
        (U k l h'').map ((gamma i j k h h').hom.app X) ≫
          (gamma i k l (h.trans h') h'').hom.app X)
    (hcover : ∀ (i j : I) (h : i ≤ j) (X : C i) (R : Presieve X),
      R ∈ P i X → R.map (U i j h) ∈ P j ((U i j h).obj X))
    (hpullback : ∀ (i j : I) (h : i ≤ j) (X Y Z : C i) (R : Presieve X),
      R ∈ P i X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (U i j h))
    [∀ (i j : I) (h : i ≤ j), (U i j h).IsContinuous
      (P i).toGrothendieck (P j).toGrothendieck]
    [∀ (i j : I) (h : i ≤ j), PreservesFiniteLimits
      (sheafPullback (U i j h) (Type 0) (P i).toGrothendieck (P j).toGrothendieck)]
    [∀ (i j : I) (h : i ≤ j), PreservesFiniteColimits
      (sheafPullback (U i j h) (Type 0) (P i).toGrothendieck (P j).toGrothendieck)]
    (D : Type 0) [Category.{0} D] (v : ∀ i : I, C i ⥤ D)
    (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i)
    (hdeltaId : ∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i)))
    (hdelta : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k) (X : C i),
      (v k).map ((gamma i j k h h').hom.app X) ≫
          (delta i k (h.trans h')).hom.app X =
        (delta j k h').hom.app ((U i j h).obj X) ≫ (delta i j h).hom.app X)
    ,
    ∃ (F : I ⥤ Cat.{0, 0}) (Q : ∀ i : I, Precoverage (F.obj i))
      (e : ∀ i : I, C i ⥤ F.obj i),
      (∀ i : I, (e i).IsEquivalence) ∧
      (∃ (_ : ∀ i, (Q i).HasIsos) (_ : ∀ i, (Q i).IsStableUnderComposition)
        (_ : ∀ i, (Q i).IsStableUnderBaseChange) (_ : ∀ i, (Q i).HasPullbacks),
        (∀ (i : I) (X : F.obj i) (R : Presieve X), R ∈ Q i X → Finite R.uncurry) ∧
        (∀ (i : I) (X : C i) (R : Presieve X),
          R ∈ P i X ↔ R.map (e i) ∈ Q i ((e i).obj X)) ∧
        (∀ (i : I) (X : F.obj i) (K : Type 0) (A : K → F.obj i)
          (f : ∀ a : K, A a ⟶ X), Presieve.ofArrows A f ∈ Q i X →
          ∃ (Y : C i) (B : K → C i) (g : ∀ a : K, B a ⟶ Y)
            (t : (e i).obj Y ≅ X) (s : ∀ a : K, (e i).obj (B a) ≅ A a),
            Presieve.ofArrows B g ∈ P i Y ∧
              ∀ a : K, (e i).map (g a) ≫ t.hom = (s a).hom ≫ f a) ∧
        (∀ (i j : I) (h : i ≤ j) (X : F.obj i) (R : Presieve X), R ∈ Q i X →
          R.map (F.map (homOfLE h)).toFunctor ∈
            Q j ((F.map (homOfLE h)).toFunctor.obj X)) ∧
        (∀ (i j : I) (h : i ≤ j) (X Y Z : F.obj i) (R : Presieve X), R ∈ Q i X →
          ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
            PreservesLimit (cospan f g) (F.map (homOfLE h)).toFunctor) ∧
        ∃ (_ : ∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor.IsContinuous
            (Q i).toGrothendieck (Q j).toGrothendieck),
          (∀ (i j : I) (h : i ≤ j), Nonempty (PreservesFiniteLimits
            (sheafPullback (F.map (homOfLE h)).toFunctor (Type 0)
              (Q i).toGrothendieck (Q j).toGrothendieck))) ∧
          (∀ (i j : I) (h : i ≤ j), Nonempty (PreservesFiniteColimits
            (sheafPullback (F.map (homOfLE h)).toFunctor (Type 0)
              (Q i).toGrothendieck (Q j).toGrothendieck))) ∧
          ∃ (theta : ∀ (i j : I) (h : i ≤ j),
              e i ⋙ (F.map (homOfLE h)).toFunctor ≅ U i j h ⋙ e j)
            (v' : ∀ i : I, F.obj i ⥤ D),
            (∀ (i j : I) (h : i ≤ j), (F.map (homOfLE h)).toFunctor ⋙ v' j = v' i) ∧
            (∀ i : I, e i ⋙ v' i = v i) ∧
            (∀ (i j : I) (h : i ≤ j) (X : C i),
              Arrow.mk ((v' j).map ((theta i j h).hom.app X)) =
                Arrow.mk ((delta i j h).inv.app X)))) := by
  intro h
  let I := WithTop ℕ
  have : Infinite I := Infinite.of_injective (fun n : ℕ ↦ (n : I)) WithTop.coe_injective
  let C : I → Cat.{0, 0} := fun _ ↦ Cat.of StrictificationPoint
  let P : ∀ i : I, Precoverage (C i) := fun _ ↦ ⊤
  let U (i j : I) (_ : i ≤ j) : C i ⥤ C j := 𝟭 StrictificationPoint
  let gamma (i j k : I) (h : i ≤ j) (h' : j ≤ k) :
      U i j h ⋙ U j k h' ≅ U i k (h.trans h') := eqToIso (Functor.id_comp _)
  let v (i : I) : C i ⥤ Codiscrete I := Codiscrete.functor (fun _ ↦ i)
  let delta (i j : I) (h : i ≤ j) : U i j h ⋙ v j ≅ v i := Codiscrete.natIso
  have hgammaId (i j k : I) (h : i ≤ j) (h' : j ≤ k) :
      HEq (gamma i j k h h') (Iso.refl (U i k (h.trans h'))) :=
    strictification_identity_comparison _
  have hdeltaId (i : I) : HEq (delta i i le_rfl) (Iso.refl (v i)) := by
    dsimp only [delta, U]
    simp only [heq_eq_eq]
    apply Iso.ext
    ext
    exact Subsingleton.elim _ _
  have hfinite (i : I) (X : C i) (R : Presieve X) : R ∈ P i X → Finite R.uncurry := by
    intro _
    change Finite {f : Σ Y : StrictificationPoint, Unit | R f.2}
    infer_instance
  have hcol : PreservesFiniteColimits (sheafPullback (𝟭 StrictificationPoint) (Type 0)
      (⊤ : Precoverage StrictificationPoint).toGrothendieck
      (⊤ : Precoverage StrictificationPoint).toGrothendieck) := by
    have : PreservesColimits (Functor.sheafPullback (𝟭 StrictificationPoint) (Type 0)
        (⊤ : Precoverage StrictificationPoint).toGrothendieck
        (⊤ : Precoverage StrictificationPoint).toGrothendieck) :=
      (Functor.sheafAdjunctionContinuous (𝟭 StrictificationPoint) (Type 0)
        (⊤ : Precoverage StrictificationPoint).toGrothendieck
        (⊤ : Precoverage StrictificationPoint).toGrothendieck).leftAdjoint_preservesColimits
    exact preservesFiniteColimits_of_natIso (sheafPullbackIso (𝟭 StrictificationPoint)
      (Type 0) (⊤ : Precoverage StrictificationPoint).toGrothendieck
      (⊤ : Precoverage StrictificationPoint).toGrothendieck)
  letI hIsos : ∀ i, (P i).HasIsos := fun _ ↦
    inferInstanceAs (⊤ : Precoverage StrictificationPoint).HasIsos
  letI hComp : ∀ i, (P i).IsStableUnderComposition := fun _ ↦
    inferInstanceAs (⊤ : Precoverage StrictificationPoint).IsStableUnderComposition
  letI hBase : ∀ i, (P i).IsStableUnderBaseChange := fun _ ↦
    inferInstanceAs (⊤ : Precoverage StrictificationPoint).IsStableUnderBaseChange
  letI hPull : ∀ i, (P i).HasPullbacks := fun _ ↦
    inferInstanceAs (⊤ : Precoverage StrictificationPoint).HasPullbacks
  letI hCont : ∀ (i j : I) (h : i ≤ j), (U i j h).IsContinuous
      (P i).toGrothendieck (P j).toGrothendieck := fun _ _ _ ↦
    inferInstanceAs ((𝟭 StrictificationPoint).IsContinuous
      (⊤ : Precoverage StrictificationPoint).toGrothendieck
      (⊤ : Precoverage StrictificationPoint).toGrothendieck)
  letI hLim : ∀ (i j : I) (h : i ≤ j), PreservesFiniteLimits
      (sheafPullback (U i j h) (Type 0) (P i).toGrothendieck (P j).toGrothendieck) :=
    fun _ _ _ ↦ inferInstanceAs (PreservesFiniteLimits
      (sheafPullback (𝟭 StrictificationPoint) (Type 0)
        (⊤ : Precoverage StrictificationPoint).toGrothendieck
        (⊤ : Precoverage StrictificationPoint).toGrothendieck))
  letI hCol : ∀ (i j : I) (h : i ≤ j), PreservesFiniteColimits
      (sheafPullback (U i j h) (Type 0) (P i).toGrothendieck (P j).toGrothendieck) :=
    fun _ _ _ ↦ hcol
  obtain ⟨F, Q, e, he, hQ⟩ := @h I inferInstance inferInstance inferInstance C P
    hIsos hComp hBase hPull hfinite U (fun _ ↦ rfl) gamma
    (fun i k h ↦ hgammaId i i k le_rfl h) (fun i k h ↦ hgammaId i k k h le_rfl)
    (by intros; exact Unit.ext _ _)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ f g _ ↦ strictification_preserves_pullback f g)
    hCont hLim hCol (Codiscrete I) inferInstance v delta hdeltaId
    (fun _ _ _ _ _ _ ↦ Subsingleton.elim _ _)
  obtain ⟨hiso, _, hbase, _, hfin, _, _, _, _, hcont, _, _, theta, v', hstrict,
    hretract, _⟩ := hQ
  letI := hiso
  letI := hbase
  letI := he
  exact site_system_strictification_obstruction I StrictificationPoint ⟨⟨⟩⟩
    F Q hfin e v' hstrict hretract

end CategoryTheory
