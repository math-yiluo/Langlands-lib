/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import WeilConjectures.CategoryTheory.Sites.PointSystemSaturation
import WeilConjectures.CategoryTheory.Sites.PointFamilyConservative
import WeilConjectures.TraceFormula.InverseSystemSitePoint
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Finite-cover sites with finite limits have enough points

Source: Stacks Project, Sites, Tag 00YQ, Proposition `proposition-criterion-points`
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private lemma map_eq_of_equalizer_eq
    {D : Type*} [Category D] [HasEqualizers D]
    (T : D ⥤ Type w) [PreservesFiniteLimits T]
    {A B Q : D} (f g : A ⟶ B) (a b : A ⟶ Q)
    (h : equalizer.ι f g ≫ a = equalizer.ι f g ≫ b)
    (x : T.obj A) (hx : T.map f x = T.map g x) :
    T.map a x = T.map b x := by
  have hc := isLimitForkMapOfIsLimit T _ (equalizerIsEqualizer f g)
  obtain ⟨l, hl⟩ := Fork.IsLimit.lift' hc
    (TypeCat.ofHom (fun _ : PUnit ↦ x)) (by ext z; exact hx)
  have hxl : T.map (equalizer.ι f g) (l PUnit.unit) = x :=
    ConcreteCategory.congr_hom hl PUnit.unit
  rw [← hxl]
  simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom (congrArg T.map h) (l PUnit.unit)

private noncomputable def sheafSectionEquiv
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    (F : Sheaf J.toGrothendieck (Type (max u w))) (U : C) :
    (((presheafToSheaf J.toGrothendieck (Type (max u w))).obj
      (uliftYoneda.{max u w}.obj U)) ⟶ F) ≃ F.obj.obj (Opposite.op U) :=
  ((sheafificationAdjunction J.toGrothendieck (Type (max u w))).homEquiv _ F).trans
    uliftYonedaEquiv

private lemma sheafSectionEquiv_symm
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    (F : Sheaf J.toGrothendieck (Type (max u w))) (U : C)
    (s : F.obj.obj (Opposite.op U)) :
    (sheafSectionEquiv J F U).symm s = sectionMorphism J F U s := rfl

private lemma sheafSectionEquiv_comp
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    (F G : Sheaf J.toGrothendieck (Type (max u w))) (U : C)
    (a : ((presheafToSheaf J.toGrothendieck (Type (max u w))).obj
      (uliftYoneda.{max u w}.obj U)) ⟶ F) (b : F ⟶ G) :
    sheafSectionEquiv J G U (a ≫ b) =
      b.hom.app (Opposite.op U) (sheafSectionEquiv J F U a) := by
  unfold sheafSectionEquiv
  simp only [Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
  rfl

private lemma sheafifiedRepresentables_separating
    {C : Type u} [SmallCategory C] (J : Precoverage C) :
    ObjectProperty.IsSeparating (.ofObj (fun U : C ↦
      (presheafToSheaf J.toGrothendieck (Type (max u w))).obj
        (uliftYoneda.{max u w}.obj U))) := by
  intro F G a b h
  ext U s
  have hh := h _ ⟨U.unop⟩ (sectionMorphism J F U.unop s)
  have he := congrArg (sheafSectionEquiv J G U.unop) hh
  rw [sheafSectionEquiv_comp, sheafSectionEquiv_comp] at he
  simpa only [← sheafSectionEquiv_symm, Equiv.apply_symm_apply,
    Opposite.op_unop, TypeCat.Fun.toFun_apply] using he

private theorem small_family_of_section_separation
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    (hsep : ∀ (F : Sheaf J.toGrothendieck (Type (max u w))) (U : C)
      (s s' : F.obj.obj (Opposite.op U)), s ≠ s' →
      ∃ (p : GeometricMorphism (Type (max u w))
        (Sheaf J.toGrothendieck (Type (max u w))))
        (x : p.inverse.obj ((presheafToSheaf J.toGrothendieck (Type (max u w))).obj
          (uliftYoneda.{max u w}.obj U))),
        pointSectionImage J p F U x s ≠ pointSectionImage J p F U x s') :
    ∃ (ι : Type (max u w))
      (p : ι → GeometricMorphism (Type (max u w))
        (Sheaf J.toGrothendieck (Type (max u w)))),
      ∀ {F G : Sheaf J.toGrothendieck (Type (max u w))} (a : F ⟶ G),
        (∀ i, Function.Bijective ((p i).inverse.map a)) → IsIso a := by
  classical
  let A (U : C) := (presheafToSheaf J.toGrothendieck (Type (max u w))).obj
    (uliftYoneda.{max u w}.obj U)
  have hA : ObjectProperty.IsSeparating (.ofObj A) :=
    sheafifiedRepresentables_separating J
  have : WellPowered.{max u w} (Sheaf J.toGrothendieck (Type (max u w))) :=
    wellPowered_of_isDetecting.{max u w} hA.isDetecting
  let D := Σ U : C, Shrink.{max u w} (Subobject (A U))
  let sub (i : D) : Subobject (A i.1) := (equivShrink.{max u w} _).symm i.2
  let Q (i : D) := pushout (sub i).arrow (sub i).arrow
  let a (i : D) : A i.1 ⟶ Q i := pushout.inl _ _
  let b (i : D) : A i.1 ⟶ Q i := pushout.inr _ _
  let s (i : D) := sheafSectionEquiv J (Q i) i.1 (a i)
  let t (i : D) := sheafSectionEquiv J (Q i) i.1 (b i)
  let ι := {i : D // s i ≠ t i}
  choose p x hp using fun i : ι ↦ hsep (Q i.1) i.1.1 (s i.1) (t i.1) i.2
  refine ⟨ι, p, ?_⟩
  have hc := point_family_conservative.{u, u, w, max u w} J ι p ?_
  · intro F G f hf
    have (i : ι) : IsIso ((p i).inverse.map f) :=
      (CategoryTheory.isIso_iff_bijective _).2 (hf i)
    exact hc.isIso f
  intro F U z z' hzz
  let f := sectionMorphism J F U z
  let g := sectionMorphism J F U z'
  let E := equalizerSubobject f g
  let d : D := ⟨U, equivShrink.{max u w} (Subobject (A U)) E⟩
  have hd : sub d = E := (equivShrink.{max u w} _).symm_apply_apply E
  have hw : (sub d).arrow ≫ f = (sub d).arrow ≫ g := by
    rw [hd]
    exact equalizerSubobject_arrow_comp f g
  let l : Q d ⟶ F := pushout.desc f g hw
  have hst : s d ≠ t d := by
    intro h
    have hh := congrArg (fun q ↦ l.hom.app (Opposite.op U) q) h
    change l.hom.app (Opposite.op U) (sheafSectionEquiv J (Q d) U (a d)) =
      l.hom.app (Opposite.op U) (sheafSectionEquiv J (Q d) U (b d)) at hh
    rw [← sheafSectionEquiv_comp, ← sheafSectionEquiv_comp] at hh
    have h₁ : a d ≫ l = f := pushout.inl_desc _ _ _
    have h₂ : b d ≫ l = g := pushout.inr_desc _ _ _
    rw [h₁, h₂] at hh
    apply hzz
    simpa only [f, g, ← sheafSectionEquiv_symm, Equiv.apply_symm_apply] using hh
  let i : ι := ⟨d, hst⟩
  refine ⟨i, x i, ?_⟩
  intro he
  apply hp i
  change (p i).inverse.map (sectionMorphism J (Q d) U (s d)) (x i) =
    (p i).inverse.map (sectionMorphism J (Q d) U (t d)) (x i)
  have h₁ : sectionMorphism J (Q d) U (s d) = a d :=
    (sheafSectionEquiv J (Q d) U).symm_apply_apply (a d)
  have h₂ : sectionMorphism J (Q d) U (t d) = b d :=
    (sheafSectionEquiv J (Q d) U).symm_apply_apply (b d)
  rw [h₁, h₂]
  have := (p i).leftExact
  refine map_eq_of_equalizer_eq (p i).inverse f g (a d) (b d) ?_ (x i) he
  have hh : E.arrow ≫ a d = E.arrow ≫ b d := by
    rw [← hd]
    exact pushout.condition
  rw [← equalizerSubobject_arrow' f g]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ (equalizerSubobjectIso f g).inv ≫ k) hh

private noncomputable def systemHomIso
    {C : Type u} [SmallCategory C] {I : Type u} [PartialOrder I]
    (U : I ⥤ Cᵒᵖ) (X : C) :
    (inverseSystemHomFunctor U.leftOp).obj X ≅
      colimit (U ⋙ uliftYoneda.{u}.obj X) :=
  colimitObjIsoColimitCompEvaluation (inverseSystemRepresentableDiagram U.leftOp) X ≪≫
    HasColimit.isoOfNatIso (NatIso.ofComponents (fun _ ↦ Equiv.ulift.symm.toIso)
      (by intros; ext z; rfl))

private lemma systemHomIso_ι
    {C : Type u} [SmallCategory C] {I : Type u} [PartialOrder I]
    (U : I ⥤ Cᵒᵖ) (X : C) (i : I) (f : (U.obj i).unop ⟶ X) :
    (systemHomIso U X).hom
      ((colimit.ι (inverseSystemRepresentableDiagram U.leftOp) i).app X f) =
        colimit.ι (U ⋙ uliftYoneda.{u}.obj X) i (ULift.up f) := by
  change (((colimit.ι (inverseSystemRepresentableDiagram U.leftOp) i).app X) ≫
    (systemHomIso U X).hom) f = _
  simp [systemHomIso, HasColimit.ι_isoOfNatIso_hom]
  rfl

private lemma systemHomIso_naturality
    {C : Type u} [SmallCategory C] {I : Type u} [PartialOrder I]
    (U : I ⥤ Cᵒᵖ) {X Y : C} (f : X ⟶ Y) :
    (inverseSystemHomFunctor U.leftOp).map f ≫ (systemHomIso U Y).hom =
      (systemHomIso U X).hom ≫
        colimMap (U.whiskerLeft (uliftYoneda.map f)) := by
  apply (cancel_epi
    (colimitObjIsoColimitCompEvaluation (inverseSystemRepresentableDiagram U.leftOp) X).inv).1
  apply colimit.hom_ext
  intro i
  simp only [← Category.assoc, colimitObjIsoColimitCompEvaluation_ι_inv]
  ext z
  have hn := ConcreteCategory.congr_hom
    ((colimit.ι (inverseSystemRepresentableDiagram U.leftOp) i).naturality f).symm z
  change (inverseSystemHomFunctor U.leftOp).map f
    ((colimit.ι (inverseSystemRepresentableDiagram U.leftOp) i).app X z) =
      (colimit.ι (inverseSystemRepresentableDiagram U.leftOp) i).app Y (z ≫ f) at hn
  change (systemHomIso U Y).hom
    ((inverseSystemHomFunctor U.leftOp).map f
      ((colimit.ι (inverseSystemRepresentableDiagram U.leftOp) i).app X z)) =
    colimMap (U.whiskerLeft (uliftYoneda.map f))
      ((systemHomIso U X).hom
        ((colimit.ι (inverseSystemRepresentableDiagram U.leftOp) i).app X z))
  rw [hn, systemHomIso_ι, systemHomIso_ι]
  rw [← ConcreteCategory.comp_apply, ι_colimMap]
  rfl

/-- A small site with finite limits and finite covering refinements has a
set-indexed conservative family of points. Source: Stacks Project, Sites, Tag 00YQ
(auxiliary; not a blueprint node).

The sheaves take values in `Type (max u w)`, a universe containing the site's
universe `u`: in the source the site is a set and its sheaves are valued in all sets
(size convention, prose-01-10). With values in a universe below `u` the
conclusion fails, e.g. for presheaves on a meet-semilattice with an antichain of
size larger than the value universe.

The proof follows the node. Step 1: fix a sheaf `F`, an object `U` and distinct
sections `s ≠ s'` of `F(U)`; starting from the one-element system at `U`, apply the
all-at-once refinement (Stacks 00YP) countably often and take the union of the
chain; the images of `s, s'` stay distinct (equality in a directed colimit is
witnessed at one index), and every element of the final `u(W)` lifts along every
finite covering `{W_k → W}`. Step 2: by the finite-refinement hypothesis the
lifting holds for every covering, and finite limits in `C` make `u` left exact, so
the system defines a point (Stacks 00YC, 00YA) in whose stalk `s, s'` stay
distinct. Step 3: the point depends only on the inverse system in `C`, and the
systems produced have index posets bounded in size in terms of `C`, so up to
isomorphism they form a set in universe `u`; one point for each of them gives the
index type `ι`, and since every distinct pair of sections is separated by one of
these points, the point-family criterion (Stacks 00YM) gives joint reflection of
isomorphisms.
-/
theorem finitarySite_enoughPoints
    {C : Type u} [SmallCategory C] [HasFiniteLimits C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (hfinite : ∀ (X : C) (I : Type (max u v)) (U : I → C)
      (f : ∀ i, U i ⟶ X),
      Presieve.ofArrows U f ∈ J X →
        ∃ (K : Type (max u v)) (_ : Finite K) (V : K → C) (g : ∀ k, V k ⟶ X)
          (r : K → I),
          Presieve.ofArrows V g ∈ J X ∧
            ∀ k, ∃ (q : V k ⟶ U (r k)), q ≫ f (r k) = g k) :
    ∃ (ι : Type (max u w))
      (p : ι → GeometricMorphism (Type (max u w))
        (Sheaf J.toGrothendieck (Type (max u w)))),
      ∀ {F G : Sheaf J.toGrothendieck (Type (max u w))} (a : F ⟶ G),
        (∀ i, Function.Bijective ((p i).inverse.map a)) → IsIso a := by
  classical
  -- Select the family through small subobject sets of sheafified representables.
  apply small_family_of_section_separation J
  intro F W s s' hne
  obtain ⟨I, po, ne, di, U, i, a, hd, hl⟩ :=
    exists_pointSystem_finiteCoverLifting J hJ F W s s' hne
  let H := inverseSystemHomFunctor U.leftOp
  have hfin (n : ℕ) (X : C) (V : Fin n → C) (f : ∀ k, V k ⟶ X)
      (hc : Presieve.ofArrows V f ∈ J X) (x : H.obj X) :
      ∃ (k : Fin n) (y : H.obj (V k)), H.map (f k) y = x := by
    obtain ⟨k, y, hy⟩ := hl n X V f hc ((systemHomIso U X).hom x)
    refine ⟨k, (systemHomIso U (V k)).inv y, ?_⟩
    apply injective_of_mono (systemHomIso U X).hom
    have hn := ConcreteCategory.congr_hom (systemHomIso_naturality U (f k))
      ((systemHomIso U (V k)).inv y)
    refine hn.trans ?_
    simpa only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] using hy
  have hcover {K : Type u} {X : C} (V : K → C) (f : ∀ k, V k ⟶ X)
      (hc : Presieve.ofArrows V f ∈ J X) (x : H.obj X) :
      ∃ (k : K) (y : H.obj (V k)), H.map (f k) y = x := by
    have hc' : Presieve.ofArrows (fun k : ULift.{v} K ↦ V k.down)
        (fun k ↦ f k.down) ∈ J X := by
      change Presieve.ofArrows (V ∘ ULift.down) (fun k : ULift.{v} K ↦ f k.down) ∈ J X
      rwa [Presieve.ofArrows_comp_eq_of_surjective f
        (show Function.Surjective (ULift.down : ULift.{v} K → K) from
          fun k ↦ ⟨ULift.up k, rfl⟩)]
    obtain ⟨L, fl, B, g, r, hg, hr⟩ := hfinite X (ULift.{v} K) _ _ hc'
    let := Fintype.ofFinite L
    let e := (Fintype.equivFin L).symm
    have hg' : Presieve.ofArrows (fun j ↦ B (e j)) (fun j ↦ g (e j)) ∈ J X := by
      change Presieve.ofArrows (B ∘ e) (fun j ↦ g (e j)) ∈ J X
      rwa [Presieve.ofArrows_comp_eq_of_surjective g e.surjective]
    obtain ⟨k, y, hy⟩ := hfin (Fintype.card L) X _ _ hg' x
    obtain ⟨q, hq⟩ := hr (e k)
    refine ⟨(r (e k)).down, H.map q y, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← H.map_comp, hq]
    exact hy
  obtain ⟨_, _, p, ⟨e⟩⟩ := inverseSystemSitePoint.{w} J U.leftOp hcover
  let A := (presheafToSheaf J.toGrothendieck (Type (max u w))).obj
    (uliftYoneda.{max u w}.obj W)
  let η := toSheafify J.toGrothendieck (uliftYoneda.{max u w}.obj W)
  let t : (inverseSystemSectionColimitFunctor.{w} J.toGrothendieck U.leftOp).obj A :=
    colimit.ι (U ⋙ A.obj) i (η.app (U.obj i) (ULift.up a))
  let x := e.inv.app A t
  refine ⟨p, x, ?_⟩
  have ht (z : F.obj.obj (Opposite.op W)) :
      (inverseSystemSectionColimitFunctor.{w} J.toGrothendieck U.leftOp).map
        (sectionMorphism J F W z) t =
      colimit.ι (U ⋙ F.obj) i (F.obj.map a.op z) := by
    change colimMap (U.whiskerLeft (sectionMorphism J F W z).hom)
      (colimit.ι (U ⋙ A.obj) i (η.app (U.obj i) (ULift.up a))) = _
    rw [← ConcreteCategory.comp_apply, ι_colimMap, ConcreteCategory.comp_apply]
    congr 1
    have hh : η ≫ (sectionMorphism J F W z).hom = uliftYonedaEquiv.symm z :=
      toSheafify_sheafifyLift J.toGrothendieck
        (P := uliftYoneda.{max u w}.obj W) (Q := F.obj)
        (uliftYonedaEquiv.symm z) F.property
    let c : (uliftYoneda.{max u w}.obj W).obj (U.obj i) := ULift.up a
    exact ConcreteCategory.congr_hom (congr_app hh (U.obj i)) c
  intro he
  apply hd
  have hh := congrArg (fun z ↦ e.hom.app F z) he
  have hn (z : F.obj.obj (Opposite.op W)) :
      e.hom.app F (pointSectionImage J p F W x z) =
        (inverseSystemSectionColimitFunctor.{w} J.toGrothendieck U.leftOp).map
          (sectionMorphism J F W z) t := by
    have hh := ConcreteCategory.congr_hom (e.hom.naturality (sectionMorphism J F W z)) x
    change e.hom.app F (pointSectionImage J p F W x z) =
      (inverseSystemSectionColimitFunctor.{w} J.toGrothendieck U.leftOp).map
        (sectionMorphism J F W z) (e.hom.app A x) at hh
    have hx : e.hom.app A x = t := by
      change (e.inv.app A ≫ e.hom.app A) t = t
      simp
    rw [hx] at hh
    exact hh
  rw [hn s, hn s', ht s, ht s'] at hh
  exact hh

end CategoryTheory
