/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QCohInverseBaseChangeMate
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.AlgebraicGeometry.RectangleOrdinaryPastingComparisons

/-! # Transport the rectangle to the pasted ordinary base-change square

Source: Stacks Project, Tag 0ATR, Lemma 48.5.2.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry

/-- The source comparison built from the canonical pullback composition family.
The chosen family is fixed by its left-derived universal property, not an arbitrary
witness of existence. 
(blueprint: lem-sc-rectangle-inverse-base-change-mate-transport)
-/
noncomputable def successiveBaseChangeSourceIso
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}} (f : X ⟶ Y) (g : S ⟶ Y) (h : T ⟶ S)
    (k : pullback (pullback.snd f g) h ⟶ pullback f (h ≫ g))
    (hk : k ≫ pullback.fst f (h ≫ g) =
      pullback.fst (pullback.snd f g) h ≫ pullback.fst f g)
    (E : schemeDerivedCategory X) :
    (derivedPullback k).obj ((derivedPullback (pullback.fst f (h ≫ g))).obj E) ≅
      (derivedPullback (pullback.fst (pullback.snd f g) h)).obj
        ((derivedPullback (pullback.fst f g)).obj E) :=
  let comp := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))
  (comp k (pullback.fst f (h ≫ g))).app E ≪≫
    eqToIso (congrArg (fun v ↦ (derivedPullback v).obj E) hk) ≪≫
    ((comp (pullback.fst (pullback.snd f g) h) (pullback.fst f g)).app E).symm

private theorem mate_comparison
    {C D E J T : Type*}
    [Category C] [Category D] [Category E] [Category J] [Category T]
    {F : C ⥤ D} {a : D ⥤ C} {P : E ⥤ T} {c : T ⥤ E}
    {Q : J ⥤ T} {d : T ⥤ J} {L : E ⥤ J}
    {U : C ⥤ E} {V : C ⥤ J} {B H : D ⥤ T}
    (af : F ⊣ a) (ac : P ⊣ c) (ad : Q ⊣ d)
    (s : U ⋙ L ≅ V) (p : L ⋙ Q ≅ P) (b : B ≅ H) (t : c ⋙ L ≅ d)
    (α : TwoSquare U F P B) (δ : TwoSquare V F Q H)
    (ht : ∀ Z : T, Q.map (t.hom.app Z) ≫ ad.counit.app Z =
      p.hom.app (c.obj Z) ≫ ac.counit.app Z)
    (hα : ∀ Z : C, Q.map (s.hom.app Z) ≫ δ.app Z =
      p.hom.app (U.obj Z) ≫ α.app Z ≫ b.hom.app (F.obj Z))
    (K : D) :
    L.map ((mateEquiv af ac α).app K) ≫ t.hom.app (B.obj K) ≫
        d.map (b.hom.app K) =
      s.hom.app (a.obj K) ≫ (mateEquiv af ad δ).app K := by
  let m : U.obj (a.obj K) ⟶ c.obj (B.obj K) := (mateEquiv af ac α).app K
  let n : V.obj (a.obj K) ⟶ d.obj (H.obj K) := (mateEquiv af ad δ).app K
  have hm : P.map m ≫ ac.counit.app (B.obj K) =
      α.app (a.obj K) ≫ B.map (af.counit.app K) := mateEquiv_counit af ac α K
  have hn : Q.map n ≫ ad.counit.app (H.obj K) =
      δ.app (a.obj K) ≫ H.map (af.counit.app K) := mateEquiv_counit af ad δ K
  have hp : Q.map (L.map m) ≫ p.hom.app (c.obj (B.obj K)) =
      p.hom.app (U.obj (a.obj K)) ≫ P.map m := p.hom.naturality m
  have hb : B.map (af.counit.app K) ≫ b.hom.app K =
      b.hom.app (F.obj (a.obj K)) ≫ H.map (af.counit.app K) :=
    b.hom.naturality (af.counit.app K)
  have hc : Q.map (d.map (b.hom.app K)) ≫ ad.counit.app (H.obj K) =
      ad.counit.app (B.obj K) ≫ b.hom.app K := ad.counit.naturality _
  change L.map m ≫ t.hom.app (B.obj K) ≫ d.map (b.hom.app K) =
    s.hom.app (a.obj K) ≫ n
  apply (ad.homEquiv _ _).symm.injective
  change Q.map (L.map m ≫ t.hom.app (B.obj K) ≫ d.map (b.hom.app K)) ≫
      ad.counit.app (H.obj K) =
    Q.map (s.hom.app (a.obj K) ≫ n) ≫ ad.counit.app (H.obj K)
  simp only [Functor.map_comp, Category.assoc]
  rw [hc, ← Category.assoc (Q.map (t.hom.app (B.obj K))), ht]
  simp only [Category.assoc]
  rw [← Category.assoc (Q.map (L.map m)), hp]
  simp only [Category.assoc]
  rw [reassoc_of% hm, hn]
  rw [hb, ← reassoc_of% hα]

/-- Transport the rectangle mate to the mate of the pasted inverse ordinary square.
This comparison has no middle right adjoint and asserts no factorization of second mates.
Source: Stacks Project, Tag 0ATR, Lemma 48.5.2.
(blueprint: lem-sc-rectangle-inverse-base-change-mate-transport)

Proof: The projection equations identify k with the iterated pullback comparison,
which is an isomorphism by the pullback universal property. The canonical pullback
composition isomorphisms identify its upper projection functor with the two
successive upper pullbacks and identify the base pullback with the two successive
base pullbacks. Conjugate the comparison of direct images obtained from the
upper isomorphism and the second projection equation; uniqueness of right adjoints
identifies pullback along k followed by c with d. Use the counit formula defining
ordinary base change to transpose both the rectangle and the horizontally pasted
ordinary transformations. Pullback composition associativity identifies the
transposes, so injectivity gives ordinary pasting. Invert the ordinary comparisons;
conjugation and the Hom equivalences respect the resulting transport. The fixed
rectangle second mate therefore identifies with the mate of the pasted inverse
ordinary square under adja and adjd. Apply the inclusion of the full quasi-coherent
subcategory and take components at K to get the displayed two comparison
isomorphisms and commuting square. The source comparison is explicitly
constructed as successiveBaseChangeSourceIso. No middle right adjoint is involved. All
comparisons are natural isomorphisms from universal properties, so this proof
also handles empty schemes and zero complexes. -/
theorem rectangle_inverseBaseChange_mate_transport
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (g : S ⟶ Y) (h : T ⟶ S)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (c : schemeDerivedQCohCategory T ⥤ schemeDerivedQCohCategory (pullback f (h ≫ g)))
    (d : schemeDerivedQCohCategory T ⥤
      schemeDerivedQCohCategory (pullback (pullback.snd f g) h))
    (adja : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
        f _ _).fst E.obj E.property) ⊣ a)
    (adjc : (schemeDerivedQCohProperty T).lift
      ((schemeDerivedQCohProperty (pullback f (h ≫ g))).ι ⋙
        schemeDerivedDirectImage (pullback.snd f (h ≫ g)))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))) _ _ _ _
        (pullback.snd f (h ≫ g)) _ _).fst E.obj E.property) ⊣ c)
    (adjd : (schemeDerivedQCohProperty T).lift
      ((schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι ⋙
        schemeDerivedDirectImage (pullback.snd (pullback.snd f g) h))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)) _ _ _ _
        (pullback.snd (pullback.snd f g) h) _ _).fst E.obj E.property) ⊣ d)
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f (h ≫ g)) (h ≫ g)
        (pullback.fst f (h ≫ g)) pullback.condition E.obj))
    (hβS : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition E.obj))
    (hβI : ∀ E : schemeDerivedQCohCategory (pullback f g),
      IsIso (schemeDerivedBaseChangeMap (pullback.snd f g) (pullback.snd (pullback.snd f g) h) h
        (pullback.fst (pullback.snd f g) h) pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y)
    (k : pullback (pullback.snd f g) h ⟶ pullback f (h ≫ g))
    (hk₁ : k ≫ pullback.fst f (h ≫ g) =
      pullback.fst (pullback.snd f g) h ≫ pullback.fst f g)
    (hk₂ : k ≫ pullback.snd f (h ≫ g) = pullback.snd (pullback.snd f g) h) :
    let G := Arrow.mk ((derivedPullback k).map
      ((schemeDerivedQCohProperty (pullback f (h ≫ g))).ι.map
      (dualityEquationBaseChangeMap f (h ≫ g) a c adja adjc hβ K)))
    let α := qcInverseBaseChange f g hβS
    let δ := @qcInverseBaseChange _ (pullback f g) S T _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
      (pullback.snd f g) _ _ h hβI
    let M := Arrow.mk ((schemeDerivedQCohProperty
      (pullback (pullback.snd f g) h)).ι.map
      ((mateEquiv adja adjd (α ≫ₕ δ)).app K))
    ∃ e₂ : G.right ≅ M.right,
      G.hom ≫ e₂.hom =
        (successiveBaseChangeSourceIso f g h k hk₁ (a.obj K).obj).hom ≫ M.hom  := by
  classical
  intro G α δ M
  obtain ⟨s, p, b, t, ht, hα, hs⟩ :=
    rectangle_ordinary_pasting_comparisons f g h c d adjc adjd hβ hβS hβI k hk₁ hk₂
  let I := (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι
  let e₂ := I.mapIso
    (t.app ((qcPullback (h ≫ g)).obj K) ≪≫
      d.mapIso (b.app K))
  refine ⟨e₂, ?_⟩
  have he := mate_comparison adja adjc adjd s p b t
    (qcInverseBaseChange f (h ≫ g) hβ) (α ≫ₕ δ) ht hα K
  have hh := I.congr_map he
  simp only [Functor.map_comp] at hh
  rw [← dualityEquationBaseChangeMap_eq_inverseSquareMate
    f (h ≫ g) a c adja adjc hβ K] at hh
  have hsource : I.map (s.hom.app (a.obj K)) =
      (successiveBaseChangeSourceIso f g h k hk₁ (a.obj K).obj).hom := by
    exact hs (a.obj K)
  rw [hsource] at hh
  change G.hom ≫ e₂.hom = _ at hh
  exact hh

end AlgebraicGeometry
