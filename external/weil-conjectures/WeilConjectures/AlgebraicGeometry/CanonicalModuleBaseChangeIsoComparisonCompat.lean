/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap

import WeilConjectures.AlgebraicGeometry.ModulePullbackComparisonTargetAutomorphism
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeCoordinateNaturality
import WeilConjectures.AlgebraicGeometry.ModulePullbackComparisonIsoTransport

/-! # Coordinate compatibility with a prescribed module comparison

Source: Stacks Project, Tags 06YJ, 08HY, 0D5T and 08IB.
(blueprint: stage3-canonicalModuleBaseChange_iso_comparison_ab).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- Combine naturality and a transported comparison, then cancel the target automorphism. -/
private theorem coordinate_comparison_square
    {C D E B : Type*} [Category* C] [Category* D] [Category* E] [Category* B]
    (U : C ⥤ D) (R : D ⥤ B) (T : B ⥤ E) (F : C ⥤ E)
    (k : F ≅ U ⋙ R ⋙ T)
    {X Y : C} {Z N : D} {L : E} {L₀ : B}
    (β : L ⟶ F.obj X) (β₀ : L₀ ⟶ R.obj Z) (a : L ≅ T.obj L₀)
    (c : X ⟶ Y) (j : U.obj X ⟶ Z) (m : U.obj Y ≅ N)
    (cT c₀ : Z ⟶ N) (α : N ≅ N)
    (hm : U.map c ≫ m.hom = j ≫ cT) (hα : cT = c₀ ≫ α.hom)
    (hβ : β ≫ k.hom.app X ≫ T.map (R.map j) = a.hom ≫ T.map β₀) :
    ∃ b : F.obj Y ≅ T.obj (R.obj N),
      (β ≫ F.map c) ≫ b.hom = a.hom ≫ T.map (β₀ ≫ R.map c₀) := by
  let b₀ := k.app Y ≪≫ T.mapIso (R.mapIso m)
  let d := T.mapIso (R.mapIso α)
  refine ⟨b₀ ≪≫ d.symm, ?_⟩
  have hcompat : (β ≫ F.map c) ≫ b₀.hom =
      (a.hom ≫ T.map (β₀ ≫ R.map c₀)) ≫ d.hom := by
    calc
      _ = β ≫ k.hom.app X ≫ T.map (R.map (U.map c ≫ m.hom)) := by
        dsimp only [b₀, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
        simp only [Functor.map_comp, Category.assoc]
        rw [← Category.assoc (F.map c), k.hom.naturality c]
        simp only [Functor.comp_map, Category.assoc]
      _ = β ≫ k.hom.app X ≫ T.map (R.map (j ≫ cT)) := by rw [hm]
      _ = (β ≫ k.hom.app X ≫ T.map (R.map j)) ≫ T.map (R.map cT) := by
        simp only [Functor.map_comp, Category.assoc]
      _ = (a.hom ≫ T.map β₀) ≫ T.map (R.map cT) := by rw [hβ]
      _ = _ := by simp only [hα, d, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  change (β ≫ F.map c) ≫ b₀.hom ≫ d.inv = _
  rw [← Category.assoc, hcompat]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Coordinate-change isomorphisms identify the canonical module base-change maps.
Source: Stacks Project, Tag 08HY, counit construction and coordinate transport;
Tag 0D5T, composition of derived functors.
(blueprint: stage3-canonicalModuleBaseChange_iso_comparison_ab).

Proof: Identify the given cartesian square with the chosen pullback square using
the coordinate isomorphisms. Derived pullback and direct-image composition,
together with cancellation of the inverse coordinates, give the source
isomorphism a0. The pullback isomorphism and ordinary tensor-pullback composition
identify the pulled-back modules; applying the single functor and derived
direct-image composition gives the target isomorphism b0. Transpose the two
base-change maps under the derived adjunction for the second projection. By
pullback composition and naturality of the counit, both transposes are the
pullback of the same counit of f after inverse coordinates cancel. Injectivity
of the adjunction Hom equivalence identifies these mates. First use compatible
counits to transport c to a comparison cT on the chosen
pullback. Mate naturality then gives the equation with a0, b0 and cT. The
predicate on c0 only asserts existence of a left-derived counit; it does not
pin it to the counit transported from hc. Apply
modulePullbackComparison_target_automorphism to c0 and cT: there is an ordinary
module automorphism alpha with cT = c0 followed by alpha[0]. Write d for the
image of alpha[0] under Rq_* and then T; d is an automorphism of the transported
target. Replace b0 by b0 followed by d.inv, and take a = a0. Functoriality and
cancellation of d.hom followed by d.inv give precisely the required equation.
Thus the assertion holds for every comparison c0, including when G is zero
or the schemes are empty. No flatness of G or affine hypothesis is used.
-/
theorem canonicalModuleBaseChange_iso_comparison_ab
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (G : X.Modules)
    (c : (derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback g').obj G))
    (hc : IsDerivedModulePullbackComparison g' G c)
    {A B : Scheme.{u}} (eS : S ≅ A) (eT : S' ≅ B)
    (c0 : (derivedPullback (pullback.fst (f ≫ eS.hom)
      (eT.inv ≫ g ≫ eS.hom))).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback (f ≫ eS.hom)
          (eT.inv ≫ g ≫ eS.hom)).toRingedSpace)) 0).obj
        ((Scheme.Modules.tensorPullback (pullback.fst (f ≫ eS.hom)
          (eT.inv ≫ g ≫ eS.hom))).obj G))
    (hc0 : IsDerivedModulePullbackComparison
      (pullback.fst (f ≫ eS.hom) (eT.inv ≫ g ≫ eS.hom)) G c0) :
  let fA := f ≫ eS.hom
      let gA := eT.inv ≫ g ≫ eS.hom
      let E := (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
      let T := schemeDerivedDirectImage eT.inv
      ∃ a : (derivedPullback g).obj ((schemeDerivedDirectImage f).obj E) ≅
            T.obj ((derivedPullback gA).obj ((schemeDerivedDirectImage fA).obj E)),
        ∃ b : (schemeDerivedDirectImage f').obj
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
                  ((Scheme.Modules.tensorPullback g').obj G)) ≅
            T.obj ((schemeDerivedDirectImage (pullback.snd fA gA)).obj
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj G))),
          (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
              (schemeDerivedDirectImage f').map c) ≫ b.hom =
            a.hom ≫ T.map
              (schemeDerivedBaseChangeMap fA (pullback.snd fA gA) gA (pullback.fst fA gA)
                pullback.condition E ≫ (schemeDerivedDirectImage (pullback.snd fA gA)).map c0)
       := by
  classical
  intro fA gA E T
  let p := pullback.fst fA gA
  let q := pullback.snd fA gA
  let S0 := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0
  let R := schemeDerivedDirectImage q
  obtain ⟨e, hp, _, j, k, a, hβ⟩ :=
    exists_derivedBaseChange_coordinate_naturality f g g' f' sq eS eT
  obtain ⟨cT, hcT, m, hm⟩ :=
    exists_modulePullbackComparison_iso_transport g' p e hp j G c hc
  obtain ⟨α, hα⟩ := modulePullbackComparison_target_automorphism p G c0 cT hc0 hcT
  refine ⟨a.app E, ?_⟩
  exact coordinate_comparison_square (schemeDerivedDirectImage e.hom) R T
    (schemeDerivedDirectImage f') k
    (schemeDerivedBaseChangeMap f f' g g' sq.w E)
    (schemeDerivedBaseChangeMap fA q gA p pullback.condition E)
    (a.app E) c (j.hom.app E) m cT c0 (S0.mapIso α) hm hα (hβ E)

end AlgebraicGeometry
