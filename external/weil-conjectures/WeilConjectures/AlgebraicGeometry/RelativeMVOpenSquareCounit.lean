/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
import WeilConjectures.AlgebraicGeometry.RelativeMVOpenSquareCoefficientCoherence

/-! # Restricting the counit in a single open base-change square

Source: Stacks Project, Cohomology, Tags 08HY, 08BV and 0D5S.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_square
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    (L : A ⥤ B) (R : B ⥤ A) (L' : C ⥤ D) (R' : D ⥤ C)
    (G : A ⥤ C) (Q : B ⥤ D) (H : B ⥤ E) (H' : D ⥤ F)
    (T : A ⥤ E) (T' : C ⥤ F) (P : E ⥤ F)
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (c : L ⋙ H ≅ T) (c' : L' ⋙ H' ≅ T')
    (s : ∀ N, Q.obj (L.obj N) ⟶ L'.obj (G.obj N))
    (t : ∀ N, P.obj (T.obj N) ⟶ T'.obj (G.obj N))
    (d : H ⋙ P ≅ Q ⋙ H')
    (hc : ∀ N, P.map (c.hom.app N) ≫ t N =
      d.hom.app (L.obj N) ≫ H'.map (s N) ≫ c'.hom.app (G.obj N))
    (K : A) (a : G.obj (R.obj (L.obj K)) ⟶ R'.obj (L'.obj (G.obj K)))
    (ha : s (R.obj (L.obj K)) ≫ L'.map a ≫
      adj'.counit.app (L'.obj (G.obj K)) =
      Q.map (adj.counit.app (L.obj K)) ≫ s K) :
    t (R.obj (L.obj K)) ≫ T'.map a ≫
      c'.inv.app (R'.obj (L'.obj (G.obj K))) ≫
      H'.map (adj'.counit.app (L'.obj (G.obj K))) ≫ c'.hom.app (G.obj K) =
    P.map (c.inv.app (R.obj (L.obj K)) ≫
      H.map (adj.counit.app (L.obj K)) ≫ c.hom.app K) ≫ t K := by
  have hn := c'.inv.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have hstart : t (R.obj (L.obj K)) ≫ c'.inv.app (G.obj (R.obj (L.obj K))) =
      P.map (c.inv.app (R.obj (L.obj K))) ≫ d.hom.app (L.obj (R.obj (L.obj K))) ≫
        H'.map (s (R.obj (L.obj K))) := by
    apply (cancel_mono (c'.hom.app (G.obj (R.obj (L.obj K))))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← hc]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    rw [P.map_id]
    simp only [Category.comp_id, Category.id_comp]
  rw [reassoc_of% hstart]
  simp only [← H'.map_comp, ← Category.assoc]
  simp only [Category.assoc]
  rw [ha]
  simp only [Functor.map_comp, Category.assoc]
  have hd := d.hom.naturality (adj.counit.app (L.obj K))
  dsimp only [Functor.comp_map] at hd
  rw [← reassoc_of% hd, ← hc]

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem baseChange_counit
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) (E : schemeDerivedCategory X) :
    ((relativeMVAdj f').homEquiv _ _).symm
        (schemeDerivedBaseChangeMap f f' g g' h E) =
      (relativeMVComp f' g).hom.app ((schemeDerivedDirectImage f).obj E) ≫
        eqToHom (congrArg (fun k ↦
          (derivedPullback k).obj ((schemeDerivedDirectImage f).obj E)) h.symm) ≫
        (relativeMVComp g' f).inv.app ((schemeDerivedDirectImage f).obj E) ≫
        (derivedPullback g').map ((relativeMVAdj f).counit.app E) := by
  exact (relativeMVAdj f').homEquiv _ _ |>.symm_apply_apply _


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The pinned derived adjunctions require a larger elaboration and kernel budget.
/-- The single open-square counit calculation. There is no structure morphism `f`
or second base-change morphism `g`, and no relative direct image to a base.
Source: Stacks Project, Cohomology, Tags 08HY, 08BV and 0D5S.
(blueprint: new-relative-mv-open-square-counit).
Proof: Transpose the base-change map for U → X using its defining 08HY formula.
The target restriction counit is the transpose after the comparison for W' → U' → X'.
Naturality moves the base-change morphism through the inverse comparison. The
triangle identity cancels the U'-adjunction unit, leaving the pullback of the
U-adjunction counit and the U coefficient comparison. Associativity of the
canonical pullback comparisons on W → U → X and W' → U' → X', together with
both projection identities of relativeMVOpenLift, identifies these factors with
the W coefficient comparison, the pulled-back inverse W → U → X comparison,
the pulled-back U-counit, and the W coefficient comparison at K. Scheme.homOfLE_ι
identifies the open composite, and proof irrelevance identifies all equality
transports. The inverse W coefficient comparison is then canceled. This argument
uses neither strictness nor nonemptiness of the opens and works also for K = 0. -/
theorem relativeMV_open_square_counit
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (K : schemeDerivedCategory X) (W U : X.Opens) (i : W ≤ U) :
    let C := (schemeDerivedDirectImage U.ι).obj ((derivedPullback U.ι).obj K)
    let c := relativeMVComp (X.homOfLE i) U.ι ≪≫
      eqToIso (congrArg (fun t : W.toScheme ⟶ X ↦ derivedPullback t)
        (Scheme.homOfLE_ι X i))
    let c' := relativeMVComp (relativeMVOpenLift g' i) (pullback.fst g' U.ι) ≪≫
      eqToIso (congrArg (fun t : pullback g' W.ι ⟶ X' ↦ derivedPullback t)
        (pullback.lift_fst _ _ _))
    let γ (N : schemeDerivedCategory X) :=
      (relativeMVComp (pullback.snd g' W.ι) W.ι).hom.app N ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj N)
        (pullback.condition (f := g') (g := W.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' W.ι) g').inv.app N
    let θ := (relativeMVComp (pullback.snd g' U.ι) U.ι).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (pullback.condition (f := g') (g := U.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' U.ι) g').inv.app K
    γ C ≫ (derivedPullback (pullback.fst g' W.ι)).map
        (schemeDerivedBaseChangeMap U.ι (pullback.fst g' U.ι) g'
            (pullback.snd g' U.ι) (pullback.condition (f := g') (g := U.ι)).symm
            ((derivedPullback U.ι).obj K) ≫
          (schemeDerivedDirectImage (pullback.fst g' U.ι)).map θ) ≫
      c'.inv.app ((schemeDerivedDirectImage (pullback.fst g' U.ι)).obj
        ((derivedPullback (pullback.fst g' U.ι)).obj ((derivedPullback g').obj K))) ≫
      (derivedPullback (relativeMVOpenLift g' i)).map
        ((relativeMVAdj (pullback.fst g' U.ι)).counit.app
          ((derivedPullback (pullback.fst g' U.ι)).obj ((derivedPullback g').obj K))) ≫
      c'.hom.app ((derivedPullback g').obj K) =
      (derivedPullback (pullback.snd g' W.ι)).map
        (c.inv.app C ≫ (derivedPullback (X.homOfLE i)).map
          ((relativeMVAdj U.ι).counit.app ((derivedPullback U.ι).obj K)) ≫ c.hom.app K) ≫
      γ K := by
  classical
  let C := (schemeDerivedDirectImage U.ι).obj ((derivedPullback U.ι).obj K)
  let r := relativeMVOpenLift g' i
  let c := relativeMVComp (X.homOfLE i) U.ι ≪≫
    eqToIso (congrArg (fun t : W.toScheme ⟶ X ↦ derivedPullback t)
      (Scheme.homOfLE_ι X i))
  let c' := relativeMVComp r (pullback.fst g' U.ι) ≪≫
    eqToIso (congrArg (fun t : pullback g' W.ι ⟶ X' ↦ derivedPullback t)
      (pullback.lift_fst _ _ _))
  let s (N : schemeDerivedCategory X) :=
    (relativeMVComp (pullback.snd g' U.ι) U.ι).hom.app N ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj N)
      (pullback.condition (f := g') (g := U.ι)).symm) ≫
    (relativeMVComp (pullback.fst g' U.ι) g').inv.app N
  let t (N : schemeDerivedCategory X) :=
    (relativeMVComp (pullback.snd g' W.ι) W.ι).hom.app N ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj N)
      (pullback.condition (f := g') (g := W.ι)).symm) ≫
    (relativeMVComp (pullback.fst g' W.ι) g').inv.app N
  let hr : r ≫ pullback.snd g' U.ι = pullback.snd g' W.ι ≫ X.homOfLE i :=
    pullback.lift_snd _ _ _
  let d := relativeMVComp (pullback.snd g' W.ι) (X.homOfLE i) ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) hr.symm) ≪≫
    (relativeMVComp r (pullback.snd g' U.ι)).symm
  let a := schemeDerivedBaseChangeMap U.ι (pullback.fst g' U.ι) g'
      (pullback.snd g' U.ι) (pullback.condition (f := g') (g := U.ι)).symm
      ((derivedPullback U.ι).obj K) ≫
    (schemeDerivedDirectImage (pullback.fst g' U.ι)).map (s K)
  have hc := relativeMV_open_square_coefficient_coherence.{u, w} g' W U i
    c c' s t d rfl rfl (fun _ ↦ rfl) (fun _ ↦ rfl) rfl
  have ha : s C ≫ (derivedPullback (pullback.fst g' U.ι)).map a ≫
      (relativeMVAdj (pullback.fst g' U.ι)).counit.app
        ((derivedPullback (pullback.fst g' U.ι)).obj ((derivedPullback g').obj K)) =
      (derivedPullback (pullback.snd g' U.ι)).map
        ((relativeMVAdj U.ι).counit.app ((derivedPullback U.ι).obj K)) ≫ s K := by
    change s C ≫ ((relativeMVAdj (pullback.fst g' U.ι)).homEquiv _ _).symm a = _
    dsimp only [a]
    rw [Adjunction.homEquiv_naturality_right_symm, baseChange_counit]
    simp only [s, C, Category.assoc, Iso.inv_hom_id_app_assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Iso.hom_inv_id_app_assoc]
  exact
    restriction_square (derivedPullback U.ι) (schemeDerivedDirectImage U.ι)
      (derivedPullback (pullback.fst g' U.ι))
      (schemeDerivedDirectImage (pullback.fst g' U.ι))
      (derivedPullback g') (derivedPullback (pullback.snd g' U.ι))
      (derivedPullback (X.homOfLE i)) (derivedPullback r)
      (derivedPullback W.ι) (derivedPullback (pullback.fst g' W.ι))
      (derivedPullback (pullback.snd g' W.ι)) (relativeMVAdj U.ι)
      (relativeMVAdj (pullback.fst g' U.ι)) c c' s t d hc K a ha

end AlgebraicGeometry
