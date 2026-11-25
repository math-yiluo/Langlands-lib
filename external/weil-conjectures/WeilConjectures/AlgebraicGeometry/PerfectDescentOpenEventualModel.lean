/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectDescentOnOpen
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData

/-! # Eventual perfect model on a specified open

Source: Stacks Project, Tag 09RF, descent of each restriction and enlargement of its stage.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Pasting the restriction square with the base-change square fixes the identification.
private noncomputable def openBaseChangeIso {Z S : Scheme.{u}} (t : Z ⟶ S)
    (O : Z.Opens) (T : Over S) :
    ((pullback.fst t T.hom) ⁻¹ᵁ O).toScheme ≅ pullback (O.ι ≫ t) T.hom :=
  ((isPullback_morphismRestrict (pullback.fst t T.hom) O).paste_vert
    (IsPullback.of_hasPullback t T.hom)).isoPullback

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The canonical map from the base change of the open to the base change of its ambient.
private noncomputable def openBaseChangeInclusion {Z S : Scheme.{u}} (t : Z ⟶ S)
    (O : Z.Opens) (T : Over S) :
    pullback (O.ι ≫ t) T.hom ⟶ pullback t T.hom :=
  pullback.map _ _ _ _ O.ι (𝟙 _) (𝟙 _) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Transport a supplied model comparison through the cartesian open identifications.
private theorem openBaseChange_transport
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {Z S : Scheme.{u}} (t : Z ⟶ S) (O : Z.Opens)
    {T T' : Over S} (β : T' ⟶ T)
    (E : schemeDerivedCategory (pullback t T'.hom))
    (B : schemeDerivedCategory (pullback (O.ι ≫ t) T.hom))
    (hB : (pullback (O.ι ≫ t) T.hom).IsPerfect B)
    (hcomp : Nonempty ((derivedPullback (baseChangeMap (O.ι ≫ t) β)).obj B ≅
      (derivedPullback (openBaseChangeInclusion t O T')).obj E)) :
    let g := baseChangeMap t β
    let U := (pullback.fst t T.hom) ⁻¹ᵁ O
    ∃ A : schemeDerivedCategory U.toScheme, U.toScheme.IsPerfect A ∧
      Nonempty ((derivedPullback (g ∣_ U)).obj A ≅
        (schemeOpenRestriction (pullback t T'.hom) (g ⁻¹ᵁ U)).mapDerivedCategory.obj E) := by
  classical
  dsimp only
  let g := baseChangeMap t β
  let U := (pullback.fst t T.hom) ⁻¹ᵁ O
  let V := g ⁻¹ᵁ U
  have hV : V = (pullback.fst t T'.hom) ⁻¹ᵁ O := by
    dsimp only [V, U, g]
    rw [← Scheme.Hom.comp_preimage, baseChangeMap_fst]
  let eU := openBaseChangeIso t O T
  let eV := (pullback t T'.hom).isoOfEq hV ≪≫ openBaseChangeIso t O T'
  let q := openBaseChangeInclusion t O T'
  let gO := baseChangeMap (O.ι ≫ t) β
  have hsquare : (g ∣_ U) ≫ eU.hom = eV.hom ≫ gO := by
    apply pullback.hom_ext
    · apply (cancel_mono O.ι).mp
      simp [eU, eV, openBaseChangeIso, gO, g, U, V,
        Category.assoc, morphismRestrict_ι]
    · simp [eU, eV, openBaseChangeIso, gO, g, U, V, Category.assoc]
  have hq : eV.hom ≫ q = V.ι := by
    apply pullback.hom_ext
    · simp [eV, q, openBaseChangeIso, openBaseChangeInclusion,
        Category.assoc, morphismRestrict_ι]
    · simp [eV, q, openBaseChangeIso, openBaseChangeInclusion, Category.assoc]
  let comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) :=
    (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))).choose
  obtain ⟨comparison⟩ := hcomp
  refine ⟨(derivedPullback eU.hom).obj B,
    derivedPullback_preserve_perfect eU.hom B hB, ⟨?_⟩⟩
  exact (comp (g ∣_ U) eU.hom).app B ≪≫
    eqToIso (congrArg (fun a ↦ (derivedPullback a).obj B) hsquare) ≪≫
    ((comp eV.hom gO).app B).symm ≪≫
    (derivedPullback eV.hom).mapIso comparison ≪≫
    (comp eV.hom q).app E ≪≫
    eqToIso (congrArg (fun a ↦ (derivedPullback a).obj E) hq) ≪≫
    (singleComplexOpenPullbackIso (pullback t T'.hom) V).app E

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Descent on one original open supplies models on its inverse image at every later stage.
Source: Stacks Project, Tag 09RF, choice and subsequent base change of each local model.
(blueprint: lem-pc-perfect-descent-open-eventual-model).

Proof: Put O = f inverse W and restrict the limit perfect object to the inverse image of O.
The presentation O.toScheme → Xi is an open immersion with image W, because W is contained
in the image of f. Pullback along the open immersion preserves perfectness (Tag 09UA).
Apply dW to this presentation. It gives an index j ≥ i, a perfect stage model, and a limit
comparison. For k ≥ j pull that model back along the transition morphism. The canonical
cartesian identifications of the base change of O with the inverse-image open in the base
change of Z transport it to A. Pullback preserves perfectness; the composition comparison
for derived pullbacks and the comparison with exact open restriction identify its limit
pullback with the displayed restriction of E. Empty opens and non-antisymmetric preorders
use the same pullback identifications; no colimit hypothesis is needed. -/
theorem perfect_descent_open_eventual_model
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ i : I, IsNoetherianRing (R.obj i)]
    (c : Cocone R) (i : I) (Xi : Scheme.{u}) (s : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (W : Xi.Opens) (dW : PerfectDescentOnOpen R c i Xi s W)
    (Z : Scheme.{u}) (f : Z ⟶ Xi) [IsOpenImmersion f] (hW : W ≤ f.opensRange)
    (E : schemeDerivedCategory (pullback (f ≫ s) (Spec.map (c.ι.app i))))
    (hE : (pullback (f ≫ s) (Spec.map (c.ι.app i))).IsPerfect E) :
    ∃ (j : I) (hij : i ≤ j), ∀ (k : I) (hjk : j ≤ k),
      let X := pullback (f ≫ s) (Spec.map (c.ι.app i))
      let g := baseChangeMap (f ≫ s)
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      let U := (pullback.fst (f ≫ s)
        (Spec.map (R.map (homOfLE (hij.trans hjk)))) ≫ f) ⁻¹ᵁ W
      ∃ A : schemeDerivedCategory U.toScheme, U.toScheme.IsPerfect A ∧
        Nonempty ((derivedPullback (g ∣_ U)).obj A ≅
          (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.obj E) := by
  classical
  let O : Z.Opens := f ⁻¹ᵁ W
  let r : O.toScheme ⟶ Xi := O.ι ≫ f
  have hr : r.opensRange = W := by
    dsimp only [r]
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hW]
  let t := f ≫ s
  let Tc : Over (Spec (R.obj i)) := Over.mk (Spec.map (c.ι.app i))
  let q := openBaseChangeInclusion t O Tc
  let Eo := (derivedPullback q).obj E
  have hEo : (pullback (O.ι ≫ t) Tc.hom).IsPerfect Eo :=
    derivedPullback_preserve_perfect q E hE
  have dr := dW O.toScheme r hr
  dsimp only [r] at dr
  have descent := dr Eo hEo
  let j := descent.choose
  have hij : i ≤ j := descent.choose_spec.choose
  let Ej := descent.choose_spec.choose_spec.choose
  have hEj := descent.choose_spec.choose_spec.choose_spec.1
  let eEj := descent.choose_spec.choose_spec.choose_spec.2.some
  refine ⟨j, hij, ?_⟩
  intro k hjk
  let Tj : Over (Spec (R.obj i)) := Over.mk (Spec.map (R.map (homOfLE hij)))
  let Tk : Over (Spec (R.obj i)) :=
    Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk))))
  let α : Tk ⟶ Tj := Over.homMk (Spec.map (R.map (homOfLE hjk))) (by
    dsimp [Tk, Tj]
    rw [← Spec.map_comp, ← R.map_comp]
    rfl)
  let βj : Tc ⟶ Tj := Over.homMk (Spec.map (c.ι.app j)) (by
    dsimp [Tc, Tj]
    rw [← Spec.map_comp, c.w (homOfLE hij)])
  let βk : Tc ⟶ Tk := Over.homMk (Spec.map (c.ι.app k)) (by
    dsimp [Tc, Tk]
    rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))])
  have hβα : βk ≫ α = βj := by
    ext
    change Spec.map (c.ι.app k) ≫ Spec.map (R.map (homOfLE hjk)) =
      Spec.map (c.ι.app j)
    rw [← Spec.map_comp, c.w (homOfLE hjk)]
  let a := baseChangeMap (O.ι ≫ t) α
  let B := (derivedPullback a).obj Ej
  have hB : (pullback (O.ι ≫ t) Tk.hom).IsPerfect B :=
    derivedPullback_preserve_perfect a Ej hEj
  let comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) :=
    (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))).choose
  have hm : baseChangeMap (O.ι ≫ t) βk ≫ a = baseChangeMap (O.ι ≫ t) βj := by
    rw [← baseChangeMap_comp, hβα]
  have hcomp : Nonempty ((derivedPullback (baseChangeMap (O.ι ≫ t) βk)).obj B ≅
      (derivedPullback q).obj E) := by
    refine ⟨(comp (baseChangeMap (O.ι ≫ t) βk) a).app Ej ≪≫ ?_ ≪≫ eEj⟩
    exact eqToIso (congrArg (fun b ↦ (derivedPullback b).obj Ej) hm)
  have result := openBaseChange_transport t O βk E B hB hcomp
  simpa only [t, O, Tc, Tk, βk, Over.mk_hom, ← Scheme.Hom.comp_preimage] using result

end AlgebraicGeometry
