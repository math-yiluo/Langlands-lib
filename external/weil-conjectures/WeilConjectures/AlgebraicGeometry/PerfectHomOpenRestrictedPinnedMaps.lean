/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictionMap
public import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictedEquivFields
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictionTransport

/-! # Pinned restriction comparisons
Source: Stacks Tags 079W, 08FE and 09RE.
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section

private theorem transport_natural {X S : Scheme.{u}} (q : X ⟶ S)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {T T' : Over S} (g : T' ⟶ T) {M N K : schemeDerivedCategory X}
    (a : M ⟶ N)
    (f : (derivedPullback (pullback.fst q T.hom)).obj N ⟶
      (derivedPullback (pullback.fst q T.hom)).obj K) :
    perfectHomMap q g ((derivedPullback (pullback.fst q T.hom)).map a ≫ f) =
      (derivedPullback (pullback.fst q T'.hom)).map a ≫ perfectHomMap q g f := by
  unfold perfectHomMap
  rw [CategoryTheory.Functor.map_comp]
  have hn := (perfectHomComparison q g).hom.naturality a
  dsimp only [CategoryTheory.Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← Category.assoc ((perfectHomComparison q g).hom.app M), ← hn]
  simp only [Category.assoc]

private theorem stage_natural
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (j k : Set.Ici i) (hjk : j ≤ k)
    {M N Q : schemeDerivedCategory Y} (g : M ⟶ N)
    (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj N ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q) :
    perfectStageMap R s j.property hjk
      ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).map g ≫ f) =
    (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).map g ≫
      perfectStageMap R s j.property hjk f := by
  unfold perfectStageMap
  exact transport_natural s
    (T := Over.mk (Spec.map (R.map (homOfLE j.property))))
    (T' := Over.mk (Spec.map (R.map (homOfLE k.property)))) _ g f

private theorem limit_natural
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (j : Set.Ici i)
    {M N Q : schemeDerivedCategory Y} (g : M ⟶ N)
    (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj N ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q) :
    perfectLimitMap R c s j.property
      ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).map g ≫ f) =
    (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).map g ≫
      perfectLimitMap R c s j.property f := by
  unfold perfectLimitMap
  exact transport_natural s
    (T := Over.mk (Spec.map (R.map (homOfLE j.property))))
    (T' := Over.mk (Spec.map (c.ι.app i))) _ g f

/-- Pinned natural equivalences respect the restricted transition and cocone maps.

Source: Stacks Project, Cohomology Tags 079W and 08FE; perfect.tex Tag 09RE.
Proof: evaluate each transition equation at the identity of the restricted stage
object. The pinned equations turn the two sides into restrictions of the original
transition equation, using commutation of cartesian restriction and transport.
For any testing morphism f on B, testing-object naturality expresses both sides
as pullback(f) followed by those identity values. Naturality of conjugated Hom
transport allows the same expression on the right. Thus the identity equation
implies the equation for every f, without lifting f to Y.
(blueprint: new-perfect-hom-open-restricted-pinned-maps). -/
theorem perfect_hom_open_restricted_pinned_maps
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ schemeDerivedCategory Y)
    (d : Cocone F) (h : PerfectHomPushPullData R c s Q F d)
    (e : PerfectHomOpenRestrictedEquivFields R c s B Q F d)
    (hs :
    ∀ (j : Set.Ici i) (M : schemeDerivedCategory Y) (f : M ⟶ F.obj j),
      e.stageEquiv j ((schemeMVDerivedRestriction Y B).obj M)
          ((schemeMVDerivedRestriction Y B).map f) =
        perfectHomOpenRestrictionMap s B
          (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j M f))
    (hl :
    ∀ (M : schemeDerivedCategory Y) (f : M ⟶ d.pt),
      e.limitEquiv ((schemeMVDerivedRestriction Y B).obj M)
          ((schemeMVDerivedRestriction Y B).map f) =
        perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a
          (h.limitEquiv M f)) :
    (∀ (j k : Set.Ici i) (hjk : j ≤ k) (M : schemeDerivedCategory B.toScheme)
      (f : M ⟶ (F ⋙ schemeMVDerivedRestriction Y B).obj j),
      e.stageEquiv k M (f ≫ (F ⋙ schemeMVDerivedRestriction Y B).map (homOfLE hjk)) =
        perfectStageMap R (B.ι ≫ s) j.property hjk (e.stageEquiv j M f)) ∧
    (∀ (j : Set.Ici i) (M : schemeDerivedCategory B.toScheme)
      (f : M ⟶ (F ⋙ schemeMVDerivedRestriction Y B).obj j),
      e.limitEquiv M (f ≫ ((schemeMVDerivedRestriction Y B).mapCocone d).ι.app j) =
        perfectLimitMap R c (B.ι ≫ s) j.property (e.stageEquiv j M f)) := by
  obtain ⟨hstage, hlimit⟩ := perfect_hom_open_restriction_transport R c s B a
  constructor
  · intro j k hjk M f
    let L := schemeMVDerivedRestriction Y B
    have hid : e.stageEquiv k (L.obj (F.obj j)) (L.map (F.map (homOfLE hjk))) =
        perfectStageMap R (B.ι ≫ s) j.property hjk
          (e.stageEquiv j (L.obj (F.obj j)) (𝟙 _)) := by
      have hm := h.stageMap j k hjk (F.obj j) (𝟙 _)
      have hs0 := hs j (F.obj j) (𝟙 _)
      simp only [Category.id_comp] at hm
      rw [hs k, hm, hstage, ← hs0]
      exact congrArg (fun g ↦ perfectStageMap R (B.ι ≫ s) j.property hjk
        (e.stageEquiv j (L.obj (F.obj j)) g)) (L.map_id (F.obj j))
    have hn := e.stageNatural k M (L.obj (F.obj j)) f (L.map (F.map (homOfLE hjk)))
    have hj := e.stageNatural j M (L.obj (F.obj j)) f (𝟙 _)
    simp only [Category.comp_id] at hj
    change e.stageEquiv k M (f ≫ L.map (F.map (homOfLE hjk))) = _
    rw [hn, hid, hj, stage_natural]
  · intro j M f
    let L := schemeMVDerivedRestriction Y B
    have hid : e.limitEquiv (L.obj (F.obj j)) (L.map (d.ι.app j)) =
        perfectLimitMap R c (B.ι ≫ s) j.property
          (e.stageEquiv j (L.obj (F.obj j)) (𝟙 _)) := by
      have hm := h.limitMap j (F.obj j) (𝟙 _)
      have hs0 := hs j (F.obj j) (𝟙 _)
      simp only [Category.id_comp] at hm
      rw [hl, hm, hlimit, ← hs0]
      exact congrArg (fun g ↦ perfectLimitMap R c (B.ι ≫ s) j.property
        (e.stageEquiv j (L.obj (F.obj j)) g)) (L.map_id (F.obj j))
    have hn := e.limitNatural M (L.obj (F.obj j)) f (L.map (d.ι.app j))
    have hj := e.stageNatural j M (L.obj (F.obj j)) f (𝟙 _)
    simp only [Category.comp_id] at hj
    change e.limitEquiv M (f ≫ L.map (d.ι.app j)) = _
    rw [hn, hid, hj, limit_natural]

end
end AlgebraicGeometry
