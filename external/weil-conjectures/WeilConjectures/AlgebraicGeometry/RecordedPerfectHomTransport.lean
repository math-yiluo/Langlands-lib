/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition
import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionCoherence
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent

/-! # Canonical transport of Hom groups in the base-change system.
Source: Stacks Project, Cohomology, Tag 0D5S and perfect.tex, Tag 09RE.
(blueprint: lem-pc-recorded-perfect-hom-transport).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The composition lift pinned to the retained original derived-pullback counits.
Source: Stacks Project, Tag 0D5S (blueprint: lem-pc-recorded-perfect-hom-transport). -/
noncomputable abbrev recordedPerfectHomComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) :=
  recordedDerivedPullbackComposition f g

/-- The counit-pinned comparison for a base-change arrow. This is the explicit
construction used by `perfectDescentComparison`, with no independently chosen data.
Source: Stacks Project, Tag 0D5S
(blueprint: lem-pc-recorded-perfect-hom-transport). -/
noncomputable def recordedPerfectHomComparison {X S : Scheme.{u}} (s : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) :
    derivedPullback (pullback.fst s T'.hom) ≅
      derivedPullback (pullback.fst s T.hom) ⋙ derivedPullback (baseChangeMap s g) :=
  eqToIso (congrArg (fun k ↦ derivedPullback k) (baseChangeMap_fst s g).symm) ≪≫
    (recordedPerfectHomComposition (baseChangeMap s g) (pullback.fst s T.hom)).symm

/-- Conjugate pullback on Hom by the fixed composition comparisons.
Source: Stacks Project, Tag 09RE (blueprint: lem-pc-recorded-perfect-hom-transport). -/
noncomputable def recordedPerfectHomMap {X S : Scheme.{u}} (s : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) {P Q : schemeDerivedCategory X}
    (f : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    (derivedPullback (pullback.fst s T'.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T'.hom)).obj Q :=
  (recordedPerfectHomComparison s g).hom.app P ≫
    (derivedPullback (baseChangeMap s g)).map f ≫ (recordedPerfectHomComparison s g).inv.app Q

/-- (blueprint: lem-pc-recorded-perfect-hom-transport) -/
@[simp] theorem recordedPerfectHomMap_id {X S : Scheme.{u}} (s : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) (P : schemeDerivedCategory X) :
    recordedPerfectHomMap s g (𝟙 ((derivedPullback (pullback.fst s T.hom)).obj P)) =
      𝟙 _ := by
  simp [recordedPerfectHomMap]

/-- (blueprint: lem-pc-recorded-perfect-hom-transport) -/
@[simp] theorem recordedPerfectHomMap_comp {X S : Scheme.{u}} (s : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) {P Q K : schemeDerivedCategory X}
    (a : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q)
    (b : (derivedPullback (pullback.fst s T.hom)).obj Q ⟶
      (derivedPullback (pullback.fst s T.hom)).obj K) :
    recordedPerfectHomMap s g (a ≫ b) = recordedPerfectHomMap s g a ≫
      recordedPerfectHomMap s g b := by
  simp [recordedPerfectHomMap, Category.assoc]

/-- (blueprint: lem-pc-recorded-perfect-hom-transport) -/
theorem recordedPerfectHomMap_eq_iff {X S : Scheme.{u}} (s : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) {P Q : schemeDerivedCategory X}
    (a b : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    recordedPerfectHomMap s g a = recordedPerfectHomMap s g b ↔
      (derivedPullback (baseChangeMap s g)).map a =
        (derivedPullback (baseChangeMap s g)).map b := by
  simp only [recordedPerfectHomMap, cancel_epi, cancel_mono]


private theorem cc_assoc {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.isoWhiskerRight (recordedPerfectHomComposition f g) (derivedPullback h) ≪≫
      recordedPerfectHomComposition h (f ≫ g) =
      Functor.associator (derivedPullback g) (derivedPullback f) (derivedPullback h) ≪≫
        Functor.isoWhiskerLeft (derivedPullback g) (recordedPerfectHomComposition h f) ≪≫
          recordedPerfectHomComposition (h ≫ f) g ≪≫
          eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k) (Category.assoc h f g)) := by
  exact (Classical.choose_spec (derivedPullbackComposition_coherence
    (fun f ↦ by
      rw [← recordedPullbackData_E f]
      exact recordedPullbackData_additive f) (fun f ↦ recordedDerivedPullbackCounit f)
    (fun f ↦ recordedDerivedPullbackCounit_universal f)
    (fun f P hP ↦ recordedDerivedPullbackCounit_kFlat f P hP)
    (fun f g ↦ recordedDerivedPullbackComposition f g) (fun _ _ ↦ rfl))).2.2 h f g

private noncomputable def recordedTr {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback g).obj P ⟶ (derivedPullback g).obj Q) :
    (derivedPullback (f ≫ g)).obj P ⟶ (derivedPullback (f ≫ g)).obj Q :=
  (recordedPerfectHomComposition f g).inv.app P ≫ (derivedPullback f).map a ≫
    (recordedPerfectHomComposition f g).hom.app Q

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem recordedTr_assoc
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback g).obj P ⟶ (derivedPullback g).obj Q) :
    recordedTr h (f ≫ g) (recordedTr f g a) =
      (eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
        (Category.assoc h f g))).inv.app P ≫ recordedTr (h ≫ f) g a ≫
      (eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
        (Category.assoc h f g))).hom.app Q := by
  have hi := congrArg (fun e ↦ e.inv.app P) (cc_assoc h f g)
  have hh := congrArg (fun e ↦ e.hom.app Q) (cc_assoc h f g)
  simp only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Category.comp_id, Category.id_comp, Category.assoc] at hi hh
  simp only [recordedTr, Functor.map_comp]
  simp only [Category.assoc] at hi hh ⊢
  rw [← Category.assoc ((recordedPerfectHomComposition h (f ≫ g)).inv.app P)
    ((derivedPullback h).map ((recordedPerfectHomComposition f g).inv.app P)), hi]
  simp only [Category.assoc]
  rw [hh]
  have hn := (recordedPerfectHomComposition h f).hom.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc ((derivedPullback h).map ((derivedPullback f).map a)), hn]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private noncomputable def recordedTrTo {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ Z)
    (q : X ⟶ Z) (e : f ≫ p = q) {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback p).obj P ⟶ (derivedPullback p).obj Q) :
    (derivedPullback q).obj P ⟶ (derivedPullback q).obj Q :=
  (eqToIso (congrArg (fun k ↦ derivedPullback k) e.symm)).hom.app P ≫
    recordedTr f p a ≫ (eqToIso (congrArg (fun k ↦ derivedPullback k) e.symm)).inv.app Q

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem recordedTrTo_refl
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ Z)
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback p).obj P ⟶ (derivedPullback p).obj Q) :
    recordedTrTo f p (f ≫ p) rfl a = recordedTr f p a := by
  simp only [recordedTrTo, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id]

-- Comparing the fixed composition isomorphisms reduces their universal properties.
omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem recordedTrTo_assoc
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y)
    (p : Y ⟶ Z) (q : X ⟶ Z) (r : W ⟶ Z) (eq : f ≫ p = q) (er : h ≫ q = r)
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback p).obj P ⟶ (derivedPullback p).obj Q) :
    recordedTrTo h q r er (recordedTrTo f p q eq a) =
      recordedTrTo (h ≫ f) p r (by rw [Category.assoc, eq, er]) a := by
  subst q
  subst r
  rw [recordedTrTo_refl, recordedTrTo_refl]
  have he : eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
      (Category.assoc h f p).symm) =
      (eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
        (Category.assoc h f p))).symm := rfl
  conv_rhs => unfold recordedTrTo
  rw [he]
  exact recordedTr_assoc h f p a

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem recordedTrTo_congr
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Z : Scheme.{u}} (f f' : X ⟶ Y) (p : Y ⟶ Z)
    (q : X ⟶ Z) (e : f ≫ p = q) (e' : f' ≫ p = q) (hf : f = f')
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback p).obj P ⟶ (derivedPullback p).obj Q) :
    recordedTrTo f p q e a = recordedTrTo f' p q e' a := by
  subst f'
  rfl

private theorem recordedHomMap_trTo {X S : Scheme.{u}} (s : X ⟶ S) {T T' : Over S}
    (g : T' ⟶ T) {P Q : schemeDerivedCategory X}
    (a : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    recordedPerfectHomMap s g a =
      recordedTrTo (baseChangeMap s g) (pullback.fst s T.hom)
      (pullback.fst s T'.hom) (baseChangeMap_fst s g) a := by
  simp only [recordedTrTo, recordedTr, recordedPerfectHomMap, recordedPerfectHomComparison,
    Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Category.assoc]

-- Reducing the fixed comparison construction exposes the conjugation formula.
/-- Conjugated Hom transport composes along successive base-change maps.
Source: Stacks Project, Tags 0D5S and 09RE
(blueprint: lem-pc-recorded-perfect-hom-transport). -/
theorem recordedPerfectHomMap_trans {X S : Scheme.{u}} (s : X ⟶ S) {T T' T'' : Over S}
    (g : T' ⟶ T) (h : T'' ⟶ T') {P Q : schemeDerivedCategory X}
    (a : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    recordedPerfectHomMap s h (recordedPerfectHomMap s g a) =
      recordedPerfectHomMap s (h ≫ g) a := by
  have ht := recordedTrTo_assoc (baseChangeMap s h) (baseChangeMap s g)
    (pullback.fst s T.hom) (pullback.fst s T'.hom) (pullback.fst s T''.hom)
    (baseChangeMap_fst s g) (baseChangeMap_fst s h) a
  rw [recordedHomMap_trTo, recordedHomMap_trTo, recordedHomMap_trTo]
  apply ht.trans
  exact recordedTrTo_congr _ _ _ _ _ _ (baseChangeMap_comp s h g).symm a

/-- Transport from one finite stage to a later finite stage.
Source: Stacks Project, Tag 09RE (blueprint: lem-pc-recorded-perfect-hom-transport). -/
noncomputable def recordedPerfectStageMap {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
    {i : I} {X : Scheme.{u}} (s : X ⟶ Spec (R.obj i))
    {j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    {P Q : schemeDerivedCategory X}
    (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Q) :=
  recordedPerfectHomMap s
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
    (Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) f

/-- Transport from a finite stage to the colimit scheme.
Source: Stacks Project, Tag 09RE (blueprint: lem-pc-recorded-perfect-hom-transport). -/
noncomputable def recordedPerfectLimitMap {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
    (c : Cocone R) {i : I} {X : Scheme.{u}} (s : X ⟶ Spec (R.obj i))
    {j : I} (hij : i ≤ j) {P Q : schemeDerivedCategory X}
    (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Q) :=
  recordedPerfectHomMap s
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (c.ι.app i)))
    (Over.homMk (Spec.map (c.ι.app j))
      (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) f

/-- (blueprint: lem-pc-recorded-perfect-hom-transport) -/
@[simp] theorem recordedPerfectStageMap_id {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) {i : I} {X : Scheme.{u}} (s : X ⟶ Spec (R.obj i))
    {j k : I} (hij : i ≤ j) (hjk : j ≤ k) (P : schemeDerivedCategory X) :
    recordedPerfectStageMap R s hij hjk
      (𝟙 ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P)) =
        𝟙 _ := by
  exact recordedPerfectHomMap_id s
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
    (Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) P

/-- (blueprint: lem-pc-recorded-perfect-hom-transport) -/
@[simp] theorem recordedPerfectLimitMap_id {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) {i : I} {X : Scheme.{u}}
    (s : X ⟶ Spec (R.obj i)) {j : I} (hij : i ≤ j) (P : schemeDerivedCategory X) :
    recordedPerfectLimitMap R c s hij
      (𝟙 ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P)) =
        𝟙 _ := by
  exact recordedPerfectHomMap_id s
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (c.ι.app i)))
    (Over.homMk (Spec.map (c.ι.app j))
      (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) P

/-- Transport to the colimit is compatible with increasing the finite stage.
No perfectness or finite-presentation hypothesis is needed for this coherence identity.
Source: Stacks Project, Cohomology, Tag 0D5S, and perfect.tex, Tag 09RE
(blueprint: lem-pc-recorded-perfect-hom-transport).

Proof: apply `derivedPullbackComposition_coherence` to the recorded counits and
explicit composition lifts, and specialize its associativity law to the
finite-stage base-change map, the map from the colimit scheme, and the projection
onto X. The equality of their composite base-change map with the direct map follows
from the pullback universal property and the cocone equation. Whisker the resulting
comparison identity at P and Q; naturality of the composition comparison transports
pullback of f. Cancel the adjacent comparison and inverse-comparison components.
The resulting conjugated Hom maps are precisely the two sides below. -/
theorem recordedPerfectLimitMap_stage {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
    (c : Cocone R) {i : I} {X : Scheme.{u}} (s : X ⟶ Spec (R.obj i))
    {j k : I} (hij : i ≤ j) (hjk : j ≤ k) {P Q : schemeDerivedCategory X}
    (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Q) :
    recordedPerfectLimitMap R c s (hij.trans hjk) (recordedPerfectStageMap R s hij hjk f) =
      recordedPerfectLimitMap R c s hij f := by
  unfold recordedPerfectLimitMap recordedPerfectStageMap
  rw [recordedPerfectHomMap_trans]
  congr 1
  ext
  change Spec.map (c.ι.app k) ≫ Spec.map (R.map (homOfLE hjk)) = Spec.map (c.ι.app j)
  rw [← Spec.map_comp, c.w (homOfLE hjk)]

end AlgebraicGeometry
