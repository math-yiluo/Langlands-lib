/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction

/-! # Equality of unit sections on a cartesian étale object
Source: Stacks Project, Tags 03S2, 00XZ, 03CB and 03CC.
(blueprint: lem-weil-pbc-sets-cartesian-unit-equality). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private noncomputable def unitSection {S T : Scheme.{u}} (h : T ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (Q : S.Etale) :=
  ((@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
    (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1)) _
    (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)
    (Etale.isContinuous_overPullback h) _ _).unit.app F).hom.app (op Q)

private noncomputable def sectionPullback {S T : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (Q : S.Etale)
    (p : T ⟶ Q.left) (w : T ⟶ S) (hw : p ≫ Q.hom = w)
    (s : F.obj.obj (op Q)) :
    ((Scheme.etaleSetPullback w).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 T))) :=
  ((Scheme.etaleSetPullback w).obj F).obj.map
    (MorphismProperty.Over.homMk
      (A := Scheme.Etale.mk (𝟙 T))
      (B := (MorphismProperty.Over.pullback @Etale ⊤ w).obj Q)
      (pullback.lift p (𝟙 T) (hw.trans (Category.id_comp w).symm))
      (by simp)).op (unitSection w F Q s)

private theorem sectionPullback_eq_iff {S T : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (Q : S.Etale)
    (p : T ⟶ Q.left) (w : T ⟶ S) (hw : p ≫ Q.hom = w)
    (s t : F.obj.obj (op Q)) :
    sectionPullback F Q p (p ≫ Q.hom) rfl s =
        sectionPullback F Q p (p ≫ Q.hom) rfl t ↔
      sectionPullback F Q p w hw s = sectionPullback F Q p w hw t := by
  subst w
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, Tag 03S2, inverse image along an étale map is
restriction; Sites Tags 00XZ, 03CB and 03CC, localization and composition units.
(blueprint: lem-weil-pbc-sets-cartesian-unit-equality).

Proof:
Let B = Q ×[S] T and use e to identify A with B. The restriction isomorphism
for the étale map A.hom identifies the value of h inverse image F at A with
the terminal value of A.hom inverse image (h inverse image F). Naturality of
the inverse-image unit in the site object, and its composition equation for
A.hom followed by h, identify the unit at Q followed by this restriction
isomorphism with the unit for p followed by Q.hom, restricted along (p,id).
The equality hp identifies the first projection of this cartesian square.
The composition and restriction maps are isomorphisms, as is the restriction
along e. Thus these maps preserve and reflect equality of the two sections.
No injectivity of the unit itself is asserted. The identity base change,
identical sections and empty total spaces satisfy the same equation. -/
theorem etaleSetCartesianUnit_eq_iff
    {S T : Scheme.{u}} (h : T ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (Q : S.Etale) (A : T.Etale)
    (e : A ≅ (MorphismProperty.Over.pullback @Etale ⊤ h).obj Q)
    (p : A.left ⟶ Q.left)
    (hp : e.hom.left ≫ pullback.fst Q.hom h = p)
    (s t : F.obj.obj (op Q)) :
    let η := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
      (S.smallGrothendieckTopology @Etale)
      (T.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op Q)
    let ηp := ((@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
      (MorphismProperty.Over.pullback @Etale ⊤ (p ≫ Q.hom)) (Type (u + 1)) _
      (S.smallGrothendieckTopology @Etale)
      (A.left.smallGrothendieckTopology @Etale)
      (Etale.isContinuous_overPullback (p ≫ Q.hom)) _ _).unit.app F).hom.app (op Q)
    let δ : Scheme.Etale.mk (𝟙 A.left) ⟶
        (MorphismProperty.Over.pullback @Etale ⊤ (p ≫ Q.hom)).obj Q :=
      MorphismProperty.Over.homMk
        (pullback.lift p (𝟙 A.left) (Category.id_comp (p ≫ Q.hom)).symm)
        (pullback.lift_snd _ _ _)
    η s = η t ↔
      ((Scheme.etaleSetPullback (p ≫ Q.hom)).obj F).obj.map δ.op (ηp s) =
        ((Scheme.etaleSetPullback (p ≫ Q.hom)).obj F).obj.map δ.op (ηp t) := by
  classical
  change unitSection h F Q s = unitSection h F Q t ↔
    sectionPullback F Q p (p ≫ Q.hom) rfl s =
      sectionPullback F Q p (p ≫ Q.hom) rfl t
  let B := (MorphismProperty.Over.pullback @Etale ⊤ h).obj Q
  let v : A.left ⟶ T := A.hom
  have hw : p ≫ Q.hom = v ≫ h := by
    rw [← hp, Category.assoc, pullback.condition]
    exact congrArg (fun a ↦ a ≫ h) e.hom.w
  rw [sectionPullback_eq_iff F Q p (v ≫ h) hw s t]
  let O := Scheme.Etale.mk (𝟙 A.left)
  let H := (Scheme.etaleSetPullback h).obj F
  let c := Classical.choose etaleSetInverseImageCompositionUnits.2.2 S T A.left h v
  let E := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) v h).app Q
  let d : O ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (v ≫ h)).obj Q :=
    MorphismProperty.Over.homMk
      (pullback.lift p (𝟙 A.left) (hw.trans (Category.id_comp _).symm))
      (by change _ = 𝟙 A.left; simp)
  let d' := d ≫ E.hom
  let M := MorphismProperty.Over.map ⊤ (inferInstance : Etale v)
  let ε := (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ v
    inferInstance trivial).counit.app B
  let z : M.obj O ≅ A := MorphismProperty.Over.isoMk (Iso.refl A.left)
    (by change 𝟙 A.left ≫ A.hom = 𝟙 A.left ≫ v; rfl)
  have hd : M.map d' ≫ ε = z.hom ≫ e.hom := by
    apply MorphismProperty.Over.Hom.ext
    simp only [MorphismProperty.Over.map_obj_left, Functor.id_obj,
      MorphismProperty.Over.pullback_obj_left, Functor.comp_obj, Functor.const_obj_obj,
      Iso.app_hom, Functor.map_comp, MorphismProperty.Over.mapPullbackAdj_counit_app,
      MorphismProperty.Over.pullback_obj_hom, Category.assoc, MorphismProperty.Comma.comp_hom,
      MorphismProperty.Over.homMk_hom, Comma.comp_left, MorphismProperty.Over.map_map_left,
      Over.homMk_left, MorphismProperty.Over.pullbackComp_hom_app_left, pullback.map_id,
      Category.id_comp, MorphismProperty.Over.isoMk_hom_left, Iso.refl_hom, M, B, d', d, E, ε, z]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
        pullback.lift_fst]
      change p = 𝟙 A.left ≫ e.hom.left ≫ pullback.fst Q.hom h
      simpa only [Category.id_comp] using hp.symm
    · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
        pullback.lift_snd_assoc]
      change 𝟙 A.left ≫ v = 𝟙 A.left ≫ e.hom.left ≫ pullback.snd Q.hom h
      have hw' := e.hom.w
      change e.hom.left ≫ pullback.snd Q.hom h = v ≫ 𝟙 T at hw'
      simpa only [Category.id_comp, Category.comp_id] using hw'.symm
  obtain ⟨ρ, hρ⟩ := etaleSetInverseImageRestriction v
  let β := (c.hom.app F).hom.app (op O)
  let χ := (ρ.hom.app H).hom.app (op O)
  let α := H.obj.map (z.hom ≫ e.hom).op
  have hα : Function.Injective α := CategoryTheory.injective_of_mono α
  have hχ : Function.Injective χ := CategoryTheory.injective_of_mono χ
  have hsection (x : F.obj.obj (op Q)) :
      χ (inv β (sectionPullback F Q p (v ≫ h) hw x)) = α (unitSection h F Q x) := by
    have hc : (c.hom.app F).hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj B))
        (unitSection v H B (unitSection h F Q x)) =
        ((Scheme.etaleSetPullback (v ≫ h)).obj F).obj.map E.inv.op
          (unitSection (v ≫ h) F Q x) :=
      (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
        S T A.left h v F Q x
    have hn := ConcreteCategory.congr_hom ((c.hom.app F).hom.naturality d'.op)
      (unitSection v H B (unitSection h F Q x))
    change β (((Scheme.etaleSetPullback v).obj H).obj.map d'.op
      (unitSection v H B (unitSection h F Q x))) =
        ((Scheme.etaleSetPullback (v ≫ h)).obj F).obj.map d'.op
          ((c.hom.app F).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj B))
            (unitSection v H B (unitSection h F Q x))) at hn
    rw [hc] at hn
    have hr : sectionPullback F Q p (v ≫ h) hw x =
        β (((Scheme.etaleSetPullback v).obj H).obj.map d'.op
          (unitSection v H B (unitSection h F Q x))) := by
      have hm : E.inv.op ≫ d'.op = d.op := by simp [d', ← op_comp]
      have hf := ((Scheme.etaleSetPullback (v ≫ h)).obj F).obj.map_comp E.inv.op d'.op
      rw [hm] at hf
      exact (ConcreteCategory.congr_hom hf (unitSection (v ≫ h) F Q x)).trans hn.symm
    rw [hr]
    have hinv (y) : inv β (β y) = y := by
      exact ConcreteCategory.congr_hom (IsIso.hom_inv_id β) y
    rw [hinv]
    have hnρ := ConcreteCategory.congr_hom ((ρ.hom.app H).hom.naturality d'.op)
      (unitSection v H B (unitSection h F Q x))
    have hρx : (ρ.hom.app H).hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj B))
        (unitSection v H B (unitSection h F Q x)) =
        H.obj.map ε.op (unitSection h F Q x) :=
      hρ H B (unitSection h F Q x)
    change χ (((Scheme.etaleSetPullback v).obj H).obj.map d'.op
      (unitSection v H B (unitSection h F Q x))) =
        H.obj.map (M.map d').op
          ((ρ.hom.app H).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj B))
            (unitSection v H B (unitSection h F Q x))) at hnρ
    rw [hρx] at hnρ
    have hh : H.obj.map ε.op ≫ H.obj.map (M.map d').op = α := by
      rw [← H.obj.map_comp, ← op_comp, hd]
    exact hnρ.trans (ConcreteCategory.congr_hom hh (unitSection h F Q x))
  constructor
  · intro heq
    apply (CategoryTheory.injective_of_mono (inv β))
    apply hχ
    rw [hsection s, hsection t, heq]
  · intro heq
    apply hα
    rw [← hsection s, ← hsection t, heq]

end AlgebraicGeometry
