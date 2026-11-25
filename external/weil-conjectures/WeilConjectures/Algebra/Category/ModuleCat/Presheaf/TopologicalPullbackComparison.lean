/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Topology.Sheaves.Presheaf

import Mathlib.Algebra.Category.ModuleCat.Stalk
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackRepresentatives

/-!
# Comparison of abstract and concrete topological module pullback

Source: Stacks Project, Sheaves, Tags 008T and 008U.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace PresheafOfModules

set_option backward.isDefEq.respectTransparency false

/-- The canonical abelian comparison to the abstract module pullback is an isomorphism.

Source: Stacks Project, Sheaves, Tags 008T and 008U.
Proof: For each open U, its neighbourhood diagram is filtered: top gives an object,
and intersections give common later objects. Apply Mathlib's `IsColimit.module` to
its ring and abelian diagrams, and `IsColimit.ι_smul` to obtain the coprojection
formula. The pointwise ring colimit remains a colimit after forgetting commutativity.
Represent a scalar and a section at one common neighbourhood. The coprojection
formula and naturality show that restrictions are semilinear, so these sectionwise
modules form a concrete module presheaf M with underlying abelian pullback.

The abelian unit gives a module map G → f_*M: its linearity is the coprojection
formula at f⁻¹(V). Let c be the abelian adjunct of the abstract module unit. On a
coprojection, c is restriction of that unit, by naturality and the adjunction formula.
Thus c is linear, using common representatives, linearity of the module unit and
semilinearity of restriction. Bundle it as cM : M → P(G). The module adjunct of
the concrete unit gives dM : P(G) → M. Apply the module adjunction bijection to show
dM ≫ cM = id, and the abelian adjunction bijection to show c ≫ forget(dM) = id.
Forgetting the first identity supplies the other inverse identity for c. All these
identities use the units, so this is the canonical comparison, not an arbitrary
isomorphism. Empty opens and trivial rings are covered by the same filtered diagrams.
(blueprint: lem-pc-topological-module-pullback-comparison) -/
theorem topologicalModulePullbackComparison {X Y : TopCat.{u}} (f : X ⟶ Y)
    (O : Y.Presheaf CommRingCat.{u}) :
    let R := O ⋙ forget₂ CommRingCat RingCat
    let O' := (TopCat.Presheaf.pullback CommRingCat.{u} f).obj O
    let R' := O' ⋙ forget₂ CommRingCat RingCat
    let iO := Functor.whiskerRight
      ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app O)
      (forget₂ CommRingCat RingCat)
    let P := pullback.{u} (F := Opens.map f) (R := R') iO
    let adj := pullbackPushforwardAdjunction.{u} (F := Opens.map f) (R := R') iO
    ∀ G : PresheafOfModules.{u} R,
      IsIso (((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
        G.presheaf (P.obj G).presheaf).symm
          ((toPresheaf R).map (adj.unit.app G))) := by
  classical
  dsimp only
  intro G
  let R := O ⋙ forget₂ CommRingCat RingCat
  let O' := (TopCat.Presheaf.pullback CommRingCat.{u} f).obj O
  let R' := O' ⋙ forget₂ CommRingCat RingCat
  let iO := Functor.whiskerRight
    ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app O)
    (forget₂ CommRingCat RingCat)
  let P := pullback.{u} (F := Opens.map f) (R := R') iO
  let adj := pullbackPushforwardAdjunction.{u} (F := Opens.map f) (R := R') iO
  let abAdj := TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f
  let A := (TopCat.Presheaf.pullback Ab.{u} f).obj G.presheaf
  let L := (Opens.map f).op
  have hfiltered (W : (Opens X)ᵒᵖ) : IsFiltered (CostructuredArrow L W) :=
    { nonempty := ⟨CostructuredArrow.mk (homOfLE (show W.unop ≤
          (Opens.map f).obj ⊤ from le_top)).op⟩
      cocone_objs := fun j k => by
        have h : W.unop ≤ (Opens.map f).obj (j.left.unop ⊓ k.left.unop) := by
          intro z hz
          exact ⟨j.hom.unop.le hz, k.hom.unop.le hz⟩
        let m : CostructuredArrow L W := CostructuredArrow.mk (homOfLE h).op
        exact ⟨m, CostructuredArrow.homMk (homOfLE inf_le_left).op (by subsingleton),
          CostructuredArrow.homMk (homOfLE inf_le_right).op (by subsingleton), trivial⟩
      cocone_maps := fun j k v w => ⟨k, 𝟙 k, by ext; subsingleton⟩ }
  let pullbackModule (W : (Opens X)ᵒᵖ) : Module (R'.obj W) (A.obj W) := by
    have := hfiltered W
    letI diagramModule (j : CostructuredArrow L W) :
        Module ((CostructuredArrow.proj L W ⋙ R).obj j)
          ((CostructuredArrow.proj L W ⋙ G.presheaf).obj j) :=
      (G.obj j.left).isModule
    exact IsColimit.module (CostructuredArrow.proj L W ⋙ R)
      (CostructuredArrow.proj L W ⋙ G.presheaf)
      (fun v a g => G.map_smul v.left a g)
      (isColimitOfPreserves (forget₂ CommRingCat RingCat)
        (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit O W))
      (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.presheaf W)
  let ι := fun (C : Type (u + 1)) [Category.{u} C] [HasColimits C]
    (B : Y.Presheaf C) (U : Opens X) (V : Opens Y)
    (h : U ≤ (Opens.map f).obj V) =>
      ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app B).app (op V) ≫
        ((TopCat.Presheaf.pullback C f).obj B).map (homOfLE h).op
  have hsmul (U : Opens X) (V : Opens Y) (h : U ≤ (Opens.map f).obj V)
      (a : O.obj (op V)) (g : G.obj (op V)) :
      (ι Ab.{u} G.presheaf U V h).hom (a • g) =
        @SMul.smul (O'.obj (op U)) (A.obj (op U))
          (pullbackModule (op U)).toSMul ((ι CommRingCat.{u} O U V h).hom a)
            ((ι Ab.{u} G.presheaf U V h).hom g) := by
    have := hfiltered (op U)
    let diagramModule (j : CostructuredArrow L (op U)) :
        Module ((CostructuredArrow.proj L (op U) ⋙ R).obj j)
          ((CostructuredArrow.proj L (op U) ⋙ G.presheaf).obj j) :=
      (G.obj j.left).isModule
    exact IsColimit.ι_smul (CostructuredArrow.proj L (op U) ⋙ R)
      (CostructuredArrow.proj L (op U) ⋙ G.presheaf)
      (fun v a g => G.map_smul v.left a g)
      (isColimitOfPreserves (forget₂ CommRingCat RingCat)
        (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit O (op U)))
      (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.presheaf (op U))
      (CostructuredArrow.mk (homOfLE h).op) a g
  have hrestrict (C : Type (u + 1)) [Category.{u} C] [HasColimits C]
      (B : Y.Presheaf C) (U W : Opens X) (V : Opens Y)
      (h : U ≤ (Opens.map f).obj V) (k : W ⟶ U) :
      ι C B U V h ≫ ((TopCat.Presheaf.pullback C f).obj B).map k.op =
        ι C B W V (k.le.trans h) := by
    dsimp only [ι]
    rw [Category.assoc, ← Functor.map_comp]
    congr 2
  have hsemi : ∀ {U W : (Opens X)ᵒᵖ} (k : U ⟶ W) (a : R'.obj U) (g : A.obj U),
      A.map k (a • g) = R'.map k a • A.map k g := by
    intro U W k a g
    obtain ⟨V, h, b, t, hb, ht⟩ :=
      topologicalPullbackCommonRepresentatives f O G.presheaf U.unop a g
    change (ι CommRingCat.{u} O U.unop V h).hom b = a at hb
    change (ι Ab.{u} G.presheaf U.unop V h).hom t = g at ht
    subst a
    subst g
    have hr := ConcreteCategory.congr_hom
      (hrestrict CommRingCat.{u} O U.unop W.unop V h k.unop) b
    have hg := ConcreteCategory.congr_hom
      (hrestrict Ab.{u} G.presheaf U.unop W.unop V h k.unop) t
    calc
      _ = A.map k ((ι Ab.{u} G.presheaf U.unop V h).hom (@SMul.smul (R.obj (op V)) (G.obj (op V))
          (G.obj (op V)).isModule.toSMul b t)) :=
        congrArg (fun z => A.map k z) (hsmul U.unop V h b t).symm
      _ = (ι Ab.{u} G.presheaf W.unop V (k.unop.le.trans h)).hom
          (@SMul.smul (R.obj (op V)) (G.obj (op V))
          (G.obj (op V)).isModule.toSMul b t) :=
        ConcreteCategory.congr_hom
          (hrestrict Ab.{u} G.presheaf U.unop W.unop V h k.unop)
          (@SMul.smul (R.obj (op V)) (G.obj (op V))
          (G.obj (op V)).isModule.toSMul b t)
      _ = @SMul.smul (R'.obj W) (A.obj W) (pullbackModule W).toSMul
          ((ι CommRingCat.{u} O W.unop V (k.unop.le.trans h)).hom b)
          ((ι Ab.{u} G.presheaf W.unop V (k.unop.le.trans h)).hom t) :=
        hsmul W.unop V (k.unop.le.trans h) b t
      _ = _ := congrArg₂ (fun (r : R'.obj W) (z : A.obj W) => r • z) hr.symm hg.symm
  let M : PresheafOfModules.{u} R' := ofPresheaf A @hsemi
  have huLinear (V : Opens Y) (a : R.obj (op V)) (g : G.obj (op V)) :
      ((abAdj.unit.app G.presheaf).app (op V)).hom (a • g) =
        @SMul.smul (R'.obj (op ((Opens.map f).obj V)))
          (A.obj (op ((Opens.map f).obj V)))
          (pullbackModule (op ((Opens.map f).obj V))).toSMul
          ((iO.app (op V)).hom a) (((abAdj.unit.app G.presheaf).app (op V)).hom g) := by
    have hh := hsmul ((Opens.map f).obj V) V le_rfl a g
    have hiA : ι Ab.{u} G.presheaf ((Opens.map f).obj V) V le_rfl =
        (abAdj.unit.app G.presheaf).app (op V) := by
      change (abAdj.unit.app G.presheaf).app (op V) ≫ A.map (𝟙 _) = _
      exact (congrArg (fun t => (abAdj.unit.app G.presheaf).app (op V) ≫ t)
        (A.map_id _)).trans (Category.comp_id _)
    have hiR : ι CommRingCat.{u} O ((Opens.map f).obj V) V le_rfl =
        ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app
          O).app (op V) := by
      change ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app
        O).app (op V) ≫ O'.map (𝟙 _) = _
      exact (congrArg (fun t =>
        ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app
          O).app (op V) ≫ t) (O'.map_id _)).trans (Category.comp_id _)
    rw [hiA, hiR] at hh
    exact hh
  let unitM : G ⟶ (pushforward (F := Opens.map f) (R := R') (S := R) iO).obj M :=
    homMk (abAdj.unit.app G.presheaf) (fun V a g => huLinear V.unop a g)
  let c := (abAdj.homEquiv G.presheaf (P.obj G).presheaf).symm
    ((toPresheaf R).map (adj.unit.app G))
  have hcunit (V : Opens Y) (g : G.obj (op V)) :
      (c.app (op ((Opens.map f).obj V))).hom
          (((abAdj.unit.app G.presheaf).app (op V)).hom g) =
        ((adj.unit.app G).app (op V)).hom g := by
    have hc := (abAdj.homEquiv G.presheaf (P.obj G).presheaf).apply_symm_apply
      ((toPresheaf R).map (adj.unit.app G))
    rw [abAdj.homEquiv_unit] at hc
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hc (op V)) g
  have hciota (U : Opens X) (V : Opens Y) (h : U ≤ (Opens.map f).obj V)
      (g : G.obj (op V)) :
      (c.app (op U)).hom ((ι Ab.{u} G.presheaf U V h).hom g) =
        ((P.obj G).map (homOfLE h).op).hom
          (((adj.unit.app G).app (op V)).hom g) := by
    have hn := ConcreteCategory.congr_hom (c.naturality (homOfLE h).op)
      (((abAdj.unit.app G.presheaf).app (op V)).hom g)
    exact hn.trans (congrArg ((P.obj G).map (homOfLE h).op).hom (hcunit V g))
  have hcLinear (U : (Opens X)ᵒᵖ) (a : R'.obj U) (g : M.obj U) :
      (c.app U).hom (a • g) = a • (c.app U).hom g := by
    obtain ⟨V, h, b, t, hb, ht⟩ :=
      topologicalPullbackCommonRepresentatives f O G.presheaf U.unop a g
    change (ι CommRingCat.{u} O U.unop V h).hom b = a at hb
    change (ι Ab.{u} G.presheaf U.unop V h).hom t = g at ht
    subst a
    subst g
    have hlin := ((adj.unit.app G).app (op V)).hom.map_smul b t
    have hres := (P.obj G).map_smul (homOfLE h).op
      (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app
        O).app (op V) b) (((adj.unit.app G).app (op V)).hom t)
    calc
      _ = (c.app U).hom ((ι Ab.{u} G.presheaf U.unop V h).hom
          (@SMul.smul (R.obj (op V)) (G.obj (op V))
            (G.obj (op V)).isModule.toSMul b t)) :=
        congrArg (c.app U).hom (hsmul U.unop V h b t).symm
      _ = ((P.obj G).map (homOfLE h).op).hom
          (((adj.unit.app G).app (op V)).hom
            (@SMul.smul (R.obj (op V)) (G.obj (op V))
              (G.obj (op V)).isModule.toSMul b t)) := hciota U.unop V h _
      _ = _ := (congrArg ((P.obj G).map (homOfLE h).op).hom hlin).trans
          (hres.trans (congrArg
            (fun (z : (P.obj G).obj U) =>
              (ι CommRingCat.{u} O U.unop V h).hom b • z)
            (hciota U.unop V h t).symm))
  let cM : M ⟶ P.obj G := homMk c hcLinear
  let dM : P.obj G ⟶ M := (adj.homEquiv G M).symm unitM
  have huc : unitM ≫
      (pushforward (F := Opens.map f) (R := R') (S := R) iO).map cM = adj.unit.app G := by
    apply (toPresheaf R).map_injective
    change abAdj.unit.app G.presheaf ≫
      (TopCat.Presheaf.pushforward Ab.{u} f).map c = _
    exact (abAdj.homEquiv_unit G.presheaf (P.obj G).presheaf c).symm.trans
      ((abAdj.homEquiv G.presheaf (P.obj G).presheaf).apply_symm_apply
        ((toPresheaf R).map (adj.unit.app G)))
  have hdc : dM ≫ cM = 𝟙 (P.obj G) := by
    apply (adj.homEquiv G (P.obj G)).injective
    exact (adj.homEquiv_naturality_right dM cM).trans
      ((congrArg (fun t => t ≫ (pushforward (F := Opens.map f) (R := R') (S := R) iO).map cM)
        ((adj.homEquiv G M).apply_symm_apply unitM)).trans
          (huc.trans (adj.homEquiv_id G).symm))
  have hd : adj.unit.app G ≫
      (pushforward (F := Opens.map f) (R := R') (S := R) iO).map dM = unitM := by
    exact (adj.homEquiv_unit G M dM).symm.trans
      ((adj.homEquiv G M).apply_symm_apply unitM)
  have hcd : c ≫ (toPresheaf R').map dM = 𝟙 A := by
    apply (abAdj.homEquiv G.presheaf A).injective
    have hd' := congrArg ((toPresheaf R).map) hd
    have hdf : (toPresheaf R).map (adj.unit.app G) ≫
        (TopCat.Presheaf.pushforward Ab.{u} f).map ((toPresheaf R').map dM) =
          abAdj.unit.app G.presheaf := by
      apply TopCat.Presheaf.ext
      intro V
      ext g
      exact ConcreteCategory.congr_hom (NatTrans.congr_app hd' (op V)) g
    exact (abAdj.homEquiv_naturality_right c ((toPresheaf R').map dM)).trans
      ((congrArg (fun t => t ≫
        (TopCat.Presheaf.pushforward Ab.{u} f).map ((toPresheaf R').map dM))
          ((abAdj.homEquiv G.presheaf (P.obj G).presheaf).apply_symm_apply
            ((toPresheaf R).map (adj.unit.app G)))).trans
              (hdf.trans (abAdj.homEquiv_id G.presheaf).symm))
  exact ⟨⟨(toPresheaf R').map dM, hcd, by
    exact ((toPresheaf R').map_comp dM cM).symm.trans
      ((congrArg ((toPresheaf R').map) hdc).trans
        ((toPresheaf R').map_id (P.obj G)))⟩⟩

end PresheafOfModules
