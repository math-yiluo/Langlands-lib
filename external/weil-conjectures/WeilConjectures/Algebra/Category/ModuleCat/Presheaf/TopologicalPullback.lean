/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Topology.Sheaves.Presheaf

import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackComparison
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackRepresentatives

/-!
# Pullback of presheaves of modules along a continuous map

Source: Stacks Project, Sheaves, Tags 008T, 008S and 008U
(blueprint: lem-pc-presheaf-module-inverse-image-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace PresheafOfModules

/-- The section map from an open neighbourhood of `f(U)` into the presheaf pullback.
Source: Stacks Project, Sheaves, Tag 008T
(blueprint: lem-pc-presheaf-module-inverse-image-adjunction). -/
noncomputable def topologicalPullbackSectionMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (C : Type (u + 1)) [Category.{u} C] [HasColimits C] (G : Y.Presheaf C)
    (U : Opens X) (V : Opens Y) (h : U ≤ (Opens.map f).obj V) :
    G.obj (op V) ⟶ ((TopCat.Presheaf.pullback C f).obj G).obj (op U) :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app G).app (op V) ≫
    ((TopCat.Presheaf.pullback C f).obj G).map (homOfLE h).op

/-- For a continuous map `f`, an `O`-module presheaf `G` pulls back sectionwise to a
module over the colimit ring presheaf. The action on sections is uniquely specified by
the coprojection formula. Direct image restricts scalars through the ring-presheaf unit.
The abelian-presheaf adjunction then restricts to an adjunction of module presheaves,
natural in both variables.

Proof (Stacks, Tags 008T, 008S, 008U): the neighbourhoods of `f(U)` form a filtered
category. Filtered-colimit representatives give a common neighbourhood for finitely
many ring and module sections, so the sectionwise multiplication is uniquely determined
and independent of representatives. The module laws, semilinear restrictions, and
linearity of pulled-back maps follow at that common neighbourhood. Direct image uses
restriction of scalars along the ring-presheaf unit. The abelian adjunction sends a
map `ψ` to `f_*ψ ∘ i_G`; the unit is linear, and the converse follows by checking
linearity on colimit representatives. These checks are compatible with both variables.
(blueprint: lem-pc-presheaf-module-inverse-image-adjunction) -/
def topologicalPullbackAdjunctionSpec {X Y : TopCat.{u}} (f : X ⟶ Y)
    (O : Y.Presheaf CommRingCat.{u}) : Prop :=
    let R := O ⋙ forget₂ CommRingCat RingCat
    let O' := (TopCat.Presheaf.pullback CommRingCat.{u} f).obj O
    let R' := O' ⋙ forget₂ CommRingCat RingCat
    let iO := Functor.whiskerRight
      ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app O)
      (forget₂ CommRingCat RingCat)
    ∃ P : PresheafOfModules.{u} R ⥤ PresheafOfModules.{u} R',
    ∃ e : P ⋙ toPresheaf R' ≅
        toPresheaf R ⋙ TopCat.Presheaf.pullback Ab.{u} f,
    ∃ adj : P ⊣ pushforward iO,
      (∀ (G : PresheafOfModules.{u} R) (U : Opens X) (V : Opens Y)
          (h : U ≤ (Opens.map f).obj V) (a : O.obj (op V)) (g : G.obj (op V)),
        let ringι := topologicalPullbackSectionMap f CommRingCat.{u} O U V h
        let groupι := topologicalPullbackSectionMap f Ab.{u} G.presheaf U V h
        letI : Module (R'.obj (op U)) ((P.obj G).obj (op U)) :=
          ((P.obj G).obj (op U)).isModule
        @SMul.smul (R'.obj (op U)) ((P.obj G).obj (op U))
            ((P.obj G).obj (op U)).isModule.toSMul (ringι.hom a)
            (((e.app G).inv.app (op U)).hom (groupι.hom g)) =
          ((e.app G).inv.app (op U)).hom (groupι.hom (a • g))) ∧
      (∀ (G : PresheafOfModules.{u} R) (U : Opens X),
        ∃! μ : O'.obj (op U) →
            ((TopCat.Presheaf.pullback Ab.{u} f).obj G.presheaf).obj (op U) →
            ((TopCat.Presheaf.pullback Ab.{u} f).obj G.presheaf).obj (op U),
          ∀ (V : Opens Y) (h : U ≤ (Opens.map f).obj V)
              (a : O.obj (op V)) (g : G.obj (op V)),
            μ ((topologicalPullbackSectionMap f CommRingCat.{u} O U V h).hom a)
                ((topologicalPullbackSectionMap f Ab.{u} G.presheaf U V h).hom g) =
              (topologicalPullbackSectionMap f Ab.{u} G.presheaf U V h).hom (a • g)) ∧
      (∀ (G : PresheafOfModules.{u} R) (F : PresheafOfModules.{u} R')
          (ψ : P.obj G ⟶ F),
        (toPresheaf R).map ((adj.homEquiv G F) ψ) =
          (TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
            G.presheaf F.presheaf
            ((e.app G).inv ≫ (toPresheaf R').map ψ))

/-- The concrete presheaf-module pullback and its adjunction, as specified by
`topologicalPullbackAdjunctionSpec`.

Source: Stacks Project, Sheaves, Tags 008T, 008S, 008U.
Proof: Use Mathlib's abstract module pullback and its adjunction. Its forgotten unit
has a canonical abelian adjunct. `topologicalModulePullbackComparison` proves that
this comparison is an isomorphism. Naturality of the two Hom equivalences makes these
comparisons natural in G; taking their inverses gives the required natural isomorphism e.
The abelian adjunction identity gives the unit formula for e. Naturality then expresses
the image of a coprojection under e⁻¹ as restriction of the module unit. Linearity of
that unit and semilinearity of restriction prove the scalar-action formula.

Transport the existing action on P(G)(U) through e to obtain a multiplication on the
abelian pullback. Its coprojection formula follows from the scalar-action formula and
the inverse identities. `topologicalPullbackCommonRepresentatives` represents any scalar
and section at one common neighbourhood, so that formula uniquely determines the action.
Finally, expand both Hom equivalences as composition with their units. The established
unit formula makes their underlying abelian maps equal. This proves the required Hom
formula with the module adjunction already supplied by Mathlib.
(blueprint: lem-pc-presheaf-module-inverse-image-adjunction) -/
theorem topologicalPullbackAdjunction {X Y : TopCat.{u}} (f : X ⟶ Y)
    (O : Y.Presheaf CommRingCat.{u}) :
    topologicalPullbackAdjunctionSpec f O := by
  classical
  let R := O ⋙ forget₂ CommRingCat RingCat
  let O' := (TopCat.Presheaf.pullback CommRingCat.{u} f).obj O
  let R' := O' ⋙ forget₂ CommRingCat RingCat
  let iO := Functor.whiskerRight
    ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app O)
    (forget₂ CommRingCat RingCat)
  let P := pullback.{u} (F := Opens.map f) (R := R') iO
  let adj := pullbackPushforwardAdjunction.{u} (F := Opens.map f) (R := R') iO
  let abAdj := TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f
  let c : toPresheaf R ⋙ TopCat.Presheaf.pullback Ab.{u} f ⟶ P ⋙ toPresheaf R' :=
    { app := fun G => (abAdj.homEquiv G.presheaf (P.obj G).presheaf).symm
        ((toPresheaf R).map (adj.unit.app G))
      naturality := fun {G H} v => by
        dsimp only [Functor.comp_map]
        have hn := congrArg ((toPresheaf R).map) (adj.unit.naturality v)
        have hn' : (toPresheaf R).map v ≫ (toPresheaf R).map (adj.unit.app H) =
            (toPresheaf R).map (adj.unit.app G) ≫
              (TopCat.Presheaf.pushforward Ab.{u} f).map
                ((toPresheaf R').map (P.map v)) := by
          apply TopCat.Presheaf.ext
          intro V
          ext g
          exact ConcreteCategory.congr_hom (NatTrans.congr_app hn (op V)) g
        exact (abAdj.homEquiv_naturality_left_symm (Y := (P.obj H).presheaf)
          ((toPresheaf R).map v)
          ((toPresheaf R).map (adj.unit.app H))).symm.trans
            ((congrArg (abAdj.homEquiv G.presheaf (P.obj H).presheaf).symm hn').trans
              (abAdj.homEquiv_naturality_right_symm (X := G.presheaf)
                (Y := (P.obj G).presheaf) (Y' := (P.obj H).presheaf)
                ((toPresheaf R).map (adj.unit.app G)) ((toPresheaf R').map (P.map v)))) }
  have : ∀ G, IsIso (c.app G) := topologicalModulePullbackComparison f O
  have : IsIso c := NatIso.isIso_of_isIso_app c
  let e := (asIso c).symm
  have hunit (G : PresheafOfModules.{u} R) (V : Opens Y) (g : G.obj (op V)) :
      ((e.app G).inv.app (op ((Opens.map f).obj V))).hom
          (((abAdj.unit.app G.presheaf).app (op V)).hom g) =
        ((adj.unit.app G).app (op V)).hom g := by
    have hc := (abAdj.homEquiv G.presheaf (P.obj G).presheaf).apply_symm_apply
      ((toPresheaf R).map (adj.unit.app G))
    rw [abAdj.homEquiv_unit] at hc
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hc (op V)) g
  have hι (G : PresheafOfModules.{u} R) (U : Opens X) (V : Opens Y)
      (h : U ≤ (Opens.map f).obj V) (g : G.obj (op V)) :
      ((e.app G).inv.app (op U)).hom
          ((topologicalPullbackSectionMap f Ab.{u} G.presheaf U V h).hom g) =
        ((P.obj G).map (homOfLE h).op).hom
          (((adj.unit.app G).app (op V)).hom g) := by
    have hn := ConcreteCategory.congr_hom
      ((e.app G).inv.naturality (homOfLE h).op)
      ((((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).unit.app
        G.presheaf).app (op V)).hom g)
    exact hn.trans (congrArg ((P.obj G).map (homOfLE h).op).hom (hunit G V g))
  have haction (G : PresheafOfModules.{u} R) (U : Opens X) (V : Opens Y)
      (h : U ≤ (Opens.map f).obj V) (a : O.obj (op V)) (g : G.obj (op V)) :
      @SMul.smul (R'.obj (op U)) ((P.obj G).obj (op U))
          ((P.obj G).obj (op U)).isModule.toSMul
          ((topologicalPullbackSectionMap f CommRingCat.{u} O U V h).hom a)
          (((e.app G).inv.app (op U)).hom
            ((topologicalPullbackSectionMap f Ab.{u} G.presheaf U V h).hom g)) =
        ((e.app G).inv.app (op U)).hom
          ((topologicalPullbackSectionMap f Ab.{u} G.presheaf U V h).hom (a • g)) := by
    have hlin := ((adj.unit.app G).app (op V)).hom.map_smul a g
    have hres := (P.obj G).map_smul (homOfLE h).op
      (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app
        O).app (op V) a) (((adj.unit.app G).app (op V)).hom g)
    rw [hι G U V h g, hι G U V h (a • g)]
    exact hres.symm.trans (congrArg ((P.obj G).map (homOfLE h).op).hom hlin.symm)
  refine ⟨P, e, adj, haction, ?_, ?_⟩
  · intro G U
    let E := (e.app G).app (op U)
    let μ := fun (a : O'.obj (op U))
      (g : ((TopCat.Presheaf.pullback Ab.{u} f).obj G.presheaf).obj (op U)) =>
        E.hom.hom (@SMul.smul (R'.obj (op U)) ((P.obj G).obj (op U))
          ((P.obj G).obj (op U)).isModule.toSMul a (E.inv.hom g))
    have hμ : ∀ (V : Opens Y) (h : U ≤ (Opens.map f).obj V)
        (a : O.obj (op V)) (g : G.obj (op V)),
        μ ((topologicalPullbackSectionMap f CommRingCat.{u} O U V h).hom a)
          ((topologicalPullbackSectionMap f Ab.{u} G.presheaf U V h).hom g) =
            (topologicalPullbackSectionMap f Ab.{u} G.presheaf U V h).hom (a • g) := by
      intro V h a g
      dsimp only [μ]
      have hh := congrArg E.hom.hom (haction G U V h a g)
      exact hh.trans (E.inv_hom_id_apply _)
    refine ⟨μ, hμ, ?_⟩
    intro ν hν
    funext a g
    obtain ⟨V, h, b, t, hb, ht⟩ :=
      topologicalPullbackCommonRepresentatives f O G.presheaf U a g
    change (topologicalPullbackSectionMap f CommRingCat.{u} O U V h).hom b = a at hb
    change (topologicalPullbackSectionMap f Ab.{u} G.presheaf U V h).hom t = g at ht
    rw [← hb, ← ht, hν V h b t, hμ V h b t]
  · intro G F ψ
    rw [adj.homEquiv_unit,
      (TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv_unit]
    apply TopCat.Presheaf.ext
    intro V
    ext g
    change (ψ.app (op ((Opens.map f).obj V))).hom
        (((adj.unit.app G).app (op V)).hom g) =
      (ψ.app (op ((Opens.map f).obj V))).hom
        (((e.app G).inv.app (op ((Opens.map f).obj V))).hom
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).unit.app
            G.presheaf).app (op V)).hom g))
    exact congrArg (ψ.app (op ((Opens.map f).obj V))).hom (hunit G V g).symm

end PresheafOfModules
