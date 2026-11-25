/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescent
import WeilConjectures.AlgebraicGeometry.GabberH0EtaleInjective
import WeilConjectures.AlgebraicGeometry.GabberH0FiniteLift
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Gabber's degree-zero criterion for etale sheaves of sets

Source: Stacks Project, Lemma 59.82.2 (Tag 09ZF)
(blueprint: lem-weil-pbc-gabber-h0-etale-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem comparison_unit {X Y W : Scheme.{u}}
    (f : Y ⟶ X) (g : W ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (s : F.obj.obj (op U)) :
    etaleSetDescentComparison f g F U (etaleSetDescentUnit f F U s) =
      etaleSetDescentUnit (g ≫ f) F U s := by
  have h := (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
    X Y W f g F U s
  unfold etaleSetDescentComparison
  erw [h]
  simp [etaleSetDescentUnit, ← Functor.map_comp_apply, ← op_comp]

private theorem unit_injective_terminal {Y W : Scheme.{u}}
    (g : W ⟶ Y) [IsFinite g] [Surjective g]
    (G : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (U : Y.Etale) (hU : IsTerminal U) :
    Function.Injective (etaleSetDescentUnit g G U) := by
  let e : U ≅ Scheme.Etale.mk (𝟙 Y) :=
    hU.uniqueUpToIso (MorphismProperty.Over.mkIdTerminal @Etale Y)
  intro s t h
  have he : G.obj.map e.inv.op s = G.obj.map e.inv.op t := by
    apply (finiteSurjectiveSetDescent g G).1
    have hn := etaleSetInverseImageCompositionUnits.1 Y W g G U
      (Scheme.Etale.mk (𝟙 Y)) e.inv
    change _ = _
    rw [show etaleSetDescentUnit g G (Scheme.Etale.mk (𝟙 Y))
      (G.obj.map e.inv.op s) = _ from hn s]
    rw [show etaleSetDescentUnit g G (Scheme.Etale.mk (𝟙 Y))
      (G.obj.map e.inv.op t) = _ from hn t]
    exact congrArg
      (((Scheme.etaleSetPullback g).obj G).obj.map
        ((MorphismProperty.Over.pullback @Etale ⊤ g).map e.inv).op) h
  have he' := congrArg (G.obj.map e.hom.op) he
  simpa [← Functor.map_comp_apply, ← op_comp] using he'

private theorem comparison_injective {X Y W : Scheme.{u}}
    (f : Y ⟶ X) (g : W ⟶ Y) [IsFinite g] [Surjective g]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    Function.Injective (etaleSetDescentComparison f g F (Scheme.Etale.mk (𝟙 X))) := by
  let U := (MorphismProperty.Over.pullback @Etale ⊤ f).obj (Scheme.Etale.mk (𝟙 X))
  have hU : IsTerminal U :=
    (MorphismProperty.Over.mkIdTerminal @Etale X).isTerminalObj
      (MorphismProperty.Over.pullback @Etale ⊤ f) _
  have hi := unit_injective_terminal g ((Scheme.etaleSetPullback f).obj F) U hU
  intro s t h
  apply hi
  let c := ((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
    X Y W f g).app F
  let e := ((Scheme.etaleSetPullback (g ≫ f)).obj F).obj.mapIso
    (((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).app
      (Scheme.Etale.mk (𝟙 X))).op)
  have h₁ := congrArg e.inv h
  have h₂ :
      c.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj U))
        (etaleSetDescentUnit g ((Scheme.etaleSetPullback f).obj F) U s) =
      c.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj U))
        (etaleSetDescentUnit g ((Scheme.etaleSetPullback f).obj F) U t) := by
    simpa [c, U, e, etaleSetDescentComparison, ← Functor.map_comp_apply, ← op_comp] using h₁
  let d := (sheafToPresheaf _ _).mapIso c
  have h₃ := congrArg (d.inv.app
    (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj U))) h₂
  simpa [d, ← NatTrans.comp_app, ← types_comp_apply] using h₃


private theorem unit_transport {X W : Scheme.{u}} (a b : W ⟶ X) (e : a = b)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (s : F.obj.obj (op U)) :
    eqToHom (congrArg
      (fun k : W ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj U))) e)
      (etaleSetDescentUnit a F U s) = etaleSetDescentUnit b F U s := by
  subst b
  rfl

/-- If Zariski restriction to a closed subscheme is bijective on sections for every
set-valued sheaf, and remains so after every finite base change, then etale restriction
is bijective on sections for every set-valued sheaf. Source: Stacks Project, Lemma 59.82.2
(Tag 09ZF) (blueprint: lem-weil-pbc-gabber-h0-etale-criterion).

Proof:
0. Use the inverse-image units and their composition isomorphisms from
`lem-weil-pbc-sets-etale-inverse-image-composition-units`. After a finite base change,
closed immersions, finiteness and surjectivity persist by
`lem-weil-pbc-closed-immersion-base-change`, `lem-weil-pbc-finite-morphism-permanence`
and `lem-weil-pbc-surjective-base-change`; the identity is finite.
1. By `lem-weil-pbc-gabber-zariski-etale-restriction-injective`, Zariski restriction
followed by the comparison injection is etale restriction. The two hypotheses therefore
give injectivity on X and on every finite X' over X.
2. Every nonempty closed subset meets Z: otherwise its pushforward constant two-element
sheaf has two distinct global sections whose restrictions agree. Use
`lem-weil-pbc-closed-pushforward-constant-stalks`,
`lem-weil-pbc-sets-inverse-image-stalk`, and
`lem-weil-pbc-sheaf-sections-determined-by-germs`.
3. A section t of the inverse image is locally represented by sections s_j on etale
X-schemes U_j and maps V_j to U_j over X, with V_j covering Z. Use
`lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`,
`lem-weil-pbc-site-sheafification-sections-local`,
`situation-conventions`,
`situation-conventions`, and
`lem-weil-pbc-filtered-colimit-sets-elementwise`.
4. Shrink U_j to make V_j surjective over U_j times Z. This uses openness of etale
morphisms and the subspace topology of a closed immersion. The sheaf condition then
gives equality of t with the pullback of s_j on all of U_j times Z. Use
`definition-torsion-sheaves--3`, `lem-weil-pbc-etale-morphism-open-map`,
and `situation-conventions`.
5. The union of the images of U_j is open and contains Z, so its closed complement
is empty by step 2. Thus their disjoint union covers X; use
`lem-weil-pbc-etale-local-on-source`.
6. Apply `lemma-weil-pbc-finite-refinement-etale-cover` to obtain a finite surjective
X' over X and an open covering W_alpha of X' mapping into the U_j over X.
7. Pull back the s_j to sections s'_alpha on W_alpha and t to t' on Z'. The composition
isomorphisms and unit compatibilities identify their restrictions to W_alpha times Z.
8. The comparison injection of step 1 makes the Zariski restrictions of s'_alpha
agree on overlaps in Z'. They glue to a Zariski inverse-image section sigma. The finite
base-change hypothesis lifts sigma to a global s' on X', whose restriction is t'.
9. The two pullbacks of s' to X' times X' agree after restriction to Z' times Z',
by compatibility of the inverse-image units. Injectivity from step 1 for this finite
X-scheme makes them equal; finiteness uses `lem-weil-pbc-finite-composition`.
10. By `lem-weil-pbc-sets-finite-surjective-descent`, s' descends to a section s on X.
Its restriction is t: their pullbacks to Z' agree by step 8 and unit compatibility,
and restriction along the finite surjection Z' to Z is injective by the same descent
lemma. This proves surjectivity and hence bijectivity.

The unit is evaluated at the terminal etale X-object. Its base change is terminal over
Z, canonically isomorphic to Z itself, so its sections are global sections on Z. -/
theorem gabber_h0_etale_criterion
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hZar :
      letI : ∀ P : X.Opensᵒᵖ ⥤ Type (u + 1),
          (Opens.map (i.base : Z.toTopCat ⟶ X.toTopCat)).op.HasPointwiseLeftKanExtension P :=
            fun P U ↦
              @Types.hasColimit.{u, u + 1, u}
                (CostructuredArrow.{u, u, u, u} (Opens.map i.base).op U)
                inferInstance (small_succ.{u} _) (CostructuredArrow.proj _ U ⋙ P)
      ∀ G : TopCat.Sheaf (Type (u + 1)) X.toTopCat,
      Function.Bijective
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map (i.base : Z.toTopCat ⟶ X.toTopCat)) (Type (u + 1))
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).unit.app G).hom.app
            (op (⊤ : X.Opens))))
    (hFinite : ∀ (X' : Scheme.{u}) (h : X' ⟶ X) [IsFinite h],
      let b : CategoryTheory.Functor.{u, u, u, u} X'.Opens (pullback i h : Scheme.{u}).Opens :=
        Opens.map
        ((pullback.snd i h : (pullback i h : Scheme.{u}) ⟶ X').base)
      letI : ∀ P : X'.Opensᵒᵖ ⥤ Type (u + 1), b.op.HasPointwiseLeftKanExtension P :=
        fun P U ↦
          @Types.hasColimit.{u, u + 1, u} (CostructuredArrow.{u, u, u, u} b.op U)
            inferInstance (small_succ.{u} _) (CostructuredArrow.proj b.op U ⋙ P)
      ∀ G : TopCat.Sheaf (Type (u + 1)) X'.toTopCat,
        Function.Bijective
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            b (Type (u + 1)) (Opens.grothendieckTopology X')
            (Opens.grothendieckTopology (pullback i h : Scheme.{u}))).unit.app G).hom.app
              (op (⊤ : X'.Opens))))
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    let adj : Scheme.etaleSetPullback i ⊣
        (MorphismProperty.Over.pullback @Etale ⊤ i).sheafPushforwardContinuous
          (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
          (Z.smallGrothendieckTopology @Etale) :=
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
        (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)
    Function.Bijective ((adj.unit.app F).hom.app (op (Scheme.Etale.mk (𝟙 X)))) := by
  change Function.Bijective (etaleSetDescentUnit i F (Scheme.Etale.mk (𝟙 X)))
  refine ⟨gabber_h0_etale_injective i hZar F, ?_⟩
  intro t
  obtain ⟨X', h, hh, hsurj, s', heq, hres⟩ := gabber_h0_finite_lift i hZar hFinite F t
  let : IsFinite h := hh
  let : Surjective h := hsurj
  obtain ⟨s, hs⟩ := ((finiteSurjectiveSetDescent h F).2 s').mp heq
  refine ⟨s, ?_⟩
  apply comparison_injective i (pullback.fst i h) F
  have hc := (comparison_unit h (pullback.snd i h) F (Scheme.Etale.mk (𝟙 X)) s).symm
  have hr := hc.trans (congrArg
    (etaleSetDescentComparison h (pullback.snd i h) F (Scheme.Etale.mk (𝟙 X))) hs)
  have hr' := congrArg (eqToHom (congrArg
    (fun k : pullback i h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj (Scheme.Etale.mk (𝟙 X)))))
    (pullback.condition (f := i) (g := h)).symm)) hr
  exact (comparison_unit i (pullback.fst i h) F _ s).trans
    ((unit_transport _ _ (pullback.condition (f := i) (g := h)).symm F _ s).symm.trans
      (hr'.trans hres.symm))

end AlgebraicGeometry
