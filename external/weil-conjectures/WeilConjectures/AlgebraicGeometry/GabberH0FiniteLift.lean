/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescent
import WeilConjectures.AlgebraicGeometry.GabberH0EtaleInjective
import WeilConjectures.AlgebraicGeometry.GabberH0FiniteSection
import WeilConjectures.AlgebraicGeometry.GabberH0ProjectionRestrictions

/-! # Finite lifts with descent data in Gabber's degree-zero argument

Source: Stacks Project, Tag 09ZF, final proof paragraph before finite descent
(blueprint: lem-weil-pbc-gabber-h0-finite-lift).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem unit_injective_terminal
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
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
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (U : X.Etale) (hU : IsTerminal U) :
    Function.Injective (etaleSetDescentUnit i F U) := by
  let e : Scheme.Etale.mk (𝟙 X) ≅ U :=
    (MorphismProperty.Over.mkIdTerminal @Etale X).uniqueUpToIso hU
  intro s t h
  have hn := etaleSetInverseImageCompositionUnits.1 X Z i F
    U (Scheme.Etale.mk (𝟙 X)) e.hom
  have hEt := (hn s).trans ((congrArg
    (((Scheme.etaleSetPullback i).obj F).obj.map
      ((MorphismProperty.Over.pullback @Etale ⊤ i).map e.hom).op) h).trans (hn t).symm)
  have htop := gabber_h0_etale_injective i hZar F hEt
  have hh := congrArg (F.obj.map e.inv.op) htop
  simpa [← Functor.map_comp_apply, ← op_comp] using hh


/-- A section on Z lifts on a finite surjective cover of X, with equal projection
pullbacks. This stops before descending the section to X.
Source: Stacks Project, Tag 09ZF, final proof paragraph through the equality of the
pullbacks to X' ×_X X' (blueprint: lem-weil-pbc-gabber-h0-finite-lift).

Proof:
1. Every nonempty closed subset of X meets i(Z). Otherwise the pushforward from
   that subset of the constant two-element sheaf has distinct constant global
   sections with equal restrictions to Z. Stalks outside the subset are singletons;
   inverse-image stalks and determination by germs give that equality, contradicting
   hZar. Use `lem-weil-pbc-closed-pushforward-constant-stalks`,
   `lem-weil-pbc-sets-inverse-image-stalk`, and
   `lem-weil-pbc-sheaf-sections-determined-by-germs`.
2. Locally represent t by sections s_j of F on étale X-schemes U_j and maps
   V_j → U_j ×_X Z covering Z. Sheafification gives local representatives;
   filtered-colimit surjectivity lifts them to F(U_j). Use
   `lem-weil-pbc-site-sheafification-sections-local`,
   `lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`,
   `situation-conventions`,
   `situation-conventions`, and
   `lem-weil-pbc-filtered-colimit-sets-elementwise`.
3. The image of V_j in U_j ×_X Z is open since this map is étale. Since
   U_j ×_X Z → U_j is a closed immersion, shrink U_j to an open with precisely
   that intersection. Now V_j surjects onto U_j ×_X Z, and the sheaf axiom gives
   t|_{U_j ×_X Z} = i^*s_j. The union of the images of U_j is open and contains
   i(Z); its closed complement is empty by step 1, so these U_j cover X.
4. `lemma-weil-pbc-finite-refinement-etale-cover` gives a finite surjective h:X' → X
   with an open cover W_alpha mapping to U_j over X. Pull back the s_j to
   s'_alpha on W_alpha and t to t' on Z'. Composition-unit compatibility gives
   equality of their restrictions on W_alpha ×_X Z.
5. The injective Zariski-to-étale comparison for i' makes their Zariski restrictions
   agree on overlaps in Z'. Glue them to a section of the Zariski inverse image.
   hFinite lifts it to a global s' on X'. The comparison-unit equation shows
   that i'^*s' = t'. Transporting both iterated pullbacks to the composite
   inverse image gives exactly the second equality below.
6. Both projection pullbacks of s' restrict to the same pullback of t on the
   closed fibre of X' ×_X X'. This scheme is finite over X (finite base change
   and composition). Apply `lem-weil-pbc-gabber-h0-etale-injective` with hFinite
   for this finite X-scheme. Injectivity gives the first equality below.
   All projection and pasting identifications use
   `lem-weil-pbc-sets-etale-inverse-image-composition-units`.
The witness is only a section on X' satisfying a descent equation; no section on X
is asserted. Empty schemes and identity closed immersions are allowed. -/
theorem gabber_h0_finite_lift
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
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk (𝟙 X))))) :
    ∃ (X' : Scheme.{u}) (h : X' ⟶ X) (_ : IsFinite h) (_ : Surjective h)
      (s' : ((Scheme.etaleSetPullback h).obj F).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj (Scheme.Etale.mk (𝟙 X))))),
      (etaleSetDescentComparison h (pullback.fst h h) F (Scheme.Etale.mk (𝟙 X)) s' =
        eqToHom (congrArg
          (fun k : pullback h h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
              (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := h) (g := h)).symm)
          (etaleSetDescentComparison h (pullback.snd h h) F (Scheme.Etale.mk (𝟙 X)) s')) ∧
      etaleSetDescentComparison i (pullback.fst i h) F (Scheme.Etale.mk (𝟙 X)) t =
        eqToHom (congrArg
          (fun k : pullback i h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
              (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := i) (g := h)).symm)
          (etaleSetDescentComparison h (pullback.snd i h) F (Scheme.Etale.mk (𝟙 X)) s') :=
  by
    obtain ⟨X', h, hh, hsurj, s', hres⟩ := gabber_h0_finite_section i hZar hFinite F t
    let _ : IsFinite h := hh
    let a : pullback h h ⟶ X := pullback.fst h h ≫ h
    let j : pullback i a ⟶ pullback h h := pullback.snd i a
    let G := (Scheme.etaleSetPullback a).obj F
    let U := (MorphismProperty.Over.pullback @Etale ⊤ a).obj (Scheme.Etale.mk (𝟙 X))
    have hU : IsTerminal U :=
      (MorphismProperty.Over.mkIdTerminal @Etale X).isTerminalObj
        (MorphismProperty.Over.pullback @Etale ⊤ a) _
    have hinj := unit_injective_terminal j (hFinite (pullback h h) a) G U hU
    refine ⟨X', h, hh, hsurj, s', ?_, hres⟩
    exact hinj (gabber_h0_projection_restrictions i h F t s' hres)

end AlgebraicGeometry
