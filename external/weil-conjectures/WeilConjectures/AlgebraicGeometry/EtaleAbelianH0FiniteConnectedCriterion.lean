/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.GabberH0EtaleCriterion
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.ZariskiClosedImmersionConnectedRestriction

/-!
# A finite-cover connectedness criterion for abelian étale sections

Source: Stacks Project, Tags 09ZG and 09ZF.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Abelian étale sections restrict isomorphically to a closed subscheme when every
irreducible closed subset of every finite cover meets it in a nonempty connected set.

Source: Stacks Project, Lemmas 59.82.4 and 59.82.2 (Tags 09ZG and 09ZF).
(blueprint: lem-weil-pbc-etale-abelian-h0-finite-connected-criterion)

Proof:
1. Every finite scheme X' over the qcqs scheme X is qcqs and spectral. The base
   change of the closed immersion i is closed and has image h inverse image of
   range i. The hypothesis and Tag 09ZG give bijective restriction of sections
   of every Zariski sheaf of sets on X'. The identity finite cover includes X.
2. Apply Gabber's Tag 09ZF criterion: these Zariski comparisons on X and all
   finite X' imply bijective restriction of sections of every étale sheaf of sets.
3. Apply this to the underlying sheaf of sets of G. Forgetting abelian groups
   preserves limits and filtered colimits. The pointwise inverse-image colimits
   and the local matching families defining sheafification are therefore the
   same after forgetting groups. The natural comparison respects the adjunction
   units, and the terminal base-change comparison identifies their global sections.
4. Thus the underlying function of globalSectionsUpperStarMap is the bijection
   of step 2, conjugated by canonical bijections. A bijective homomorphism of
   abelian groups has an additive inverse, so it is an isomorphism.

The universe of the underlying sets is u+1. This is independent of any henselian
pair, any coefficient ring, and any identification of H^0 with global sections.
For the empty scheme, the condition is vacuous and both section groups are zero. -/
theorem isIso_abelian_globalSectionsUpperStarMap_of_finite_connected_closed_intersections
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hconn : ∀ (X' : Scheme.{u}) (h : X' ⟶ X) [IsFinite h],
      ∀ C : Set X', IsClosed C → IsIrreducible C →
        IsConnected (C ∩ h ⁻¹' Set.range i))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} i G) := by
  have hZar := zariski_restriction_universe_transport i (fun x ↦ by
    simpa using hconn X (𝟙 X) (closure ({x} : Set X)) isClosed_closure
      (isIrreducible_singleton.closure))
  have hFinite (X' : Scheme.{u}) (h : X' ⟶ X) [IsFinite h] := by
    letI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace h
    letI : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated h
    exact zariski_restriction_universe_transport (pullback.snd i h) (fun x ↦ by
      rw [Scheme.Pullback.range_snd]
      exact hconn X' h (closure ({x} : Set X')) isClosed_closure
        (isIrreducible_singleton.closure))
  have hsets := gabber_h0_etale_criterion i hZar hFinite
    ((sheafForget (D := AddCommGrpCat.{u + 1}) X.smallEtaleTopology).obj G)
  obtain ⟨_, ea, da, _, _, _, _, _, _, _, hunit, _⟩ :=
    etaleInverseImageAlgebraicStructures Z X i
  let W : X.Etaleᵒᵖ := Opposite.op (Scheme.Etale.mk (𝟙 X))
  let ev := (sheafSections X.smallEtaleTopology (Type (u + 1))).obj W
  have heq := congrArg (fun k ↦ ev.map k) (hunit G)
  simp only [Functor.map_comp] at heq
  have : IsIso (ev.map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ i) (Type (u + 1))
        (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
        (Z.smallGrothendieckTopology @AlgebraicGeometry.Etale)).unit.app
          ((sheafForget (D := AddCommGrpCat.{u + 1}) X.smallEtaleTopology).obj G))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hsets
  have hη : IsIso (ev.map
      ((sheafForget (D := AddCommGrpCat.{u + 1}) X.smallEtaleTopology).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G))) := by
    have hi : IsIso (ev.map
        ((sheafForget (D := AddCommGrpCat.{u + 1}) X.smallEtaleTopology).map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G)) ≫
      ev.map (da.hom.app ((upperStar AddCommGrpCat.{u + 1} i).obj G)) ≫
      ev.map ((Functor.sheafPushforwardContinuous
        (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ i) (Type (u + 1))
          (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
          (Z.smallGrothendieckTopology @AlgebraicGeometry.Etale)).map (ea.hom.app G))) := by
      rw [heq]
      infer_instance
    simpa only [isIso_comp_right_iff] using hi
  change IsIso ((forget AddCommGrpCat.{u + 1}).map
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app W)) at hη
  have : IsIso
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app W) :=
    isIso_of_reflects_iso _ (forget AddCommGrpCat.{u + 1})
  have hterminal : IsIso
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app
        (Opposite.op (⊤_ X.Etale))) := by
    exact (NatTrans.isIso_app_iff_of_iso
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom
      ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X).uniqueUpToIso
        (terminalIsTerminal (C := X.Etale))).op).mpr inferInstance
  have : IsIso (((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op (⊤_ X.Etale))).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G)) := hterminal
  have : IsIso (((upperStar AddCommGrpCat.{u + 1} i).obj G).obj.map
      (PreservesTerminal.iso i.Etale).inv.op) := by infer_instance
  unfold globalSectionsUpperStarMap
  infer_instance

end AlgebraicGeometry.Etale
