/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalInjectiveSourceComparison
import WeilConjectures.AlgebraicGeometry.EtaleObjectSections
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.ObjectSectionsNaturality

/-! # Restriction of the underived stage sections comparison

Source: Stacks Project, Tags 03Q9 and 03S2, restriction of an injective complex.
(blueprint: lem-weil-pbc-source-stage-sections-naturality).
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.SourceStageSectionsNaturality.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem sectionsPullbackNat_app {Y Z : Scheme.{v}} (m : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (sectionsPullbackNat m).app F = globalSectionsUpperStarMap AddCommGrpCat.{v + 1} m F := by
  let A := AddCommGrpCat.{v + 1}
  let η := (upperStarLowerStarAdjunction A m).unit.app F
  let K := (upperStar A m).obj F
  let tZ := Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology A terminalIsTerminal
  let tY := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A terminalIsTerminal
  change (Sheaf.Γ Z.smallEtaleTopology A).map η ≫
      (tZ.hom.app ((lowerStar A m).obj K) ≫
        K.obj.map (PreservesTerminal.iso m.Etale).inv.op ≫ tY.inv.app K) =
    tZ.hom.app F ≫ η.hom.app (op (⊤_ Z.Etale)) ≫
      K.obj.map (PreservesTerminal.iso m.Etale).inv.op ≫ tY.inv.app K
  exact (reassoc_of% (tZ.hom.naturality η))
    (K.obj.map (PreservesTerminal.iso m.Etale).inv.op ≫ tY.inv.app K)

set_option maxRecDepth 2048 in
-- Unfolding the stage comparison and the complex components needs additional elaboration.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The stage comparison intertwines restriction already at the chain level.
Source: Stacks Project, Tag 03Q9, final paragraph, and Tag 03S2,
etale restriction and its left adjoint.
(blueprint: lem-weil-pbc-source-stage-sections-naturality).

Proof: In degree k, direct-image sections at W_i are sections of M.X k on
W_i times_S X, with restriction along the pullback of the neighbourhood arrow.
The comparison smallModel_sourceStageSectionsIso evaluates localization restriction on the
identity etale object of this fibre product and then inverts terminal evaluation.
The localization comparison is the unique left-adjoint comparison compatible
with units. Its unit identity identifies sectionsPullbackNat with restriction
along the projection from the pullback of that identity object. The canonical
isomorphism from that pullback to the identity object over the smaller stage
has the two prescribed projections, so composing it with the projection gives
exactly the base-changed neighbourhood arrow. Compatibility of upperStarComp
with the composed adjunction units identifies its inverse with the comparison
of the two successive localizations; the naturality equation for the stage
projection supplies the required equality over X. Thus the two composites
agree after terminal evaluation, which is an isomorphism, and hence agree.
This is natural in the sheaf M.X k. Apply it in every degree: differentials
commute by the naturality in M.X k, and chain-map extensionality gives the
stated equation. No injectivity, boundedness, derived object, or cohomology
degree is needed. Identity arrows give identity restrictions and the zero
complex gives zero chain maps. -/
theorem smallModel_sourceStageSectionsIso_naturality {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {i j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)} (a : i ⟶ j)
    (M : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) :
    (NatTrans.mapHomologicalComplex
      ((sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).map
        ((strictLocalNeighbourhoods s).map a).op) (.up ℤ)).app
          (((lowerStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex (.up ℤ)).obj M) ≫
      (NatIso.mapHomologicalComplex (smallModel_sourceStageSectionsIso f s i) (.up ℤ)).hom.app M =
    (NatIso.mapHomologicalComplex (smallModel_sourceStageSectionsIso f s j) (.up ℤ)).hom.app M ≫
      ((NatTrans.mapHomologicalComplex
        (sectionsPullbackNat ((strictLocalNeighbourhoodDiagram f s).map a))
          (.up ℤ)).app
            (((upperStar AddCommGrpCat.{v + 1}
              ((strictLocalNeighbourhoodProjection f s).app j)).mapHomologicalComplex
                (.up ℤ)).obj M) ≫
        ((Sheaf.Γ ((strictLocalNeighbourhoodDiagram f s).obj i).smallEtaleTopology
          AddCommGrpCat.{v + 1}).mapHomologicalComplex (.up ℤ)).map
            ((NatIso.mapHomologicalComplex
              (upperStarComp AddCommGrpCat.{v + 1}
                ((strictLocalNeighbourhoodDiagram f s).map a)
                ((strictLocalNeighbourhoodProjection f s).app j)
                ((strictLocalNeighbourhoodProjection f s).app i)
                ((Category.comp_id _).symm.trans
                  ((strictLocalNeighbourhoodProjection f s).naturality a).symm))
              (.up ℤ)).inv.app M)) := by
  apply HomologicalComplex.Hom.ext
  funext k
  let P := MorphismProperty.Over.pullback @Etale ⊤ f
  let U := P.obj ((strictLocalNeighbourhoods s).obj i)
  let V := P.obj ((strictLocalNeighbourhoods s).obj j)
  let b := P.map ((strictLocalNeighbourhoods s).map a)
  let A := AddCommGrpCat.{v + 1}
  let e := (upperStarComp A b.left V.hom U.hom b.w.symm).app (M.X k)
  let Γ := Sheaf.Γ U.left.smallEtaleTopology A
  have hn := objectSections_naturality b (M.X k)
  have h := congrArg (fun t ↦ t ≫ Γ.map e.inv) hn
  change (M.X k).obj.map b.op ≫ (etaleObjectSectionsIso U).hom.app (M.X k) ≫
      Γ.map e.hom ≫ Γ.map e.inv =
    (etaleObjectSectionsIso V).hom.app (M.X k) ≫
      globalSectionsUpperStarMap A b.left ((upperStar A V.hom).obj (M.X k)) ≫
        Γ.map e.inv at h
  erw [← Γ.map_comp e.hom e.inv, e.hom_inv_id, Γ.map_id, Category.comp_id] at h
  change (M.X k).obj.map b.op ≫ (etaleObjectSectionsIso U).hom.app (M.X k) =
    (etaleObjectSectionsIso V).hom.app (M.X k) ≫
      (sectionsPullbackNat b.left).app ((upperStar A V.hom).obj (M.X k)) ≫ Γ.map e.inv
  rw [sectionsPullbackNat_app]
  exact h

end AlgebraicGeometry.Etale
