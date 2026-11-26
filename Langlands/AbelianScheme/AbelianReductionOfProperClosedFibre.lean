import Langlands.AbelianScheme.AbelianReductionStatement
import Langlands.AbelianScheme.RelativeHomNeronExtension
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Langlands.AlgebraicGeometry.SmoothDvrProperClosedFibreStatement
import Langlands.GroupScheme.Absolute.ParabolicIntersectionTorusReduction
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.IntegralModel.RelativeComponentConstruction
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothBaseChangeProof
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothExistenceProof

/-! # Abelian reduction from the proper closed fibre criterion -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Langlands.GroupScheme TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

/-- In the abelian reduction criterion, properness of the smooth relative
identity component follows from the proper closed fibre criterion. The Néron
mapping property makes the resulting abelian scheme equal to the model. -/
theorem abelianReduction_of_properClosedFibre
    (hP : Langlands.AlgebraicGeometry.SmoothDvrProperClosedFibreStatement.{u}) :
    AbelianReductionStatement.{u} := by
  intro V K _ _ _ _ _ _ B N J i hi hJ
  let S := Spec (CommRingCat.of V)
  let G := N.group.toGrp
  let k := IsLocalRing.ResidueField V
  let kbar := AlgebraicClosure k
  let sp := Spec.algebraMap V k
  let c := Spec.algebraMap k kbar
  let spGeom := geometricSpecialPoint V
  let gen := NeronModelInfra.specGenericFibreInclusion V K
  let : Smooth G.X.hom := N.property.smooth
  let : IsSeparated G.X.hom := N.property.separated
  let : QuasiCompact G.X.hom := N.property.quasiCompact
  obtain ⟨H, j, hj, hHsm, hHconn⟩ := RelativeIdentityComponent.smoothExistence S G N.property.smooth
  let : IsOpenImmersion j.hom.hom.left := hj.isOpenImmersion
  let : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  let : CompactSpace G.X.left := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  let : IsNoetherian G.X.left := {}
  let : NoetherianSpace H.X.left :=
    j.hom.hom.left.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have hHsep : IsSeparated H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let HGeom := (GroupScheme.baseChange spGeom).obj H
  have hjGeom : IsRelativeIdentityComponent N.geometricSpecialFibre.toGrp
      ((GroupScheme.baseChange spGeom).map j) :=
    RelativeIdentityComponent.smoothBaseChange S G N.property.smooth H j hj _ spGeom
  let e : HGeom.X ≅ J.X := (Grp.forget _).mapIso (hjGeom.iso hi)
  have hGeom : IsProper HGeom.X.hom := by
    let : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    let : IsProper J.X.hom := hJ
    rw [← Over.w e.hom]
    infer_instance
  have hclosed : IsProper (pullback.snd H.X.hom sp) := by
    have hc := fieldExtension_fpqc k kbar
    have hp : IsProper (pullback.snd (pullback.snd H.X.hom sp) c) := by
      rw [← pullbackLeftPullbackSndIso_hom_snd H.X.hom sp c]
      have : IsProper (pullback.snd H.X.hom (c ≫ sp)) := hGeom
      infer_instance
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsProper)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (IsPullback.of_hasPullback (pullback.snd H.X.hom sp) c).flip
      ⟨⟨hc.1, hc.2.1⟩, hc.2.2⟩ hp
  have hHproper : IsProper H.X.hom :=
    hP V H.X.left H.X.hom hHsm hHsep inferInstance hHconn hclosed
  let F := GroupScheme.baseChange gen
  let eGen : B.X ≅ (F.obj G).X := (Grp.forget _).mapIso (CommGroupScheme.groupIso N.genericIso)
  let : GeometricallyConnected (F.obj G).X.hom := by
    let : IsIso eGen.inv.left := (Over.forget _).map_isIso eGen.inv
    rw [← Over.w eGen.inv]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected)
      eGen.inv.left B.X.hom).mpr B.geometricallyConnected
  have hjGen : IsRelativeIdentityComponent (F.obj G) (F.map j) :=
    RelativeIdentityComponent.smoothBaseChange S G N.property.smooth H j hj _ gen
  let eJ := hjGen.isoOfGeometricallyConnected
  let : GeometricallyConnected H.X.hom := hHconn
  let hH : GoodReductionJacobian.AbelianSchemePropertyBundle V H.X.hom :=
    { smooth := hHsm
      proper := hHproper
      connectedFibres := fun s => H.X.hom.isConnected_preimage_singleton s
      hasGroupLaw := ⟨@GoodReductionJacobian.relativeGroupLawOfGrpObj V _ _ _ H.grp⟩ }
  obtain ⟨r, hr⟩ := baseChange_map_surjective K G H hH eJ.inv
  have hcomp : r.hom.hom ≫ j.hom.hom = 𝟙 G.X := by
    apply genericFibre_map_injective K
    change (Over.pullback gen).map (r.hom.hom ≫ j.hom.hom) =
      (Over.pullback gen).map (𝟙 G.X)
    rw [(Over.pullback gen).map_comp, (Over.pullback gen).map_id]
    change (F.map r).hom.hom ≫ (F.map j).hom.hom = _
    change F.map r = eJ.inv at hr
    have hgen : (F.map j).hom.hom = eJ.hom.hom.hom :=
      congrArg (fun f => f.hom.hom) hjGen.isoOfGeometricallyConnected_hom.symm
    rw [hr, hgen]
    exact congrArg (fun f => f.hom.hom) eJ.inv_hom_id
  let : Mono j.hom.hom := hj.mono_hom
  let : IsSplitEpi j.hom.hom := ⟨⟨r.hom.hom, hcomp⟩⟩
  let : IsIso j.hom.hom := isIso_of_mono_of_isSplitEpi _
  let : IsIso j.hom.hom.left := (Over.forget _).map_isIso j.hom.hom
  exact ⟨(MorphismProperty.cancel_left_of_respectsIso (P := @IsProper) j.hom.hom.left G.X.hom).mp
      (by simpa only [Over.w] using hHproper),
    (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected)
      j.hom.hom.left G.X.hom).mp (by simpa only [Over.w] using hHconn)⟩

end Langlands.AbelianScheme
