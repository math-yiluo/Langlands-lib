import Langlands.GroupScheme.Torus.UnipotentQuotientMaximalSplit
import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.GroupScheme.IntegralModel.SplitTorusUnitPoints
import Langlands.GroupScheme.Torus.HenselianSplitRank

/-! # Special-fibre maximality of a common integral split torus -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.IntegralModel

/-- A map from an integral split torus to a model over a noetherian domain is
closed whenever its generic-fibre map is closed. -/
theorem isClosedSubgroup_of_split_generic
    {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)
    (T : CommGroupScheme (Spec (CommRingCat.of R))) (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ M.group)
    (hj : IsClosedSubgroup
      ((GroupScheme.baseChange (Spec.algebraMap R K)).map j ≫ M.genericIso.hom)) :
    IsClosedSubgroup j := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  let d : (SplitTorusClosure.torus R I).toGrp ≅ T.toGrp :=
    SplitTorusClosure.splitIsoR R I ≪≫ e.symm
  have hd : IsClosedSubgroup (d.hom ≫ j) := by
    apply SplitTorusClosure.isClosedSubgroup_of_genericTorusMap M
    change IsClosedSubgroup
      ((GroupScheme.baseChange (Spec.algebraMap R K)).map (d.hom ≫ j) ≫
        M.genericIso.hom)
    rw [Functor.map_comp, Category.assoc]
    exact hj.iso_comp ((GroupScheme.baseChange (Spec.algebraMap R K)).mapIso d)
  simpa only [Iso.symm_hom, Iso.inv_hom_id_assoc] using hd.iso_comp d.symm

end Langlands.GroupScheme.IntegralModel

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme

/-- Transport a supplied integral torus along a compatible model morphism,
keeping its generic torus and generic inclusion. -/
def RelativeComponentModelHom.mapIntegralTorus
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {G : GroupScheme (Spec (CommRingCat.of K))}
    {source target : RelativeComponentModelData R K G}
    (φ : RelativeComponentModelHom source target)
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData source S i) : IntegralTorusData target S i where
  torus := T.torus
  genericIso := T.genericIso
  inclusion := T.inclusion ≫ φ.neutral.hom
  generic_comm := by
    rw [Functor.map_comp, Category.assoc, φ.neutral.generic_comm,
      Category.comp_id, T.generic_comm]

/-- A common split integral torus with maximal generic fibre is maximal in
the target special fibre of any model morphism over a noetherian Henselian domain. -/
theorem RelativeComponentModelHom.isMaximalSplitTorus_targetTorusInclusion
    {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [HenselianLocalRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (hG : IsConnectedReductive G)
    {source target : RelativeComponentModelData R K G}
    (φ : RelativeComponentModelHom source target)
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData source S i) (hT : IsSplitTorus T.torus.toGrp)
    (hi : IsMaximalSplitTorus i) :
    IsMaximalSplitTorus (φ.targetTorusInclusion T) := by
  let j := (φ.mapIntegralTorus T).inclusion
  have hjgen :
      (GroupScheme.baseChange (Spec.algebraMap R K)).map j ≫
        target.neutral.genericIso.hom = T.genericIso.hom ≫ i := by
    exact (φ.mapIntegralTorus T).generic_comm
  have hjclosed : IsClosedSubgroup j := by
    apply IntegralModel.isClosedSubgroup_of_split_generic target.neutral T.torus hT j
    rw [hjgen]
    exact hi.1.2.iso_comp T.genericIso
  have hjmax : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus)
      ((GroupScheme.baseChange (Spec.algebraMap R K)).map j) := by
    apply (IsMaximalSplitTorus.comp_iso_iff _ target.neutral.genericIso).mp
    rw [hjgen]
    exact IsMaximalSplitTorus.iso_comp
      (T' := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus)
      T.genericIso hi
  let : Smooth target.neutral.group.X.hom := target.neutral_smooth
  have hres := isMaximalSplitTorus_residue_of_generic
    (IsLocalRing.residue_surjective : Function.Surjective
      (algebraMap R (IsLocalRing.ResidueField R)))
    target.neutral.group (hG.of_iso target.neutral.genericIso)
    T.torus hT j hjclosed hjmax
  simpa only [j, RelativeComponentModelHom.mapIntegralTorus, Functor.map_comp,
    RelativeComponentModelHom.targetTorusInclusion,
    IntegralTorusData.specialFibreInclusion, RelativeComponentModelHom.neutralSpecialFibreMap,
    IntegralModel.Hom.specialFibreMap, IntegralModel.residueBaseMap,
    IntegralTorusData.specialFibre, IntegralModel.specialFibre, Spec.algebraMap,
    IsLocalRing.ResidueField.algebraMap_eq] using hres

end Langlands.BruhatTits.IntegralModels
