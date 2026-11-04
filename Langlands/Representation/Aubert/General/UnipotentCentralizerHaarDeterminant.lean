import Langlands.GroupScheme.Dynamic.UnipotentCentralizerRestriction
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.Representation.Aubert.General.SmoothAffineUnipotentHaarDeterminant
import Langlands.Representation.Aubert.General.CorrectedOrbitJacquet

/-! # Actual Haar determinants on unipotent-centralizer intersections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology MeasureTheory
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

section Character

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G Z : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The Haar character of the original point map acting by forward conjugation
on the literal positive/zero intersection in the ambient point group. -/
def centralizingUnipotentCentralizerHaarCharacter :
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [IsTopologicalGroup (RationalPoint k G.X)]
      (chi psi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (iZ : Z ⟶ G)
      (_hZ : SubgroupFunctor.range iZ ≤ Dynamic.centralizer chi)
      (_hZ' : SubgroupFunctor.range iZ ≤ Dynamic.centralizer psi)
      (_hUc : IsClosed ((Dynamic.unipotent chi ⊓ Dynamic.centralizer psi).carrier
        (Over.mk (𝟙 _)) : Set (RationalPoint k G.X))),
      rationalPoints Z →* ℝ≥0ˣ := by
  intro _ _ chi psi iZ hZ hZ' hUc
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  exact (HaarModulus.closedNormalizerCharacter _ hUc).comp
    (Dynamic.centralizingUnipotentCentralizerNormalizerHom chi psi iZ hZ hZ')

end Character

section Haar

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- The forward Haar factor on the actual positive/zero intersection equals
the absolute determinant of its actual common-centralizer action. -/
theorem unipotentCentralizerHaarDeterminant :
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (chi psi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (_hchi : SubgroupFunctor.range chi ≤ Dynamic.centralizer psi)
      {Z U : GroupScheme (Spec (CommRingCat.of k))} (iZ : Z ⟶ G) {iU : U ⟶ G}
      (hZ : SubgroupFunctor.range iZ ≤ Dynamic.centralizer chi)
      (hZ' : SubgroupFunctor.range iZ ≤ Dynamic.centralizer psi)
      (hU : (Dynamic.unipotent chi ⊓ Dynamic.centralizer psi).IsRepresentedBy iU)
      [IsAffine Z.X.left] [IsAffineHom U.X.hom]
      {d : ℕ} (c : Lie.FiniteCoordinates U d)
      (hUc : IsClosed ((Dynamic.unipotent chi ⊓ Dynamic.centralizer psi).carrier
        (Over.mk (𝟙 _)) : Set (RationalPoint k G.X))) (m : rationalPoints Z),
      (centralizingUnipotentCentralizerHaarCharacter chi psi iZ hZ hZ' hUc m : ℝ≥0) =
        distribHaarChar k (rationalCharacterEval
          ((Dynamic.centralizingUnipotentCentralizerIntersectionAction
            chi psi iZ hZ hZ' hU).determinantCharacter c) m) := by
  intro _ _ _ chi psi hchi Z U iZ iU hZ hZ' hU _ _ d c hUc m
  let : T2Space k := BruhatTits.localField_t2Space k
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let M := Dynamic.Affine.centralizerScheme psi
  let iM := Dynamic.Affine.centralizerHom psi
  have hM : (Dynamic.centralizer psi).IsRepresentedBy iM :=
    Dynamic.Affine.isRepresentedBy_centralizerHom psi
  have hMc : IsClosedSubgroup iM := Dynamic.Affine.isClosedSubgroup_centralizerHom psi
  have : IsClosedImmersion iM.hom.hom.left := hMc
  have : IsAffineHom M.X.hom := hMc.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : Smooth M.X.hom := (dynamicSmooth k G psi M iM).2.1 hM
  let chiM : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ M := hM.factorHom chi hchi
  have hchiM : chiM ≫ iM = chi := hM.factorHom_comp chi hchi
  have hiUM : SubgroupFunctor.range iU ≤ Dynamic.centralizer psi := by
    rw [hU.2]
    intro T x hx
    exact hx.2
  let fU : U ⟶ M := hM.factorHom iU hiUM
  have hfU : fU ≫ iM = iU := hM.factorHom_comp iU hiUM
  have hUM : (Dynamic.unipotent chiM).IsRepresentedBy fU :=
    Dynamic.isRepresentedBy_unipotent_centralizer_factor chi psi hM hMc chiM hchiM hU fU hfU
  have hUMc : IsClosedSubgroup fU :=
    Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_unipotent chiM hUM
  have hiUc : IsClosedSubgroup iU := by
    rw [← hfU]
    exact hUMc.comp hMc
  let fZ : Z ⟶ M := hM.factorHom iZ hZ'
  have hfZ : fZ ≫ iM = iZ := hM.factorHom_comp iZ hZ'
  have hZM : SubgroupFunctor.range fZ ≤ Dynamic.centralizer chiM :=
    Dynamic.range_factor_le_centralizer chi hMc chiM hchiM iZ hZ fZ hfZ
  let _ : TopologicalSpace (RationalPoint k M.X) := pointTopology
  have hMe : IsClosedEmbedding (fun p : RationalPoint k M.X => p ≫ iM.hom.hom) :=
    isClosedEmbedding_rationalPointMap k iM.hom.hom
  have : IsTopologicalGroup (RationalPoint k M.X) := rationalPoint_isTopologicalGroup k M
  have : LocallyCompactSpace (RationalPoint k M.X) := hMe.locallyCompactSpace
  have : T2Space (RationalPoint k M.X) := hMe.isEmbedding.t2Space
  have : NonarchimedeanGroup (RationalPoint k M.X) :=
    CorrectedFiltration.nonarchimedeanGroup_of_isInducing (rationalPoints.map iM) hMe.isInducing
  let UM := (Dynamic.unipotent chiM).carrier (Over.mk (𝟙 _))
  have hUMclosed : IsClosed (UM : Set (RationalPoint k M.X)) :=
    isClosed_rationalPoint_subgroup k (Dynamic.unipotent chiM) fU hUM hUMc
  have h := smoothAffineCentralizingUnipotentHaarDeterminant M chiM fZ hZM hUM c hUMclosed m
  rw [Dynamic.centralizingUnipotentAction_eq_intersectionAction
    chi psi hM hMc chiM hchiM hU fU hfU iZ hZ hZ' fZ hfZ] at h
  let UG := (Dynamic.unipotent chi ⊓ Dynamic.centralizer psi).carrier (Over.mk (𝟙 _))
  let _ : TopologicalSpace (RationalPoint k U.X) := pointTopology
  let eM : RationalPoint k U.X ≃ₜ* UM :=
    rationalPointSubgroupHomeomorph k (Dynamic.unipotent chiM) fU hUM hUMc
  let eG : RationalPoint k U.X ≃ₜ* UG :=
    rationalPointSubgroupHomeomorph k (Dynamic.unipotent chi ⊓ Dynamic.centralizer psi)
      iU hU hiUc
  let e : UM ≃ₜ* UG := eM.symm.trans eG
  have he (x : UM) : (e x : RationalPoint k G.X) = (x : RationalPoint k M.X) ≫ iM.hom.hom := by
    change eM.symm x ≫ iU.hom.hom = _
    rw [← hfU, Grp.comp_hom_hom, ← Category.assoc]
    change (eM (eM.symm x) : RationalPoint k M.X) ≫ iM.hom.hom = _
    rw [ContinuousMulEquiv.apply_symm_apply]
  let gm := Dynamic.centralizingUnipotentNormalizerHom chiM fZ hZM m
  let gg := Dynamic.centralizingUnipotentCentralizerNormalizerHom chi psi iZ hZ hZ' m
  have hmg : (gm : RationalPoint k M.X) ≫ iM.hom.hom = (gg : RationalPoint k G.X) := by
    change (m ≫ fZ.hom.hom) ≫ iM.hom.hom = m ≫ iZ.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, hfZ]
  have : LocallyCompactSpace UM := hUMclosed.locallyCompactSpace
  let : MeasurableSpace UM := borel UM
  have : BorelSpace UM := ⟨rfl⟩
  have htransport := CorrectedFiltration.mulEquivHaarChar_eq_closedNormalizerCharacter
    UG hUc gg e (HaarModulus.normalizerConj UM gm) (fun x => by
      rw [he, HaarModulus.normalizerConj_apply, MonObj.mul_comp, MonObj.mul_comp,
        GrpObj.inv_comp, hmg, he])
  change (HaarModulus.closedNormalizerCharacter UG hUc gg : ℝ≥0) = _
  exact htransport.symm.trans h

end Haar

end Langlands.Aubert.General.RationalPointFamily
