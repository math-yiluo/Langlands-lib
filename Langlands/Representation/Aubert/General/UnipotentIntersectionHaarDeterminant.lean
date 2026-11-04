import Langlands.GroupScheme.Dynamic.UnipotentIntersectionSemidirectModel
import Langlands.GroupScheme.Dynamic.NormalizedLimits
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.Representation.Aubert.General.SmoothAffineUnipotentHaarDeterminant
import Langlands.Representation.Aubert.General.CorrectedOrbitJacquet

/-! # Actual Haar determinants on intersections of unipotent subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology MeasureTheory
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace Langlands.GroupScheme.Dynamic

variable {k : Type u} [Field k] {G Z : GroupScheme (Spec (CommRingCat.of k))}
  (chi psi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (iZ : Z ⟶ G)
  (hZ : SubgroupFunctor.range iZ ≤ centralizer chi)
  (hZ' : SubgroupFunctor.range iZ ≤ centralizer psi)

/-- The original point map, restricted to the normalizer of the literal
positive/positive intersection. -/
def centralizingUnipotentIntersectionNormalizerHom :
    rationalPoints Z →*
      Subgroup.normalizer
        ((unipotent chi ⊓ unipotent psi).carrier (Over.mk (𝟙 _)) :
          Set (rationalPoints G)) :=
  (rationalPoints.map iZ).codRestrict _ (fun z =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨centralizer_le_normalizer_unipotent chi _ (hZ _ ⟨z, rfl⟩),
        centralizer_le_normalizer_unipotent psi _ (hZ' _ ⟨z, rfl⟩)⟩)

@[simp] theorem centralizingUnipotentIntersectionNormalizerHom_coe
    (z : rationalPoints Z) :
    (centralizingUnipotentIntersectionNormalizerHom chi psi iZ hZ hZ' z :
      rationalPoints G) = z ≫ iZ.hom.hom := rfl

end Langlands.GroupScheme.Dynamic

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

section Character

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G Z : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Forward conjugation Haar character on the literal positive/positive
intersection in the original ambient point group. -/
def centralizingUnipotentIntersectionHaarCharacter :
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [IsTopologicalGroup (RationalPoint k G.X)]
      (chi psi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (iZ : Z ⟶ G)
      (_hZ : SubgroupFunctor.range iZ ≤ Dynamic.centralizer chi)
      (_hZ' : SubgroupFunctor.range iZ ≤ Dynamic.centralizer psi)
      (_hUc : IsClosed ((Dynamic.unipotent chi ⊓ Dynamic.unipotent psi).carrier
        (Over.mk (𝟙 _)) : Set (RationalPoint k G.X))),
      rationalPoints Z →* ℝ≥0ˣ := by
  intro _ _ chi psi iZ hZ hZ' hUc
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  exact (HaarModulus.closedNormalizerCharacter _ hUc).comp
    (Dynamic.centralizingUnipotentIntersectionNormalizerHom chi psi iZ hZ hZ')

end Character

section Haar

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

/-- The canonical point group of an affine group of finite type over a
nonarchimedean local field has an open subgroup basis. -/
theorem affineRationalPoint_nonarchimedeanGroup
    (A : GroupScheme (Spec (CommRingCat.of k))) [IsAffine A.X.left]
    [LocallyOfFiniteType A.X.hom] :
    letI : TopologicalSpace (RationalPoint k A.X) := rationalPointTopology k A.X
    NonarchimedeanGroup (RationalPoint k A.X) := by
  let _ : TopologicalSpace (RationalPoint k A.X) := rationalPointTopology k A.X
  have : IsTopologicalGroup (RationalPoint k A.X) := rationalPoint_isTopologicalGroup k A
  refine { is_nonarchimedean := ?_ }
  intro O hO
  obtain ⟨K, -, hKO⟩ := (Langlands.Topology.LocallyProfiniteProof.vanDantzig
    (RationalPoint k A.X)).mp (BruhatTits.rationalPoint_isLocallyProfinite k A) |>.2 O hO
  exact ⟨K, hKO⟩

variable (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- The forward Haar factor on the actual common positive intersection is
the absolute determinant of the actual common-centralizer action. -/
theorem unipotentIntersectionHaarDeterminant :
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (chi psi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (_hchi : SubgroupFunctor.range chi ≤ Dynamic.centralizer psi)
      {Z U : GroupScheme (Spec (CommRingCat.of k))} (iZ : Z ⟶ G) {iU : U ⟶ G}
      (hZ : SubgroupFunctor.range iZ ≤ Dynamic.centralizer chi)
      (hZ' : SubgroupFunctor.range iZ ≤ Dynamic.centralizer psi)
      (hU : (Dynamic.unipotent chi ⊓ Dynamic.unipotent psi).IsRepresentedBy iU)
      [IsAffine Z.X.left] [IsAffineHom U.X.hom]
      {d : ℕ} (c : Lie.FiniteCoordinates U d)
      (hUc : IsClosed ((Dynamic.unipotent chi ⊓ Dynamic.unipotent psi).carrier
        (Over.mk (𝟙 _)) : Set (RationalPoint k G.X))) (m : rationalPoints Z),
      (centralizingUnipotentIntersectionHaarCharacter chi psi iZ hZ hZ' hUc m : ℝ≥0) =
        distribHaarChar k (rationalCharacterEval
          ((Dynamic.centralizingUnipotentIntersectionAction
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
  have : IsAffineHom M.X.hom := hMc.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : Smooth M.X.hom := (dynamicSmooth k G psi M iM).2.1 hM
  let chiM : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ M := hM.factorHom chi hchi
  have hchiM : chiM ≫ iM = chi := hM.factorHom_comp chi hchi
  let H := Dynamic.Affine.centralizerScheme chiM
  let iHM := Dynamic.Affine.centralizerHom chiM
  have hHM : (Dynamic.centralizer chiM).IsRepresentedBy iHM :=
    Dynamic.Affine.isRepresentedBy_centralizerHom chiM
  have hHMc : IsClosedSubgroup iHM := Dynamic.Affine.isClosedSubgroup_centralizerHom chiM
  have : IsAffineHom H.X.hom := hHMc.isAffineHom
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : Smooth H.X.hom := (dynamicSmooth k M chiM H iHM).2.1 hHM
  let iH : H ⟶ G := iHM ≫ iM
  have hHc : IsClosedSubgroup iH := hHMc.comp hMc
  have hH : SubgroupFunctor.range iH ≤ Dynamic.centralizer chi := by
    rw [← hchiM]
    intro T x hx
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    change (x ≫ iHM.hom.hom) ≫ iM.hom.hom ∈
      (Dynamic.centralizer (chiM ≫ iM)).carrier T
    apply Dynamic.centralizer_le_comap chiM iM T
    rw [← hHM.2]
    exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
  have hH' : SubgroupFunctor.range iH ≤ Dynamic.centralizer psi := by
    rw [← hM.2]
    intro T x hx
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨x ≫ iHM.hom.hom, by
      rw [Grp.comp_hom_hom, Category.assoc]⟩
  let chiH : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ H :=
    hHM.factorHom chiM (Dynamic.range_le_centralizer chiM)
  have hchiH : chiH ≫ iH = chi := by
    change chiH ≫ iHM ≫ iM = chi
    rw [← Category.assoc, hHM.factorHom_comp chiM (Dynamic.range_le_centralizer chiM), hchiM]
  let N := Dynamic.Affine.unipotentScheme psi
  let iN := Dynamic.Affine.unipotentHom psi
  have hN : (Dynamic.unipotent psi).IsRepresentedBy iN :=
    Dynamic.Affine.isRepresentedBy_unipotentHom psi
  have hNc : IsClosedSubgroup iN := Dynamic.Affine.isClosedSubgroup_unipotentHom psi
  have : IsAffineHom N.X.hom := hNc.isAffineHom
  have : IsAffine N.X.left := isAffine_of_isAffineHom N.X.hom
  have : Smooth N.X.hom := (dynamicSmooth k G psi N iN).2.2 hN
  have hiUN : SubgroupFunctor.range iU ≤ Dynamic.unipotent psi := by
    rw [hU.2]
    intro T x hx
    exact hx.2
  let fU : U ⟶ N := hN.factorHom iU hiUN
  have hfU : fU ≫ iN = iU := hN.factorHom_comp iU hiUN
  let fZM : Z ⟶ M := hM.factorHom iZ hZ'
  have hfZM : fZM ≫ iM = iZ := hM.factorHom_comp iZ hZ'
  have hZM : SubgroupFunctor.range fZM ≤ Dynamic.centralizer chiM :=
    Dynamic.range_factor_le_centralizer chi hMc chiM hchiM iZ hZ fZM hfZM
  let fZ : Z ⟶ H := hHM.factorHom fZM hZM
  have hfZ : fZ ≫ iH = iZ := by
    change fZ ≫ iHM ≫ iM = iZ
    rw [← Category.assoc, hHM.factorHom_comp fZM hZM, hfZM]
  let a := Dynamic.centralizingUnipotentAction psi iH hH' hN
  let A := a.semidirectProduct
  have : IsAffineHom A.X.hom := inferInstance
  have : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  have : Smooth A.X.hom := inferInstance
  let chiA := chiH ≫ a.semidirectInr
  let jU := fU ≫ a.semidirectInl
  let jZ := fZ ≫ a.semidirectInr
  have hUA : (Dynamic.unipotent chiA).IsRepresentedBy jU :=
    Dynamic.isRepresentedBy_unipotentIntersection_semidirect
      chi psi iH hH hH' hHc hN hNc chiH hchiH hU fU hfU
  have hUAc : IsClosedSubgroup jU :=
    Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_unipotent chiA hUA
  have hfUc : IsClosedSubgroup fU :=
    a.isClosedSubgroup_semidirectInl.of_comp hUAc
  have hiUc : IsClosedSubgroup iU := by
    rw [← hfU]
    exact hfUc.comp hNc
  have hZA : SubgroupFunctor.range jZ ≤ Dynamic.centralizer chiA :=
    AutomorphicAction.range_comp_semidirectInr_le_centralizer_of_central a chiH
      (Dynamic.centralizer_factor_eq_top chi iH hH hHc chiH hchiH) fZ
  let _ : TopologicalSpace (RationalPoint k A.X) := pointTopology
  have : IsTopologicalGroup (RationalPoint k A.X) := rationalPoint_isTopologicalGroup k A
  have : LocallyCompactSpace (RationalPoint k A.X) := rationalPoint_locallyCompactSpace k A
  have : T2Space (RationalPoint k A.X) := rationalPoint_t2Space k A
  have : NonarchimedeanGroup (RationalPoint k A.X) := affineRationalPoint_nonarchimedeanGroup A
  let UA := (Dynamic.unipotent chiA).carrier (Over.mk (𝟙 _))
  have hUAclosed : IsClosed (UA : Set (RationalPoint k A.X)) :=
    isClosed_rationalPoint_subgroup k (Dynamic.unipotent chiA) jU hUA hUAc
  let b := Dynamic.centralizingUnipotentAction chiA jZ hZA hUA
  have hb : b = Dynamic.centralizingUnipotentIntersectionAction chi psi iZ hZ hZ' hU :=
    Dynamic.semidirectUnipotentIntersectionAction_eq
      chi psi iH hH hH' hHc hN hNc chiH hchiH hU fU hfU fZ iZ hZ hZ' hfZ
  have h := smoothAffineCentralizingUnipotentHaarDeterminant A chiA jZ hZA hUA c hUAclosed m
  change (HaarModulus.closedNormalizerCharacter UA hUAclosed
    (Dynamic.centralizingUnipotentNormalizerHom chiA jZ hZA m) : ℝ≥0) =
      distribHaarChar k (rationalCharacterEval (b.determinantCharacter c) m) at h
  rw [hb] at h
  let UG := (Dynamic.unipotent chi ⊓ Dynamic.unipotent psi).carrier (Over.mk (𝟙 _))
  let _ : TopologicalSpace (RationalPoint k U.X) := pointTopology
  let eA : RationalPoint k U.X ≃ₜ* UA :=
    rationalPointSubgroupHomeomorph k (Dynamic.unipotent chiA) jU hUA hUAc
  let eG : RationalPoint k U.X ≃ₜ* UG :=
    rationalPointSubgroupHomeomorph k (Dynamic.unipotent chi ⊓ Dynamic.unipotent psi)
      iU hU hiUc
  let e : UA ≃ₜ* UG := eA.symm.trans eG
  let gm := Dynamic.centralizingUnipotentNormalizerHom chiA jZ hZA m
  let gg := Dynamic.centralizingUnipotentIntersectionNormalizerHom chi psi iZ hZ hZ' m
  have hnorm (x : UA) :
      HaarModulus.normalizerConj UA gm x = eA (b.act m (eA.symm x)) := by
    apply Subtype.ext
    change (gm : RationalPoint k A.X) * (x : RationalPoint k A.X) *
      (gm : RationalPoint k A.X)⁻¹ = b.act m (eA.symm x) ≫ jU.hom.hom
    dsimp only [b]
    rw [Dynamic.centralizingUnipotentAction_act_comp]
    have hx : eA.symm x ≫ jU.hom.hom = (x : RationalPoint k A.X) := by
      change (eA (eA.symm x) : RationalPoint k A.X) = _
      rw [ContinuousMulEquiv.apply_symm_apply]
    rw [hx]
    rfl
  have : LocallyCompactSpace UA := hUAclosed.locallyCompactSpace
  let : MeasurableSpace UA := borel UA
  have : BorelSpace UA := ⟨rfl⟩
  have htransport := CorrectedFiltration.mulEquivHaarChar_eq_closedNormalizerCharacter
    UG hUc gg e (HaarModulus.normalizerConj UA gm) (fun x => by
      rw [hnorm]
      change eA.symm (eA (b.act m (eA.symm x))) ≫ iU.hom.hom =
        (gg : RationalPoint k G.X) * (eA.symm x ≫ iU.hom.hom) *
          (gg : RationalPoint k G.X)⁻¹
      rw [ContinuousMulEquiv.symm_apply_apply, hb,
        Dynamic.centralizingUnipotentIntersectionAction_act_comp]
      rfl)
  change (HaarModulus.closedNormalizerCharacter UG hUc gg : ℝ≥0) = _
  exact htransport.symm.trans h

end Haar

end Langlands.Aubert.General.RationalPointFamily
