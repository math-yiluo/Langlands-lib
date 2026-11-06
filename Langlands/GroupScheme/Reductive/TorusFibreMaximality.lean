import Langlands.GroupScheme.Reductive.EtaleResidueFibre
import Langlands.GroupScheme.Reductive.GeometricReductiveFieldInputs
import Langlands.GroupScheme.Torus.MaximalFieldIso
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof

/-! # Maximality and self-centralization in actual torus fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Maximality in a composite field fibre agrees with maximality in the
successive actual pullbacks, through their natural comparisons. -/
theorem isMaximalTorus_baseChange_comp
    {S S' : Scheme.{u}} (a : S' ⟶ S) {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S') (T : CommGroupScheme S)
    {G : GroupScheme S} (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus (T := (CommGroupScheme.baseChange (b ≫ a)).obj T)
      ((baseChange (b ≫ a)).map i)) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj
      ((CommGroupScheme.baseChange a).obj T))
      ((baseChange b).map ((baseChange a).map i)) := by
  have hn := ((Functor.mapGrpNatIso (Over.pullbackComp b a)) ≪≫
    Functor.mapGrpCompIso).hom.naturality i
  change (baseChange (b ≫ a)).map i ≫ (baseChangeCompIso a b G).hom =
    (baseChangeCompIso a b T.toGrp).hom ≫
      (baseChange b).map ((baseChange a).map i) at hn
  have hm := (IsMaximalTorus.iso_comp
    (T := (CommGroupScheme.baseChange (b ≫ a)).obj T)
    (T' := (CommGroupScheme.baseChange b).obj ((CommGroupScheme.baseChange a).obj T))
    (baseChangeCompIso a b T.toGrp).symm hi).comp_iso (baseChangeCompIso a b G)
  simpa only [Iso.symm_hom, Category.assoc, hn, Iso.inv_hom_id_assoc] using hm

namespace splitTorus

variable {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)

local instance smooth_fieldPullback {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of r)) :
    Smooth ((baseChange b).obj G).X.hom :=
  inferInstanceAs (Smooth (Limits.pullback.snd G.X.hom b))

local instance affine_fieldPullback {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of r)) :
    IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

set_option maxHeartbeats 4000000 in
/-- A maximal torus in any algebraically closed field-valued fibre certifies
self-centralization in the chosen original geometric fibre at its image.
The comparison uses actual zero weights and their relative ranks. -/
theorem mem_geometricSelfCentralizingTorusLocus_of_maximal_fieldPoint
    (hCentralizer : AlgClosedMaximalTorusCentralizerStatement.{u})
    (hi : IsClosedSubgroup i) {k : Type u} [Field k] [IsAlgClosed k]
    (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of r))
    (hs : b (IsLocalRing.closedPoint k) ∈ identityComponentReductiveLocus G)
    (hmax : IsMaximalTorus (T := commGroupScheme _ I)
      (RelativeCocharacterCentralizer.baseChangedTorusHom I G i b)) :
    b (IsLocalRing.closedPoint k) ∈ geometricSelfCentralizingTorusLocus I G i := by
  let H := (baseChange b).obj G
  let j : (commGroupScheme (Spec (CommRingCat.of k)) I).toGrp ⟶ H :=
    RelativeCocharacterCentralizer.baseChangedTorusHom I G i b
  have hred : IsConnectedReductive (identityComponent H) :=
    (fieldIdentityComponentReductive_iff_mem_locus G b).mpr hs
  have hm : IsMaximalTorus (T := commGroupScheme _ I)
      (IdentityComponent.torusHom (T := commGroupScheme _ I) j
        (isSplitTorus_splitTorus I)) := by
    apply IsMaximalTorus.of_comp (T := commGroupScheme _ I)
      (IdentityComponent.isClosedSubgroup_identityComponentι H)
    simpa only [IdentityComponent.torusHom_comp] using hmax
  have hself := hCentralizer k (identityComponent H) hred (commGroupScheme _ I)
    (IdentityComponent.torusHom j (isSplitTorus_splitTorus I)) hm
  let : IsAffineHom (commGroupScheme (Spec (CommRingCat.of k)) I).X.hom :=
    isAffineHom_splitTorus _ I
  let : IsClosedImmersion
      (IdentityComponent.torusHom j (isSplitTorus_splitTorus I)).hom.hom.left := hm.2.1
  let : Mono (IdentityComponent.torusHom j (isSplitTorus_splitTorus I)).hom.hom :=
    Over.mono_of_mono_left _
  have hdim : Module.finrank k (weightSpace (T := commGroupScheme _ I) j 0) = Nat.card I := by
    exact (IdentityComponent.finrank_weightSpace (T := commGroupScheme _ I) j
      (isSplitTorus_splitTorus I) 0).symm.trans
        ((Lie.finrank_zeroWeight_of_selfCentralizing (T := commGroupScheme _ I)
          _ hself).trans (finrank_lieKernel I k))
  have hr := exponentWeightRank_affineBaseChange I G i b 0 (IsLocalRing.closedPoint k)
  have hfield : exponentWeightRank I H j 0 (IsLocalRing.closedPoint k) =
      Module.finrank k (weightSpace (T := commGroupScheme _ I) j 0) := by
    let : Module.Free k (exponentWeightSpace I H j 0) :=
      Module.Free.of_divisionRing k (exponentWeightSpace I H j 0)
    dsimp only [exponentWeightRank]
    rw [Module.rankAtStalk_eq_finrank_of_free,
      exponentWeightSpace_eq_weightSpace k I H j 0, map_zero]
    rfl
  exact (mem_geometricSelfCentralizingTorusLocus_iff I G i hi _).mpr
    (hr.symm.trans (hfield.trans hdim))

/-- An actual maximal torus over an algebraically closed field-valued point
constructs a good original-base open from the retained field statements. -/
def identityComponentReductiveNeighbourhood_of_maximal_fieldPoint
    (hCentralizer : AlgClosedMaximalTorusCentralizerStatement.{u})
    (hReflection : RelativeRootReflectionExistenceStatement.{u})
    (hReduced : RootReducednessStatement.{u})
    (hLine : SplitRootLieLineStatement.{u})
    (hi : IsClosedSubgroup i) {k : Type u} [Field k] [IsAlgClosed k]
    (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of r))
    (hs : b (IsLocalRing.closedPoint k) ∈ identityComponentReductiveLocus G)
    (hmax : IsMaximalTorus (T := commGroupScheme _ I)
      (RelativeCocharacterCentralizer.baseChangedTorusHom I G i b)) :
    IdentityComponentReductiveOpenNeighbourhood G (b (IsLocalRing.closedPoint k)) := by
  let : IsClosedImmersion i.hom.hom.left := hi
  exact identityComponentReductiveNeighbourhood_of_fieldStatements I G i _
    hReflection hReduced hLine hs
    (mem_geometricSelfCentralizingTorusLocus_of_maximal_fieldPoint I G i
      hCentralizer hi b hs hmax)

end splitTorus

end Langlands.GroupScheme

namespace Langlands.AlgebraicGeometry.EtaleResidueExtensionData

open Langlands.GroupScheme

variable {S : Scheme.{u}} {s : S} {K : Type u} [Field K]
  [Algebra (S.residueField s) K] (d : EtaleResidueExtensionData S s K)

/-- The actual torus inclusion in the new residue fibre remains maximal.
The residue comparison is an isomorphism of fields, so no smoothness or
reductivity assumption is needed for this transport. -/
theorem torusFibreInclusion_isMaximal (G : GroupScheme S)
    (T : CommGroupScheme (Spec (CommRingCat.of K)))
    (i : T.toGrp ⟶ (baseChange d.extensionPoint).obj G) (hi : IsMaximalTorus i) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange d.inverseResiduePoint).obj T)
      (d.torusFibreInclusion G T.toGrp i) := by
  have hm := hi.baseChange_fieldIso d.residueIso.symm.commRingCatIsoToRingEquiv
  exact hm.comp_iso (d.groupFibreIso G)

end Langlands.AlgebraicGeometry.EtaleResidueExtensionData
