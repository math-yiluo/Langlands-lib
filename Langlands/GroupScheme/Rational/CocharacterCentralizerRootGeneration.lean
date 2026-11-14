import Langlands.GroupScheme.Rational.RootGeneratedCentralizerCovering
import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Root generation of cocharacter centralizer points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G)

/-- A subgroup containing the whole-torus centralizer and all root groups
annihilating a cocharacter contains that cocharacter's centralizer points. -/
theorem dynamicCentralizer_rationalPoints_le_of_zeroRootGroups
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ζ : cocharacterLattice T) (N : Subgroup (rationalPoints G))
    (hZ : centralizerPoints i ≤ N)
    (hroot : ∀ α ∈ relativeRoots i, latticePairing T α ζ = 0 →
      (RelativeRoot.subgroup i α).carrier (Over.mk (𝟙 _)) ≤ N) :
    (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier
      (Over.mk (𝟙 _)) ≤ N := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let M := Dynamic.Affine.centralizerScheme (CommGroupScheme.groupHom ζ ≫ i)
  let j : M ⟶ G := Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom ζ ≫ i)
  have hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j :=
    Dynamic.Affine.isRepresentedBy_centralizerHom _
  have hjc : IsClosedSubgroup j := Dynamic.Affine.isClosedSubgroup_centralizerHom _
  have hM : IsConnectedReductive M := dynamicCentralizerReductive k G hG _ M j hjc hj
  have : IsAffineHom M.X.hom := hjc.isAffineHom
  have : Smooth M.X.hom := hM.smooth
  let iM := Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj
  have hcomp : iM ≫ j = i := Dynamic.torusFactor_comp i _ hj
  have hiM : IsMaximalSplitTorus iM :=
    IsMaximalSplitTorus.of_comp hjc (hcomp.symm ▸ hi)
  have hrootsM : relativeRootGeneratedSubgroup iM ≤
      N.comap (rationalPoints.map j) := by
    rw [relativeRootGeneratedSubgroup_le_iff]
    intro α hα m hm
    have hαG := relativeRoots_subset_of_factor hj iM hcomp hα
    have hα0 := relativeRoot_pairing_eq_zero_of_le_dynamicCentralizer
      hj iM hcomp ζ le_rfl hα
    apply hroot α hαG hα0
    have h := RelativeRoot.comp_mem_subgroup iM α j hm
    rwa [hcomp] at h
  have hZM : centralizerPoints iM ≤ N.comap (rationalPoints.map j) := by
    intro z hz
    apply hZ
    rw [← torusCentralizer_carrier_base]
    intro U a t
    apply (commute_iff_eq _ _).mpr
    have hc := centralizerPoints_le_torusCentralizer iM hz U a t
    have he := congrArg (fun x => x ≫ j.hom.hom) hc.eq
    simpa only [← hcomp, rationalPoints.map_apply, Grp.comp_hom_hom,
      MonObj.mul_comp, Category.assoc] using he
  have htotal : (⊤ : Subgroup (rationalPoints M)) ≤
      N.comap (rationalPoints.map j) := by
    rw [← relativeRootGeneratedSubgroup_sup_centralizerPoints hM hiM]
    exact sup_le hrootsM hZM
  intro g hg
  obtain ⟨m, rfl⟩ := SubgroupFunctor.mem_range.mp (hj.2.symm ▸ hg)
  exact htotal (Subgroup.mem_top m)

end Langlands.GroupScheme
