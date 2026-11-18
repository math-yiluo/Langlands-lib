import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMapProofs
import Langlands.GroupScheme.AffinePointRingPointComparison
import Langlands.GroupScheme.AffinePointTopologicalGroup
import Langlands.GroupScheme.Rational.QuasiSplitSimplyConnectedRootGenerationProof
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Real-point topology for the components theorem -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

namespace RealPointTopology

local instance (H : GroupScheme (Spec (CommRingCat.of ℝ))) :
    Group (RingPoint ℝ H.X ℝ) := H.ringPointGroup (CommAlgCat.of ℝ ℝ)

local instance (H : GroupScheme (Spec (CommRingCat.of ℝ))) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of ℝ ℝ)) :=
  H.affinePointsTopologicalSpace (CommAlgCat.of ℝ ℝ)

local instance : IsAffine (AffineLine.scheme (Spec (CommRingCat.of ℝ))).left := by
  change IsAffine (AffineSpace PUnit (Spec (CommRingCat.of ℝ)))
  infer_instance

/-- The identity-test convention preserves the actual group-object point law. -/
def rationalRingPointMulEquiv (G : GroupScheme (Spec (CommRingCat.of ℝ))) :
    rationalPoints G ≃* RingPoint ℝ G.X ℝ where
  __ := rationalPointEquiv ℝ G.X
  map_mul' x y := by
    change ((ringTestSelfIso ℝ).hom ≫ (x * y)) ≫ 𝟙 _ =
      (((ringTestSelfIso ℝ).hom ≫ x) ≫ 𝟙 _) *
        (((ringTestSelfIso ℝ).hom ≫ y) ≫ 𝟙 _)
    simp only [Category.comp_id, MonObj.comp_mul]

variable (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left]

/-- Evaluation-topologized scheme points have their usual topological group law. -/
instance ringPointIsTopologicalGroup : IsTopologicalGroup (RingPoint ℝ G.X ℝ) := by
  let : IsTopologicalRing (CommAlgCat.of ℝ ℝ) := inferInstanceAs (IsTopologicalRing ℝ)
  let := G.affinePointsIsTopologicalGroup (CommAlgCat.of ℝ ℝ)
  apply Topology.IsInducing.isTopologicalGroup
    (G.affinePointsRingPointMulEquiv (CommAlgCat.of ℝ ℝ)).symm.toMonoidHom
  convert (G.affinePointsRingPointHomeomorph (CommAlgCat.of ℝ ℝ)).symm.isInducing using 1
  funext x
  exact (G.affinePointsRingPointHomeomorph_symm_apply (CommAlgCat.of ℝ ℝ) x).symm

/-- Real points of the actual affine line form a connected space. -/
theorem affineLine_connectedSpace :
    ConnectedSpace (RingPoint ℝ (AffineLine.scheme (Spec (CommRingCat.of ℝ))) ℝ) := by
  let e : AffineLine.scheme (Spec (CommRingCat.of ℝ)) ≅
      ringTest ℝ (MvPolynomial PUnit ℝ) :=
    (Over.isoMk (AffineSpace.SpecIso PUnit (CommRingCat.of ℝ)).symm
      (AffineSpace.SpecIso_inv_over (n := PUnit) (CommRingCat.of ℝ))).symm
  let h := ((affinePresentationPointHomeomorph ℝ ℝ (MvPolynomial PUnit ℝ) e).trans
    (specPointHomeomorph ℝ (MvPolynomial PUnit ℝ) ℝ)).trans
      (AlgPoint.polynomialPointHomeomorph PUnit)
  exact h.connectedSpace_iff.mpr inferInstance

local instance (X : Over (Spec (CommRingCat.of ℝ))) [IsAffine X.left] :
    TopologicalSpace (RationalPoint ℝ X) := rationalPointTopology ℝ X

/-- Every point admitting a root-orbit contraction belongs to the identity component. -/
theorem root_mem_connectedComponent_one
    {S : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : S.toGrp ⟶ G)
    (a : characterLattice S) {g : rationalPoints G}
    (hg : g ∈ (RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _))) :
    rationalRingPointMulEquiv G g ∈
      connectedComponent (1 : RingPoint ℝ G.X ℝ) := by
  obtain ⟨e, he, he0⟩ := (RelativeRoot.mem_subgroup i a).mp hg
  let A := AffineLine.scheme (Spec (CommRingCat.of ℝ))
  let T : Over (Spec (CommRingCat.of ℝ)) := Over.mk (𝟙 _)
  have hlift (p : T ⟶ A) : lift (𝟙 T) p = p ≫ (λ_ A).inv := by
    apply (cancel_mono (λ_ A).hom).mp
    simp
  let f : RationalPoint ℝ A → RingPoint ℝ G.X ℝ :=
    fun p => rationalRingPointMulEquiv G (lift (𝟙 T) p ≫ e)
  have hf : Continuous f := by
    change Continuous (fun p => rationalPointEquiv ℝ G.X (lift (𝟙 T) p ≫ e))
    simp_rw [hlift, Category.assoc, rationalPointEquiv_natural]
    exact (continuous_affineSchemePointMap ℝ ℝ ((λ_ A).inv ≫ e)).comp
      (rationalPointHomeomorph ℝ A).continuous
  let z : RationalPoint ℝ A := AffineLine.zeroSection _
  let o : RationalPoint ℝ A :=
    (1 : T ⟶ S.X) ≫ (CommGroupScheme.groupHom a).hom.hom ≫ AffineLine.unitInclusion _
  have hz : f z = 1 := by
    have hz' : lift (𝟙 T) z ≫ e = 1 := by
      have hu : toUnit T = 𝟙 _ := toUnit_unique _ _
      change lift (𝟙 T) (toUnit T ≫ AffineLine.zeroSection _) ≫ e = 1 at he0
      simpa only [hu, Category.id_comp] using he0
    change rationalRingPointMulEquiv G _ = 1
    rw [hz', map_one]
  have ho : f o = rationalRingPointMulEquiv G g := by
    apply congrArg (rationalRingPointMulEquiv G)
    change lift (𝟙 T)
      ((1 : T ⟶ S.X) ≫
        ((CommGroupScheme.groupHom a).hom.hom ≫ AffineLine.unitInclusion _)) ≫ e = g
    rw [← lift_whiskerLeft_assoc, he]
    simp only [T, RelativeRoot.orbit, AutomorphicAction.naturality, lift_snd, lift_fst_assoc,
      Category.id_comp, AutomorphicAction.act_one_left]
  let : ConnectedSpace (RingPoint ℝ A ℝ) := affineLine_connectedSpace
  let : ConnectedSpace (RationalPoint ℝ A) :=
    (rationalPointHomeomorph ℝ A).connectedSpace_iff.mpr inferInstance
  exact (isPreconnected_range hf).subset_connectedComponent
    ⟨z, hz⟩ ⟨o, ho⟩

/-- Rational points whose corresponding real point is in the identity component. -/
def identityComponentPreimage : Subgroup (rationalPoints G) :=
  (Subgroup.connectedComponentOfOne (RingPoint ℝ G.X ℝ)).comap
    (rationalRingPointMulEquiv G).toMonoidHom

/-- The identity component contains the subgroup generated by the root points. -/
theorem rootGenerated_le_identityComponentPreimage
    {S : CommGroupScheme (Spec (CommRingCat.of ℝ))} (i : S.toGrp ⟶ G) :
    relativeRootGeneratedSubgroup i ≤ identityComponentPreimage G := by
  rw [relativeRootGeneratedSubgroup_le_iff]
  intro a _ g hg
  exact root_mem_connectedComponent_one G i a hg

/-- Root generation makes the real points of a quasi-split simply connected
group connected, for a supplied maximal split torus. -/
theorem quasiSplitSimplyConnected_connectedSpace
    (hG : IsSimplyConnected G) (hqs : IsQuasiSplit G)
    (S : CommGroupScheme (Spec (CommRingCat.of ℝ))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) : ConnectedSpace (RingPoint ℝ G.X ℝ) := by
  have htop : relativeRootGeneratedSubgroup i = ⊤ :=
    quasiSplitSimplyConnectedRootGenerationStatement_proof ℝ G hG hqs S i hi
  have hroot : (⊤ : Subgroup (rationalPoints G)) ≤ identityComponentPreimage G :=
    htop ▸ rootGenerated_le_identityComponentPreimage G i
  apply connectedSpace_iff_connectedComponent.mpr
  refine ⟨1, Set.eq_univ_iff_forall.mpr ?_⟩
  intro g
  obtain ⟨x, rfl⟩ := (rationalRingPointMulEquiv G).surjective g
  exact hroot (show x ∈ (⊤ : Subgroup (rationalPoints G)) from trivial)

end RealPointTopology

end Langlands.GroupScheme
