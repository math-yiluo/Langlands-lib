import Langlands.GroupScheme.Torus.GeometricAdjointWeightRanks
import Langlands.GroupScheme.Torus.SelfCentralizingFromLie
import Langlands.GroupScheme.Lie.IdentityComponentWeights
import Langlands.GroupScheme.Lie.SplitTorusCoordinates

/-! # Openness of the actual fibrewise self-centralizing split-torus locus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

variable {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)

local instance affine_standardTorus (S : Scheme.{u}) :
    IsAffineHom (splitTorus S I).X.hom := isAffineHom_splitTorus S I

local instance affine_commStandardTorus (S : Scheme.{u}) :
    IsAffineHom (commGroupScheme S I).X.hom := isAffineHom_splitTorus S I

local instance smooth_actualGeometricFiber (s : Spec (CommRingCat.of r)) :
    Smooth (geometricFiber G s).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

local instance affine_actualGeometricFiber (s : Spec (CommRingCat.of r)) :
    IsAffineHom (geometricFiber G s).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

/-- The actual split-torus map in the identity component of the actual chosen
geometric fibre. -/
def geometricIdentityComponentHom (s : Spec (CommRingCat.of r)) :
    splitTorus
        (Spec (CommRingCat.of
          (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) I ⟶
      identityComponent (geometricFiber G s) :=
  IdentityComponent.torusHom
    (T := commGroupScheme _ I) (geometricFiberHom I G i s)
    (isSplitTorus_splitTorus I)

omit [DecidableEq I] in
@[reassoc (attr := simp)] theorem geometricIdentityComponentHom_comp
    (s : Spec (CommRingCat.of r)) :
    geometricIdentityComponentHom I G i s ≫ identityComponentι (geometricFiber G s) =
      geometricFiberHom I G i s :=
  IdentityComponent.torusHom_comp _ _

omit [DecidableEq I] [Smooth G.X.hom] [IsAffineHom G.X.hom] in
theorem isClosedSubgroup_geometricFiberHom (hi : IsClosedSubgroup i)
    (s : Spec (CommRingCat.of r)) :
    IsClosedSubgroup (geometricFiberHom I G i s) :=
  (IsClosedSubgroup.of_iso (baseChangeIso (geometricPoint _ s) I).symm).comp
    (hi.baseChange (geometricPoint _ s))

omit [DecidableEq I] in
theorem isClosedSubgroup_geometricIdentityComponentHom (hi : IsClosedSubgroup i)
    (s : Spec (CommRingCat.of r)) :
    IsClosedSubgroup (geometricIdentityComponentHom I G i s) :=
  IdentityComponent.isClosedSubgroup_torusHom _ _
    (isClosedSubgroup_geometricFiberHom I G i hi s)

/-- The actual zero weight in the fibre identity component has exactly the
relative zero-exponent rank. -/
theorem finrank_zeroWeight_geometricIdentityComponentHom
    (s : Spec (CommRingCat.of r)) :
    Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))
        (weightSpace (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s) 0) =
      exponentWeightRank I G i 0 s := by
  calc
    _ = Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))
        (weightSpace (T := commGroupScheme _ I) (geometricFiberHom I G i s) 0) :=
      IdentityComponent.finrank_weightSpace _ _ _
    _ = geometricExponentWeightRankProfile I G i s 0 := by
      dsimp only [geometricExponentWeightRankProfile]
      rw [map_zero]
    _ = _ := geometricExponentWeightRankProfile_apply I G i s 0

/-- Points where the given torus is its whole centralizer inside the actual
geometric identity component. -/
def geometricSelfCentralizingTorusLocus : Set (Spec (CommRingCat.of r)) :=
  {s | torusCentralizer (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s) =
    SubgroupFunctor.range (geometricIdentityComponentHom I G i s)}

/-- Actual all-test selfcentralizing equality is exactly the relative
zero-weight rank condition. -/
theorem mem_geometricSelfCentralizingTorusLocus_iff
    (hi : IsClosedSubgroup i) (s : Spec (CommRingCat.of r)) :
    s ∈ geometricSelfCentralizingTorusLocus I G i ↔
      exponentWeightRank I G i 0 s = Nat.card I := by
  let k := AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)
  have hc := isClosedSubgroup_geometricIdentityComponentHom I G i hi s
  let : IsClosedImmersion (geometricIdentityComponentHom I G i s).hom.hom.left := hc
  let : Mono (geometricIdentityComponentHom I G i s).hom.hom := Over.mono_of_mono_left _
  have hdim : Module.finrank k (Additive (lieKernel (splitTorus
      (Spec (CommRingCat.of k)) I) k)) = Nat.card I :=
    finrank_lieKernel I k
  constructor
  · intro hs
    have hzero := Lie.finrank_zeroWeight_of_selfCentralizing
      (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s) hs
    exact (finrank_zeroWeight_geometricIdentityComponentHom I G i s).symm.trans
      (hzero.trans hdim)
  · intro hs
    exact torusCentralizer_eq_range_of_finrank_zeroWeight
      (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s)
      (isSplitTorus_splitTorus I) hc
      ((finrank_zeroWeight_geometricIdentityComponentHom I G i s).trans
        (hs.trans hdim.symm))

/-- For any supplied actual closed split torus, its selfcentralizing locus
in actual geometric identity components is open over an arbitrary base ring. -/
theorem isOpen_geometricSelfCentralizingTorusLocus (hi : IsClosedSubgroup i) :
    IsOpen (geometricSelfCentralizingTorusLocus I G i) := by
  have heq : geometricSelfCentralizingTorusLocus I G i =
      {s | exponentWeightRank I G i 0 s = Nat.card I} := by
    ext s
    exact mem_geometricSelfCentralizingTorusLocus_iff I G i hi s
  rw [heq]
  exact (isLocallyConstant_exponentWeightRank I G i 0).isOpen_fiber _

omit [DecidableEq I] in
/-- Every actual torus in this open locus is geometrically maximal in the
corresponding identity component. -/
theorem isMaximalTorus_geometricIdentityComponentHom_of_mem
    (hi : IsClosedSubgroup i) (s : Spec (CommRingCat.of r))
    (hs : s ∈ geometricSelfCentralizingTorusLocus I G i) :
    IsMaximalTorus (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s) :=
  isMaximalTorus_of_torusCentralizer_eq
    (isSplitTorus_splitTorus I).isTorus
    (isClosedSubgroup_geometricIdentityComponentHom I G i hi s) hs

end Langlands.GroupScheme.splitTorus
