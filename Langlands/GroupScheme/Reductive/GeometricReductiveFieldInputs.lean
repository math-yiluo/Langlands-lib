import Langlands.GroupScheme.Reductive.GeometricRootReflectionConstruction
import Langlands.GroupScheme.Rational.RootReflectionExistenceStatement
import Langlands.GroupScheme.Reductive.RootReducednessStatement
import Langlands.GroupScheme.Reductive.SplitRootLieLineStatement
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerReduction

/-! # Applying field structure statements in the original geometric fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

variable {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)

local instance fieldInputs_smooth_geometricFiber (s : Spec (CommRingCat.of r)) :
    Smooth (geometricFiber G s).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

local instance fieldInputs_affine_geometricFiber (s : Spec (CommRingCat.of r)) :
    IsAffineHom (geometricFiber G s).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

variable [hi : IsClosedImmersion i.hom.hom.left] (s : Spec (CommRingCat.of r))

local instance fieldInputs_mono :
    Mono (geometricIdentityComponentHom I G i s).hom.hom.left := by
  let : IsClosedImmersion (geometricIdentityComponentHom I G i s).hom.hom.left :=
    isClosedSubgroup_geometricIdentityComponentHom I G i hi s
  infer_instance

/-- Apply the universal forward reflection statement to the actual reductive
geometric identity component and the supplied self-centralizing torus. -/
def geometricFieldReflectionData
    (hReflection : RelativeRootReflectionExistenceStatement.{u})
    (hs : s ∈ identityComponentReductiveLocus G)
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i) :
    RelativeRootReflectionData (T := commGroupScheme _ I)
      (geometricIdentityComponentHom I G i s) := by
  let k := AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)
  have hmax := isMaximalTorus_geometricIdentityComponentHom_of_mem I G i hi s hself
  exact Classical.choose (hReflection k (identityComponent (geometricFiber G s)) hs
    (commGroupScheme _ I) (geometricIdentityComponentHom I G i s)
    (hmax.isMaximalSplitTorus (isSplitTorus_splitTorus I)))

omit [DecidableEq I] in
/-- Actual root reducedness gives the required equality of original integral
exponent vectors, with its equality-or-opposite orientation preserved. -/
theorem geometricExponentRoots_reduced_of_fieldStatement
    (hReduced : RootReducednessStatement.{u})
    (hs : s ∈ identityComponentReductiveLocus G)
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i)
    (m : I → ℤ) (hm : m ∈ geometricExponentRoots I G i s)
    (a : I → ℤ) (ha : a ∈ geometricExponentRoots I G i s)
    (hdep : ¬ LinearIndependent ℤ ![
      exponentCharacter
        (Spec (CommRingCat.of (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) I m,
      exponentCharacter
        (Spec (CommRingCat.of (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)))) I a]) :
    a = m ∨ a = -m := by
  let k := AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)
  have hmax := isMaximalTorus_geometricIdentityComponentHom_of_mem I G i hi s hself
  rcases hReduced k (identityComponent (geometricFiber G s)) hs (commGroupScheme _ I)
      (isSplitTorus_splitTorus I) (geometricIdentityComponentHom I G i s) hmax
      (exponentCharacter _ I m) hm (exponentCharacter _ I a) ha hdep with h | h
  · left
    have h' := congrArg (characterLatticeEquiv k I) h
    simpa only [exponentCharacter_eq_characterLatticeEquiv_symm,
      AddEquiv.apply_symm_apply] using h'.symm
  · right
    have h' : m = -a := by
      have h' := congrArg (characterLatticeEquiv k I) h
      rw [(characterLatticeEquiv k I).map_neg (exponentCharacter _ I a)] at h'
      simpa only [exponentCharacter_eq_characterLatticeEquiv_symm I k,
        AddEquiv.apply_symm_apply] using h'
    simpa only [neg_neg] using (congrArg Neg.neg h').symm

/-- A line equivalence for each actual root weight gives rank one for the
corresponding original relative exponent summand. -/
theorem exponentWeightRank_eq_one_of_fieldStatement
    (hLine : SplitRootLieLineStatement.{u})
    (hs : s ∈ identityComponentReductiveLocus G)
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i)
    (m : I → ℤ) (hm : m ∈ geometricExponentRoots I G i s) :
    exponentWeightRank I G i m s = 1 := by
  let k := AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)
  have hmax := isMaximalTorus_geometricIdentityComponentHom_of_mem I G i hi s hself
  obtain ⟨e⟩ := hLine k (identityComponent (geometricFiber G s)) hs
    (commGroupScheme _ I) (isSplitTorus_splitTorus I)
    (geometricIdentityComponentHom I G i s) hmax (exponentCharacter _ I m) hm
  rw [← finrank_weight_geometricIdentityComponentHom I G i s m]
  simpa only [Module.finrank_self] using e.symm.finrank_eq

/-- Universal field reflection, reducedness and root-line statements construct
an actual good original-base open from a supplied closed torus that is
self-centralizing at the specified original reductive geometric fibre. -/
def identityComponentReductiveNeighbourhood_of_fieldStatements
    (hReflection : RelativeRootReflectionExistenceStatement.{u})
    (hReduced : RootReducednessStatement.{u})
    (hLine : SplitRootLieLineStatement.{u})
    (hs : s ∈ identityComponentReductiveLocus G)
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i) :
    IdentityComponentReductiveOpenNeighbourhood G s :=
  identityComponentReductiveNeighbourhood_of_fieldReflectionData I G i s
    (geometricFieldReflectionData I G i s hReflection hs hself) hself
    (geometricExponentRoots_reduced_of_fieldStatement I G i s hReduced hs hself)
    (exponentWeightRank_eq_one_of_fieldStatement I G i s hLine hs hself)

/-- The self-centralization statement converts original geometric maximality
into the self-centralizing input of the good-open construction. -/
def identityComponentReductiveNeighbourhood_of_maximalFieldTorus
    (hCentralizer : AlgClosedMaximalTorusCentralizerStatement.{u})
    (hReflection : RelativeRootReflectionExistenceStatement.{u})
    (hReduced : RootReducednessStatement.{u})
    (hLine : SplitRootLieLineStatement.{u})
    (hs : s ∈ identityComponentReductiveLocus G)
    (hmax : IsMaximalTorus (T := commGroupScheme _ I)
      (geometricIdentityComponentHom I G i s)) :
    IdentityComponentReductiveOpenNeighbourhood G s :=
  identityComponentReductiveNeighbourhood_of_fieldStatements I G i s
    hReflection hReduced hLine hs
    (hCentralizer _ (identityComponent (geometricFiber G s)) hs
      (commGroupScheme _ I) (geometricIdentityComponentHom I G i s) hmax)

end Langlands.GroupScheme.splitTorus
