import Langlands.Representation.Aubert.General.RationalLeviCuspidalEmbedding
import Langlands.Representation.Aubert.General.RationalSupportInduction
import Langlands.Representation.Aubert.General.RationalSupercuspidalInductionFiniteLengthStatement
import Langlands.Representation.Aubert.General.InductionEmbeddings
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Smooth.FiniteLengthGrothendieckIso

/-! # Standard irreducible induction from cuspidal induction -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)

local instance pointTopologyForIrreducibleInduction :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
    [NonarchimedeanGroup (RationalPoint k G.X)]
    [T2Space (RationalPoint k G.X)]

/-- An actual induced ambient representation of finite length and an injective
intertwiner into it from the original standard induced representation. -/
structure StandardIrreducibleInductionEmbedding
    (K : Finset (SimpleRoot i ν))
    (h : IsSemidirectDecomposition (parabolic i ν K) (levi i ν K) (unipotent i ν K))
    (hc : IsClosed (unipotent i ν K : Set (RationalPoint k G.X)))
    (τ : SmoothRep.{0, u, uV} ℂ (levi i ν K)) where
  coefficient : SmoothRep.{0, u, max (u + 1) uV} ℂ (levi i ν K)
  map : ((normalizedInductionFunctor.{u, uV} h hc).obj τ).representation.IntertwiningMap
    ((normalizedInductionFunctor.{u, max (u + 1) uV} h hc).obj coefficient).representation
  injective : Function.Injective map
  finiteLength :
    ((normalizedInductionFunctor.{u, max (u + 1) uV} h hc).obj coefficient).HasFiniteLength

/-- Choose actual finite-length induction and an injective induced intertwiner
using cuspidal embedding and induction in stages. -/
def standardIrreducibleInductionEmbedding
    (hSuper : RationalSupercuspidalInductionFiniteLengthStatement.{u, max (u + 1) uV})
    (hStandard : StandardCocharacterStatement.{u})
    (hInter : StandardLeviIntersectionStatement.{u})
    (hRoots : haveI := hi.isSplitSubtorus.mono; HasRelativeRootSystem i)
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
    (K : Finset (SimpleRoot i ν))
    (hCompact : ∀ I : Finset K, CompactSpace
      (Induction.LeftQuotient ((parabolic i ν (leviIndex K I)).subgroupOf (levi i ν K))))
    (τ : SmoothRep.{0, u, uV} ℂ (levi i ν K)) (hτ : τ.IsIrreducible) :
    StandardIrreducibleInductionEmbedding i ν K
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν K) (hU K) τ := by
  classical
  apply Classical.choice
  have := hi.isSplitSubtorus.mono
  let τ' := SmoothRep.universeLift.{u + 1} τ
  have hτ' : τ'.IsIrreducible := (SmoothRep.isIrreducible_universeLift_iff τ).mpr hτ
  obtain ⟨I, σ, hσ, hcusp, f, hf⟩ :=
    exists_cuspidal_embedding_in_levi.{u, max (u + 1) uV}
      i ν hInter hG hi hν hStandard hU hM K hCompact τ' hτ'
  have hσfl := hSuper k G hG T i hi ν hν hStandard hInter hRoots hU hM
    (leviIndex K I) σ hσ hcusp
  let stages := (standardInductionStagesIso_of_standardData.{u, uV}
    i ν hStandard hG hi hν hInter hU K I (hM K)).app σ
  have hB := SmoothRep.hasFiniteLength_of_iso stages.symm hσfl
  let e := SmoothRep.universeLiftEquiv.{u + 1} τ
  let g := (SmoothRep.hom f).comp e.toIntertwiningMap
  exact ⟨⟨_, normalizedInductionMap _ _ g,
    normalizedInductionMap_injective _ _ g (hf.comp e.injective), hB⟩⟩

/-- Finite length descends along the chosen actual induced embedding. -/
theorem standardIrreducibleInduction_hasFiniteLength
    (hSuper : RationalSupercuspidalInductionFiniteLengthStatement.{u, max (u + 1) uV})
    (hStandard : StandardCocharacterStatement.{u})
    (hInter : StandardLeviIntersectionStatement.{u})
    (hRoots : haveI := hi.isSplitSubtorus.mono; HasRelativeRootSystem i)
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
    (K : Finset (SimpleRoot i ν))
    (hCompact : ∀ I : Finset K, CompactSpace
      (Induction.LeftQuotient ((parabolic i ν (leviIndex K I)).subgroupOf (levi i ν K))))
    (τ : SmoothRep.{0, u, uV} ℂ (levi i ν K)) (hτ : τ.IsIrreducible) :
    ((normalizedInductionFunctor.{u, uV}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν K) (hU K)).obj τ).HasFiniteLength := by
  let E := standardIrreducibleInductionEmbedding i ν hG hi hν
    hSuper hStandard hInter hRoots hU hM K hCompact τ hτ
  exact IsFiniteLength.of_injective E.finiteLength
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ E.map) E.injective

end Langlands.Aubert.General.RationalPointFamily
