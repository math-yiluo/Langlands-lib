import Langlands.Representation.Aubert.General.RationalCuspidalEmbeddingProof
import Langlands.Representation.Category.UniverseLift

/-! # Actual cuspidal embeddings with an independent input carrier -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i)

/-- Choose an actual cuspidal inducing representation and an injective
intertwiner from the original representation, whose carrier need not dominate
the field universe. Only the inducing carrier is raised. -/
def cuspidalEmbeddingIndependentCarrier :
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (_hEndpoints : StandardParabolicEndpointsStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
      (_hCompact : ∀ I, CompactSpace (Induction.LeftQuotient (parabolic i ν I)))
      (_hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I)),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      let h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν
      let hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν
      ∀ (π : SmoothRep.{0, u, uV} ℂ (RationalPoint k G.X)), π.IsIrreducible →
        Σ I : Finset (SimpleRoot i ν),
          Σ σ : SmoothRep.{0, u, max (u + 1) uV} ℂ (levi i ν I),
            {f : π.representation.IntertwiningMap
                ((normalizedInductionFunctor.{u, max (u + 1) uV}
                  (h I) (hU I)).obj σ).representation //
              σ.IsIrreducible ∧
              IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
                hU I (hM I) (hL I) σ ∧
              Function.Injective f} := by
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hEndpoints hRoots hU hM hCompact hUc
  dsimp only
  intro π hπ
  let π' := SmoothRep.universeLift.{u + 1} π
  have hπ' : π'.IsIrreducible :=
    (SmoothRep.isIrreducible_universeLift_iff π).mpr hπ
  let witnesses := rationalCuspidalEmbedding.{u, uV}
    k G hG T i hi ν hν hStandard hInter hEndpoints hRoots hU hM hCompact hUc π' hπ'
  let I := Classical.choose witnesses
  let hI := Classical.choose_spec witnesses
  let σ := Classical.choose hI.2.2
  let hσ := Classical.choose_spec hI.2.2
  let f := Classical.choose hσ.2.2
  have hf := Classical.choose_spec hσ.2.2
  let e := SmoothRep.universeLiftEquiv.{u + 1} π
  exact ⟨I, σ, ⟨(SmoothRep.hom f).comp e.toIntertwiningMap,
    hσ.1, hσ.2.1, hf.comp e.injective⟩⟩

end Langlands.Aubert.General.RationalPointFamily
