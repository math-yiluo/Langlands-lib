import Langlands.Representation.Aubert.General.Endpoint
import Langlands.Representation.Aubert.General.RationalAlternatingOperator
import Langlands.GroupScheme.Rational.EndpointReductions

/-! # Actual full-index and empty-root identities on rational-point K0 -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- At the full simple-root index, the actual standard parabolic is G(k). -/
theorem parabolic_univ_eq_top [Fintype (SimpleRoot i ν)]
    (hStandard : StandardCocharacterStatement.{u}) (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) :
    parabolic i ν Finset.univ = ⊤ := by
  have hfull := (hStandard k G hG T i hi ν hν _ Set.Subset.rfl).2
    0 (isStandardCocharacter_simple_zero i ν)
  change (standardParabolic i ν (rootSet i ν Finset.univ)).carrier
    (Over.mk (𝟙 _)) = ⊤
  rw [rootSet_univ, hfull.1, groupHom_zero_comp_eq_trivialCocharacter,
    Dynamic.parabolic_trivialCocharacter]
  rfl

/-- At the full simple-root index, the actual standard Levi is G(k). -/
theorem levi_univ_eq_top [Fintype (SimpleRoot i ν)]
    (hStandard : StandardCocharacterStatement.{u}) (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) :
    levi i ν Finset.univ = ⊤ := by
  have hfull := (hStandard k G hG T i hi ν hν _ Set.Subset.rfl).2
    0 (isStandardCocharacter_simple_zero i ν)
  change (standardLevi i ν (rootSet i ν Finset.univ)).carrier
    (Over.mk (𝟙 _)) = ⊤
  rw [rootSet_univ, hfull.2.1, groupHom_zero_comp_eq_trivialCocharacter,
    Dynamic.centralizer_trivialCocharacter]
  rfl

/-- The actual full-index radical is the trivial subgroup. -/
theorem unipotent_univ_eq_bot [Fintype (SimpleRoot i ν)] :
    unipotent i ν Finset.univ = ⊥ := by
  change (standardUnipotent i ν (rootSet i ν Finset.univ)).carrier
    (Over.mk (𝟙 _)) = ⊥
  rw [rootSet_univ, standardUnipotent_simple_eq_bot]
  rfl

section Topology

variable [TopologicalSpace k]

local instance : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hproj : ∀ I, Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I).projection)
  (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
  (hiFl : ∀ I, PreservesFiniteLength
    (normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
      (hU I)))
  (hrFl : ∀ I, PreservesFiniteLength
    (jacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
      (hU I)))

/-- The actual full-index normalized induction after Jacquet restriction is
isomorphic to the original rational-point representation. -/
def fullIndexInductionJacquetIso [Fintype (SimpleRoot i ν)]
    (A : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) :
    (inductionJacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν Finset.univ) (hU Finset.univ)).obj A ≅ A :=
  endpointInductionJacquetIso _ _
    (parabolic_univ_eq_top i ν hStandard hG hi hν)
    (levi_univ_eq_top i ν hStandard hG hi hν)
    (unipotent_univ_eq_bot i ν) A

/-- The actual full-index normalized induction-Jacquet term is the identity on
all of exact finite-length K0, under the original visible premises. -/
theorem alternatingTerm_univ_eq_id [Fintype (SimpleRoot i ν)] :
    alternatingTerm.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν)
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
      (standardParabolicFiniteLength i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
      Finset.univ = LinearMap.id :=
  endpoint_inductionK0_comp_jacquetK0 _ _
    (parabolic_univ_eq_top i ν hStandard hG hi hν)
    (levi_univ_eq_top i ν hStandard hG hi hν)
    (unipotent_univ_eq_bot i ν)
    (standardParabolicFiniteLength i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl _)

variable [Mono i.hom.hom.left] (hRoots : HasRelativeRootSystem i)

/-- With no simple roots, the actual rational alternating operator equals the
identity on the whole exact Grothendieck group. -/
theorem rationalAlternatingOperator_eq_id_of_isEmpty [IsEmpty (SimpleRoot i ν)] :
    rationalAlternatingOperator.{u, v}
      i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl hRoots = LinearMap.id := by
  let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  rw [rationalAlternatingOperator_of_isEmpty]
  have huniv : (Finset.univ : Finset (SimpleRoot i ν)) = ∅ := by
    ext a
    exact isEmptyElim a
  simpa only [huniv] using
    alternatingTerm_univ_eq_id i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl

/-- The empty-root case of the exact rational involutivity conclusion. -/
theorem rationalAlternatingOperator_sq_eq_id_of_isEmpty [IsEmpty (SimpleRoot i ν)] :
    let D := rationalAlternatingOperator.{u, v}
      i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl hRoots
    D.comp D = LinearMap.id := by
  dsimp only
  rw [rationalAlternatingOperator_eq_id_of_isEmpty
    i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl hRoots]
  rfl

end Topology

end Langlands.Aubert.General.RationalPointFamily
