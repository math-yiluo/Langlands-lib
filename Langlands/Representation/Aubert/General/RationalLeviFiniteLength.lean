import Langlands.Representation.Aubert.General.RationalLeviDecomposition

/-! # Exactness and the alternating operator inside actual standard Levis -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance rationalLeviPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (J : Finset (SimpleRoot i ν))
  (hM : IsClosed (levi i ν J : Set (RationalPoint k G.X)))

variable
  (hproj : ∀ I : Finset J, Continuous (standardLeviProjection i ν hInter hG hi hν J I))
  (hUc : ∀ I : Finset J, Jacquet.Localization.IsLimitOfCompactSubgroups
    ((unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)))
  (hiFl : letI := hM.locallyCompactSpace
    ∀ I : Finset J, PreservesFiniteLength
    (normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
      ((hU (leviIndex J I)).preimage continuous_subtype_val)))
  (hrFl : letI := hM.locallyCompactSpace
    ∀ I : Finset J, PreservesFiniteLength
    (jacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
      ((hU (leviIndex J I)).preimage continuous_subtype_val)))

include hP hproj hUc hiFl hrFl in
/-- Restricted exactness follows from the existing topological exactness
proofs inside the closed Levi; finite-length preservation remains explicit. -/
theorem standardLeviParabolicFiniteLength (I : Finset J) :
    letI := hM.locallyCompactSpace
    ParabolicFiniteLength.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
      ((hU (leviIndex J I)).preimage continuous_subtype_val) := by
  let _ := hM.locallyCompactSpace
  exact ParabolicFiniteLength.of_preservesFiniteLength
    (compactOpenCofinal_of_nonarchimedean _)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
    ((hU (leviIndex J I)).preimage continuous_subtype_val)
    ((hP (leviIndex J I)).preimage continuous_subtype_val)
    (hproj I) (hUc I) (hiFl I) (hrFl I)

/-- The unadjusted operator of the actual standard Levi, with restricted
subgroups and decomposition derived from the named intersection statement. -/
def rationalLeviAlternatingOperator :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) :=
  letI := hM.locallyCompactSpace
  leviAlternatingOperator.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) J hM
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU
    (standardLeviParabolicFiniteLength i ν hInter hG hi hν hU hP J hM
      hproj hUc hiFl hrFl)

end Langlands.Aubert.General.RationalPointFamily
