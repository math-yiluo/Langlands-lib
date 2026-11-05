import Langlands.Group.RelativeWeylSolomonProof
import Langlands.Representation.Aubert.General.RationalJacquetGeometricCommon
import Langlands.Representation.Aubert.General.RationalSourceJacquet
import Langlands.Representation.Aubert.General.TargetInductionComparison
import Langlands.Representation.Classification.SupercuspidalSupport

/-! # Actual standard induction and exclusion for rational geometric targets -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open Classical CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) C)
  (hSource : PointSourceIntersectionIdentities i ν cs)
  [TopologicalSpace k]

local instance rationalProperTargetPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))

include hSource in
/-- Every actual geometric term is an actual standard normalized induction
inside its target Levi. The input datum is unrestricted. -/
theorem exists_pointGeometricTerm_target_induction
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs J I w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w)
    (hs : GeometricSourceDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) J I n)
    (ht : GeometricTargetDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) J I n)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I)) :
    let K := intersectionLeviIndex cs I J w⁻¹
    letI := (hM J).locallyCompactSpace
    ∃ ρ : SmoothRep.{0, u, max (u + 1) v} ℂ
        ((levi i ν (leviIndex J K)).subgroupOf (levi i ν J)),
      Nonempty
        ((geometricTermFunctor.{u, u, max (u + 1) v}
          (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I n hs ht).obj σ ≅
          (normalizedInductionFunctor.{u, max (u + 1) v}
            (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
            ((hU (leviIndex J K)).preimage continuous_subtype_val)).obj ρ) := by
  let K := intersectionLeviIndex cs I J w⁻¹
  let _ := (hM J).locallyCompactSpace
  have hlabels : leviIndex J K = simpleImage cs w I ∩ J := by
    rw [leviIndex_intersectionLeviIndex,
      intersectionSubset_eq_simpleImage_inter cs (isMinimal_inv cs hw)]
    ext a
    simp only [inv_inv, Finset.mem_inter]
  obtain ⟨hL, hP, hR⟩ :=
    pointTargetIntersectionIdentities i ν cs hSource J I w hw n hn
  rw [← hlabels] at hL hP hR
  have hKJ := levi_le_of_subset i ν hInter hG hi hν
    (leviIndex J K) J (leviIndex_subset J K)
  let B := (conjugationFunctor (n : RationalPoint k G.X)
    (geometricIntersectionMembership (levi i ν J) (levi i ν I) n)).obj
      ((geometricSourceJacquetFunctor.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I n hs).obj σ)
  let ρ := (SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hKJ)).obj
    ((conjugationFunctor 1 (identityConjugationMembership hL)).obj B)
  refine ⟨ρ, ⟨?_⟩⟩
  exact ((geometricTargetInductionComparisonIso.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
    J I (leviIndex J K) n ht hKJ
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
    hL hP hR).app B).symm

/-- Proper target intersections exclude actual irreducible cuspidal
subquotients. This is an input condition until proper-induction exclusion
has been established for the literal standard families inside each Levi. -/
def PointProperTargetGeometricTermExclusion : Prop :=
  ∀ (I J : Finset (SimpleRoot i ν)) (w : Weyl i), IsMinimal cs J I w →
    ∀ (n : Group.RelativeWeyl.normalizer (torusPoints i)), QuotientGroup.mk n = w →
      ∀ (hs : GeometricSourceDecomposition
          (parabolic i ν) (levi i ν) (unipotent i ν) J I n)
        (ht : GeometricTargetDecomposition
          (parabolic i ν) (levi i ν) (unipotent i ν) J I n),
        intersectionSubset cs I J w⁻¹ ≠ J →
        ∀ (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I))
          (τ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)),
          τ.IsIrreducible →
          IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU J (hM J)
            (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) τ →
          ¬ SmoothRep.IsSubquotient τ
            ((geometricTermFunctor.{u, u, max (u + 1) v}
              (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I n hs ht).obj σ)

include hSource in
/-- A uniform proper-standard induction exclusion transfers to every actual
geometric term through an actual equivariant isomorphism. The exclusion
premise is explicit and is not proved by this transport. -/
theorem pointProperTargetGeometricTermExclusion_of_standardInduction
    (hExclude :
      ∀ (J : Finset (SimpleRoot i ν)) (K : Finset J), K ≠ Finset.univ →
        letI := (hM J).locallyCompactSpace
        ∀ (ρ : SmoothRep.{0, u, max (u + 1) v} ℂ
            ((levi i ν (leviIndex J K)).subgroupOf (levi i ν J)))
          (τ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)),
          τ.IsIrreducible →
          IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU J (hM J)
            (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) τ →
          ¬ SmoothRep.IsSubquotient τ
            ((normalizedInductionFunctor.{u, max (u + 1) v}
              (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
              ((hU (leviIndex J K)).preimage continuous_subtype_val)).obj ρ)) :
    PointProperTargetGeometricTermExclusion.{u, v}
      i ν cs hInter hG hi hν hM hU := by
  intro I J w hw n hn hs ht hproper σ τ hτ hc hsub
  let K := intersectionLeviIndex cs I J w⁻¹
  have hK : K ≠ Finset.univ := by
    intro hfull
    apply hproper
    calc
      intersectionSubset cs I J w⁻¹ = leviIndex J K :=
        (leviIndex_intersectionLeviIndex cs I J w⁻¹).symm
      _ = J := by
        rw [hfull]
        ext a
        simp [leviIndex]
  obtain ⟨ρ, ⟨e⟩⟩ := exists_pointGeometricTerm_target_induction
    i ν cs hSource hInter hG hi hν hM hU I J w hw n hn hs ht σ
  exact hExclude J K hK ρ τ hτ hc (hsub.of_iso_right e)

end Langlands.Aubert.General.RationalPointFamily
