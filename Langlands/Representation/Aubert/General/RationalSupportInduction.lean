import Langlands.Representation.Aubert.General.RationalInductionStages
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.Representation.Filtration.ExactSmoothSubquotients
import Langlands.Representation.Filtration.SubquotientAlgebraProof

/-! # Actual induction and subquotients from standard rational data -/

noncomputable section

universe u v

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
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

local instance rationalSupportInductionPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

include hStandard hG hi hν in
/-- The standard parabolic is closed in the canonical point topology. -/
theorem standardParabolic_isClosed_of_standardCocharacterStatement
    (I : Finset (SimpleRoot i ν)) :
    IsClosed (parabolic i ν I : Set (RationalPoint k G.X)) := by
  let : T2Space k := BruhatTits.localField_t2Space k
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨hexists, hcompare⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨ζ, hζ⟩ := hexists
  obtain ⟨hP, _, _⟩ := hcompare ζ hζ
  change IsClosed
    ((standardParabolic i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _)) :
      Set (RationalPoint k G.X))
  rw [hP]
  exact isClosed_dynamic_parabolic k G (CommGroupScheme.groupHom ζ ≫ i)

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  [T2Space (RationalPoint k G.X)]

local notation "dec" => isSemidirectDecomposition_of_standardCocharacterStatement
  i ν hStandard hG hi hν

/-- Actual standard induction preserves every short exact sequence. -/
theorem standardInduction_mapsShortExact_of_standardData
    (I : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X))) :
    Derivative.Mirabolic.MapsShortExactIntertwiners
      (normalizedInductionFunctor.{u, max (u + 1) v} (dec I) hU) := by
  intro A B C f g hf hg hex
  have h := normalizedInductionFunctor_map_isShortExact
    (compactOpenCofinal_of_nonarchimedean _) (dec I) hU
    (standardParabolic_isClosed_of_standardCocharacterStatement
      i ν hStandard hG hi hν I)
    (continuous_standard_projection i ν hStandard hG hi hν I)
    f g ⟨hf, hg, hex⟩
  exact ⟨h.1, h.2.2, h.2.1⟩

/-- Actual standard induction preserves actual subquotients of arbitrary
smooth representations, at the carrier universe of the support targets. -/
theorem standardInduction_isSubquotient_of_standardData
    (I : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    {A B : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I)}
    (hBA : IsSubquotient B A) :
    IsSubquotient ((normalizedInductionFunctor (dec I) hU).obj B)
      ((normalizedInductionFunctor (dec I) hU).obj A) :=
  ExactSmoothTransport.map_isSubquotient _
    (standardInduction_mapsShortExact_of_standardData.{u, v}
      i ν hStandard hG hi hν I hU) hBA

/-- The actual induction-in-stages isomorphism needs only the standard data
and closedness hypotheses displayed in the support targets. -/
def standardInductionStagesIso_of_standardData
    (hInter : StandardLeviIntersectionStatement.{u})
    (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
    (K : Finset (SimpleRoot i ν)) (J : Finset K)
    (hM : IsClosed (levi i ν K : Set (RationalPoint k G.X))) :
    leviNormalizedInductionFunctor.{u, max (u + 1) v} hM
        (levi_le_of_subset i ν hInter hG hi hν _ K (leviIndex_subset K J))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν K J)
        (hU (leviIndex K J)) ⋙
      normalizedInductionFunctor (dec K) (hU K) ≅
    normalizedInductionFunctor (dec (leviIndex K J)) (hU (leviIndex K J)) :=
  standardInductionStagesIso.{u, v} i ν hInter hG hi hν hStandard hU
    (continuous_standard_projection i ν hStandard hG hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν hStandard hG hi hν) K J hM
    (isLimitOfCompactSubgroups_subgroupOf _ _ hM
      (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν hStandard hG hi hν (leviIndex K J)))

/-- A subquotient presentation inside a standard Levi becomes an actual
ambient induction subquotient presentation. -/
theorem standardInduction_stages_isSubquotient_of_standardData
    (hInter : StandardLeviIntersectionStatement.{u})
    (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
    (K : Finset (SimpleRoot i ν)) (J : Finset K)
    (hM : IsClosed (levi i ν K : Set (RationalPoint k G.X)))
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν (leviIndex K J)))
    (τ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν K))
    (hτ : IsSubquotient τ
      ((leviNormalizedInductionFunctor hM
        (levi_le_of_subset i ν hInter hG hi hν _ K (leviIndex_subset K J))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν K J)
        (hU (leviIndex K J))).obj σ)) :
    IsSubquotient ((normalizedInductionFunctor (dec K) (hU K)).obj τ)
      ((normalizedInductionFunctor (dec (leviIndex K J))
        (hU (leviIndex K J))).obj σ) := by
  let F := leviNormalizedInductionFunctor.{u, max (u + 1) v} hM
    (levi_le_of_subset i ν hInter hG hi hν _ K (leviIndex_subset K J))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν K J)
    (hU (leviIndex K J))
  have h : IsSubquotient ((normalizedInductionFunctor (dec K) (hU K)).obj τ)
      ((F ⋙ normalizedInductionFunctor (dec K) (hU K)).obj σ) :=
    standardInduction_isSubquotient_of_standardData.{u, v}
      i ν hStandard hG hi hν K (hU K) (A := F.obj σ) (B := τ) hτ
  let e : (F ⋙ normalizedInductionFunctor (dec K) (hU K)).obj σ ≅
      (normalizedInductionFunctor (dec (leviIndex K J))
        (hU (leviIndex K J))).obj σ :=
    (standardInductionStagesIso_of_standardData.{u, v}
      i ν hStandard hG hi hν hInter hU K J hM).app σ
  exact h.of_iso_right e

/-- The same actual presentation also contains every subquotient of the
outer induction of the supplied Levi representation. -/
theorem standardInduction_stages_subquotient_transitive_of_standardData
    (hInter : StandardLeviIntersectionStatement.{u})
    (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
    (K : Finset (SimpleRoot i ν)) (J : Finset K)
    (hM : IsClosed (levi i ν K : Set (RationalPoint k G.X)))
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν (leviIndex K J)))
    (τ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν K))
    (π : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
    (hτ : IsSubquotient τ
      ((leviNormalizedInductionFunctor hM
        (levi_le_of_subset i ν hInter hG hi hν _ K (leviIndex_subset K J))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν K J)
        (hU (leviIndex K J))).obj σ))
    (hπ : IsSubquotient π
      ((normalizedInductionFunctor (dec K) (hU K)).obj τ)) :
    IsSubquotient π
      ((normalizedInductionFunctor (dec (leviIndex K J))
        (hU (leviIndex K J))).obj σ) :=
  smoothSubquotientTransitivity ℂ (RationalPoint k G.X) _ _ _ hπ
    (standardInduction_stages_isSubquotient_of_standardData.{u, v}
      i ν hStandard hG hi hν hInter hU K J hM σ τ hτ)

end Langlands.Aubert.General.RationalPointFamily
