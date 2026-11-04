import Langlands.Representation.Aubert.General.RationalCuspidalJacquetFactorTarget
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.Representation.Filtration.ExactSmoothSubquotients
import Langlands.Representation.Filtration.SubquotientAlgebraProof

/-! # Reduction of actual cuspidal factor extraction to the induced object -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe uI uG uV u v

open CategoryTheory

namespace Langlands.Aubert.General

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {ι : Type uI}

variable (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hM : ∀ I, IsClosed (M I : Set G))
  (hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I))
      ((U (leviIndex I K)).subgroupOf (M I)))
  (IsAssociate : Finset ι → Finset ι → G → Prop)

/-- The factor-extraction assertion restricted to the Jacquet module of the
whole actual induction. This is a proposition template, not an assertion for
arbitrary subgroup families. -/
def InducedCuspidalJacquetFactorExtractionTarget : Prop :=
  ∀ (I J : Finset ι) (σ : SmoothRep.{0, uG, max uG uV} ℂ (M I))
    (τ : SmoothRep.{0, uG, max uG uV} ℂ (M J)),
    σ.IsIrreducible → IsLeviCuspidal P M U hU I (hM I) (hL I) σ →
    τ.IsIrreducible → IsLeviCuspidal P M U hU J (hM J) (hL J) τ →
    SmoothRep.IsSubquotient τ
      ((jacquetFunctor.{uG, max uG uV} (h J) (hU J)).obj
        ((normalizedInductionFunctor.{uG, max uG uV} (h I) (hU I)).obj σ)) →
    ∃ (n : G) (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
      IsAssociate I J n ∧ Nonempty (τ ≅ (conjugationFunctor n hn).obj σ)

/-- Exactness and transitivity put every factor of `r_J π`, for an arbitrary
actual subquotient `π` of `i_I σ`, in the actual object `r_J i_I σ`. -/
theorem isSubquotient_jacquet_induction_of_exact
    (hExact : ∀ J, Derivative.Mirabolic.MapsShortExactIntertwiners
      (jacquetFunctor.{uG, max uG uV} (h J) (hU J)))
    {I J : Finset ι}
    {σ : SmoothRep.{0, uG, max uG uV} ℂ (M I)}
    {π : SmoothRep.{0, uG, max uG uV} ℂ G}
    {τ : SmoothRep.{0, uG, max uG uV} ℂ (M J)}
    (hπ : SmoothRep.IsSubquotient π
      ((normalizedInductionFunctor (h I) (hU I)).obj σ))
    (hτ : SmoothRep.IsSubquotient τ ((jacquetFunctor (h J) (hU J)).obj π)) :
    SmoothRep.IsSubquotient τ
      ((jacquetFunctor (h J) (hU J)).obj
        ((normalizedInductionFunctor (h I) (hU I)).obj σ)) :=
  smoothSubquotientTransitivity ℂ (M J) _ _ _ hτ
    (ExactSmoothTransport.map_isSubquotient _ (hExact J) hπ)

/-- Under full actual Jacquet exactness, extraction for arbitrary intermediate
subquotients is equivalent to extraction from the whole induced object. -/
theorem cuspidalJacquetFactorExtractionTarget_iff_induced
    (hExact : ∀ J, Derivative.Mirabolic.MapsShortExactIntertwiners
      (jacquetFunctor.{uG, max uG uV} (h J) (hU J))) :
    CuspidalJacquetFactorExtractionTarget.{uI, uG, uV}
        P M U h hU hM hL IsAssociate ↔
      InducedCuspidalJacquetFactorExtractionTarget.{uI, uG, uV}
        P M U h hU hM hL IsAssociate := by
  constructor
  · intro hExtract I J σ τ hσ hcσ hτ hcτ hSub
    apply hExtract I J σ _ τ hσ hcσ hτ hcτ _ hSub
    exact SmoothRep.isSubquotient_iff_exists.mpr
      ⟨_, 𝟙 _, 𝟙 _, Function.injective_id, Function.surjective_id⟩
  · intro hExtract I J σ π τ hσ hcσ hτ hcτ hπ hτπ
    exact hExtract I J σ τ hσ hcσ hτ hcτ
      (isSubquotient_jacquet_induction_of_exact P M U h hU hExact hπ hτπ)

end Langlands.Aubert.General

namespace Langlands.Aubert.General.RationalPointFamily

open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- The actual rational extraction assertion for `r_J i_I σ`, with exactly the
structural hypotheses and universe scope of the full extraction target. -/
def RationalInducedCuspidalJacquetFactorExtractionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      InducedCuspidalJacquetFactorExtractionTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hU := hU) (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
        (IsAssociate := rootAssociation i ν hN hZ)

/-- The reduction introduces no extra hypothesis for actual rational points:
full Jacquet exactness follows from the displayed standard-cocharacter data. -/
theorem rationalCuspidalJacquetFactorExtractionStatement_iff_induced :
    RationalCuspidalJacquetFactorExtractionStatement.{u, v} ↔
      RationalInducedCuspidalJacquetFactorExtractionStatement.{u, v} := by
  constructor
  · intro hExtract k _ _ _ _ G hG T i hi
    have := hG.isAffineHom
    have := hi.isSplitSubtorus.mono
    let : TopologicalSpace (RationalPoint k G.X) := pointTopology
    intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
    let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
    apply (cuspidalJacquetFactorExtractionTarget_iff_induced
      (parabolic i ν) (levi i ν) (unipotent i ν)
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
      hU hM (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
      (rootAssociation i ν hN hZ) ?_).mp
    · exact hExtract k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM
    · intro J A B C f g hf hg hfg
      have hex :=
        standardJacquetFunctor_map_isShortExact_of_standardCocharacterStatement
          i ν hStandard hG hi hν J (hU J) f g ⟨hf, hg, hfg⟩
      exact ⟨hex.1, hex.2.2, hex.2.1⟩
  · intro hExtract k _ _ _ _ G hG T i hi
    have := hG.isAffineHom
    have := hi.isSplitSubtorus.mono
    let : TopologicalSpace (RationalPoint k G.X) := pointTopology
    intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
    let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
    apply (cuspidalJacquetFactorExtractionTarget_iff_induced
      (parabolic i ν) (levi i ν) (unipotent i ν)
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
      hU hM (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
      (rootAssociation i ν hN hZ) ?_).mpr
    · exact hExtract k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM
    · intro J A B C f g hf hg hfg
      have hex :=
        standardJacquetFunctor_map_isShortExact_of_standardCocharacterStatement
          i ν hStandard hG hi hν J (hU J) f g ⟨hf, hg, hfg⟩
      exact ⟨hex.1, hex.2.2, hex.2.1⟩

end Langlands.Aubert.General.RationalPointFamily
