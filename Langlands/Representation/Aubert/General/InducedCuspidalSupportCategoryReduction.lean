import Langlands.Representation.Aubert.General.InducedCuspidalSupportCategoryStatement
import Langlands.Representation.Aubert.General.RationalCuspidalExtractionInputs
import Langlands.Representation.Aubert.General.RationalLeviInductionExclusionFromWhole
import Langlands.Representation.Aubert.General.RationalCuspidalJacquetSubquotient
import Langlands.Representation.Aubert.General.CuspidalQuotientEmbedding
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction
import Langlands.Representation.Aubert.General.ConjugationComposition
import Langlands.Representation.Tensor.SmoothSubquotients
import Langlands.BruhatTits.Parabolic.QuotientCompactProof

/-! # Induced inside-Levi cuspidal representations lie in `Alg({K})`, from the extraction inputs -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe uI uG uV u v

open CategoryTheory AlgebraicGeometry
namespace Langlands.Aubert.General

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {Index : Type uI}

/-- An irreducible inside-Levi cuspidal subquotient of an object with supplied
cuspidal graded pieces is a subquotient of a conjugate of the inducing datum.
The inducing datum need not be irreducible. -/
theorem exists_conjugation_isSubquotient_of_gradedPieces
    {P M U : Finset Index → Subgroup G}
    {hU : ∀ I, IsClosed (U I : Set G)}
    {hM : ∀ I, IsClosed (M I : Set G)}
    {hL : ∀ (I : Finset Index) (K : Finset I),
      IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
        ((M (leviIndex I K)).subgroupOf (M I))
        ((U (leviIndex I K)).subgroupOf (M I))}
    {IsAssociate : Finset Index → Finset Index → G → Prop}
    {I J : Finset Index}
    {σ : SmoothRep.{0, uG, max uG uV} ℂ (M I)}
    {ρ A : SmoothRep.{0, uG, max uG uV} ℂ (M J)}
    {r : ℕ} (s : ObjectRepFiltration A.obj r)
    (hρ : ρ.IsIrreducible)
    (hcρ : IsLeviCuspidal P M U hU J (hM J) (hL J) ρ)
    (hρA : SmoothRep.IsSubquotient ρ A)
    (hgrades : CuspidalJacquetGradedPieces P M U hU hM hL IsAssociate I J σ s) :
    ∃ (n : G) (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
      IsAssociate I J n ∧
      SmoothRep.IsSubquotient ρ ((conjugationFunctor n hn).obj σ) := by
  obtain ⟨j, hρj⟩ := s.exists_smoothGradedObject_subquotient hρ hρA
  rcases hgrades j with hno | ⟨n, hn, hassoc, ⟨e⟩⟩
  · exact (hno ρ hρ hcρ hρj).elim
  · exact ⟨n, hn, hassoc, hρj.of_iso_right e⟩

/-- Pull an irreducible subquotient of a conjugate datum back to an irreducible
inside-Levi cuspidal subquotient `σ` of the datum itself. The conjugate of `σ`
by `(n⁻¹)⁻¹` is the original subquotient, so an induction containing `π`
along the target Levi contains it along that conjugate. -/
theorem exists_inducedConjugate_of_conjugation_isSubquotient
    {P M U : Finset Index → Subgroup G}
    (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
    (hU : ∀ I, IsClosed (U I : Set G))
    {I J : Finset Index} {hM : IsClosed (M I : Set G)}
    {hI : ∀ K : Finset I,
      IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
        ((M (leviIndex I K)).subgroupOf (M I))
        ((U (leviIndex I K)).subgroupOf (M I))}
    (hUc : ∀ K : Finset I, Jacquet.Localization.IsLimitOfCompactSubgroups
      ((U (leviIndex I K)).subgroupOf (M I)))
    {τ : SmoothRep.{0, uG, max uG uV} ℂ (M I)}
    {ρ : SmoothRep.{0, uG, max uG uV} ℂ (M J)}
    {π : SmoothRep.{0, uG, max uG uV} ℂ G}
    (hcτ : IsLeviCuspidal P M U hU I hM hI τ)
    (hρ : ρ.IsIrreducible)
    (n : G) (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I)
    (hρn : SmoothRep.IsSubquotient ρ ((conjugationFunctor n hn).obj τ))
    (hπ : SmoothRep.IsSubquotient π
      ((normalizedInductionFunctor.{uG, max uG uV} (h J) (hU J)).obj ρ)) :
    ∃ (hn' : ∀ x : G, x ∈ M J ↔ ((n⁻¹)⁻¹)⁻¹ * x * (n⁻¹)⁻¹ ∈ M I)
      (σ : SmoothRep.{0, uG, max uG uV} ℂ (M I)),
      σ.IsIrreducible ∧ IsLeviCuspidal P M U hU I hM hI σ ∧
        SmoothRep.IsSubquotient π
          ((normalizedInductionFunctor.{uG, max uG uV} (h J) (hU J)).obj
            ((conjugationFunctor (n⁻¹)⁻¹ hn').obj σ)) := by
  let hinv := conjugationMembership_inv n hn
  let σ : SmoothRep.{0, uG, max uG uV} ℂ (M I) := (conjugationFunctor n⁻¹ hinv).obj ρ
  have hστ : SmoothRep.IsSubquotient σ τ :=
    (hρn.pullback (conjugationEquiv n⁻¹ hinv)).of_iso_right
      (conjugationFunctorInvIsoApp n hn τ)
  have hσ : σ.IsIrreducible :=
    (Langlands.isIrreducible_comp_continuousMulEquiv_iff
      ρ.representation (conjugationEquiv n⁻¹ hinv)).mpr hρ
  refine ⟨conjugationMembership_inv n⁻¹ hinv, σ, hσ,
    IsLeviCuspidal.of_isSubquotient hUc hcτ hστ, ?_⟩
  exact hπ.of_iso_right ((normalizedInductionFunctor.{uG, max uG uV} (h J) (hU J)).mapIso
    (conjugationFunctorInvIsoApp n⁻¹ hinv ρ)).symm

end Generic

namespace RationalPointFamily

open scoped CategoryTheory.MonObj
open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

section Rational

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

local instance inducedCuspidalSupportCategoryReductionPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hRoots : HasRelativeRootSystem i)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))

local notation "hstd" =>
  isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν

local notation "hlev" => isSemidirectDecomposition_in_levi i ν hInter hG hi hν

include hRoots in
/-- An irreducible actual smooth representation `π` has a standard index `I`
and an irreducible inside-Levi cuspidal `ρ` on `M_I` which is a subquotient
(indeed a quotient) of `r_I(π)` and such that `π` is a subquotient (indeed a
subrepresentation) of `i_I(ρ)`. -/
theorem exists_cuspidal_jacquet_quotient_embedding
    (π : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (hπ : π.IsIrreducible) :
    ∃ (I : Finset (SimpleRoot i ν)) (ρ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I)),
      ρ.IsIrreducible ∧
      IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I (hM I) (hlev I) ρ ∧
      SmoothRep.IsSubquotient ρ ((jacquetFunctor.{u, max (u + 1) v} (hstd I) (hU I)).obj π) ∧
      SmoothRep.IsSubquotient π
        ((normalizedInductionFunctor.{u, max (u + 1) v} (hstd I) (hU I)).obj ρ) := by
  have : π.representation.IsIrreducible := hπ
  have : Nontrivial π := by
    have : Nontrivial π.representation.asModule :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (RationalPoint k G.X)) _
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : π.representation.asModule)
    exact nontrivial_of_ne (v₀ : π) 0 hv₀
  obtain ⟨I, hI, hcusp⟩ := exists_nontrivial_isLeviCuspidal_jacquet
    i ν hStandard hInter hRoots hG hi hν hU hM π
  have hfg : Module.Finite (MonoidAlgebra ℂ (RationalPoint k G.X))
      π.representation.asModule := inferInstance
  have := compactSpace_leftQuotient_parabolic i ν
    BruhatTits.dynamicParabolicQuotientCompact hStandard hG hi hν I
  let rI := (jacquetFunctor.{u, max (u + 1) v} (hstd I) (hU I)).obj π
  have : Nontrivial rI := hI
  have hfgI : Module.Finite (MonoidAlgebra ℂ (levi i ν I)) rI.representation.asModule :=
    JacquetFiniteGeneration.finite_of_compactQuotient (hstd I) (hU I) π hfg
  obtain ⟨ρ, hρ, q, hq⟩ := CuspidalEmbedding.exists_irreducible_quotient_of_finite rI hfgI
  have : ρ.representation.IsIrreducible := hρ
  have : Nontrivial ρ := by
    have : Nontrivial ρ.representation.asModule :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (levi i ν I)) _
    obtain ⟨w₀, hw₀⟩ := exists_ne (0 : ρ.representation.asModule)
    exact nontrivial_of_ne (w₀ : ρ) 0 hw₀
  have hδ := standardUnipotent_isUnimodular_of_standardCocharacterStatement
    i ν hStandard hG hi hν I (hU I)
  refine ⟨I, ρ, hρ, IsLeviCuspidal.of_surjective hcusp q hq,
    SmoothRep.IsQuotient.isSubquotient ⟨q, hq⟩, ?_⟩
  exact SmoothRep.IsSubrepresentation.isSubquotient
    ⟨CuspidalEmbedding.adjointOfJacquetMap.{u, max (u + 1) v} (hstd I) (hU I) hδ π ρ q,
      CuspidalEmbedding.adjointOfJacquetMap_injective.{u, max (u + 1) v} (hstd I) (hU I) hδ π hπ ρ q hq⟩

variable (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  [Fintype (SimpleRoot i ν)]

include hRoots in
/-- At one displayed datum, a geometric filtration for some actual point
Coxeter system with the root-length comparison, together with proper-standard
induction exclusion, puts the actual normalized induction of every
inside-Levi cuspidal smooth representation in the actual support category. -/
theorem inducedCuspidalSupportCategory_of_filtration_exclusion
    (hFilt : ∃ (C : CoxeterMatrix (SimpleRoot i ν))
      (cs : ActualCoxeterSystem (torusPoints i) C),
      RootLengthComparison i ν hN hZ cs ∧
        PointInducedJacquetGeometricFiltration.{u, v}
          i ν hStandard hG hi hν hM hU cs)
    (hExclude : PointLeviStandardInductionCuspidalExclusion.{u, v}
      i ν hInter hG hi hν hM hU) :
    InducedCuspidalSupportCategoryTarget.{u, u, max (u + 1) v}
      (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
      (h := hstd) (hU := hU) (hM := hM) (hL := hlev)
      (IsAssociate := rootAssociation i ν hN hZ) := by
  obtain ⟨C, cs, hLength, hF⟩ := hFilt
  have hSimple := positiveSimpleReflectionComparison_of_rootLength
    i ν hN hZ cs hi.isSplitSubtorus.1 hRoots hν hLength
  have hGeom := pointCuspidalExtractionGeometry_of_rootComparisons.{u, v}
    i ν hN hZ cs hLength hSimple hG hi hν hStandard hInter hM hU
  have hProper := pointProperTargetGeometricTermExclusion_of_standardInduction.{u, v}
    i ν cs hGeom.1 hInter hG hi hν hM hU hExclude
  have hDich := pointGeometricCuspidalGradeDichotomy_of_geometry_exclusion
    i ν hN hZ cs hInter hG hi hν hM hU hGeom hProper
  have hExact : ∀ J, Derivative.Mirabolic.MapsShortExactIntertwiners
      (jacquetFunctor.{u, max (u + 1) v} (hstd J) (hU J)) := by
    intro J A B C f g hf hg hfg
    have hex :=
      standardJacquetFunctor_map_isShortExact_of_standardCocharacterStatement
        i ν hStandard hG hi hν J (hU J) f g ⟨hf, hg, hfg⟩
    exact ⟨hex.1, hex.2.2, hex.2.1⟩
  intro K τ hcτ π hπ hπK
  -- A minimal cuspidal Jacquet quotient `ρ` of `π` on `M_I`, with `π ⊆ i_I(ρ)`.
  obtain ⟨I, ρ, hρ, hcρ, hρr, hπI⟩ :=
    exists_cuspidal_jacquet_quotient_embedding i ν hStandard hInter hRoots hG hi hν hU hM π hπ
  -- Exactness puts `ρ` in `r_I i_K(τ)`.
  have hρind := isSubquotient_jacquet_induction_of_exact.{_, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hstd hU hExact hπK hρr
  -- The geometric filtration of `r_I i_K(τ)` and its cuspidal graded pieces.
  obtain ⟨r, s, hgrades⟩ := hF K I τ
  have hpieces := pointCuspidalJacquetGradedPieces_of_geometricTerms
    i ν hN hZ cs hInter hG hi hν hM hU hDich K I τ hcτ s hgrades
  obtain ⟨n, hn, hassoc, hρn⟩ :=
    exists_conjugation_isSubquotient_of_gradedPieces.{_, u, max (u + 1) v} s hρ hcρ hρind hpieces
  -- Pull `ρ` back to an irreducible cuspidal subquotient of `τ`.
  have hUc : ∀ K' : Finset K, Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex K K')).subgroupOf (levi i ν K)) := fun K' =>
    isLimitOfCompactSubgroups_subgroupOf _ _ (hM K)
      (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν hStandard hG hi hν (leviIndex K K'))
  obtain ⟨hn', σ, hσ, hcσ, hπσ⟩ :=
    exists_inducedConjugate_of_conjugation_isSubquotient.{_, u, max (u + 1) v} hstd hU hUc hcτ hρ n hn hρn hπI
  refine ⟨I, (n⁻¹)⁻¹, hn', ?_, σ, hσ, hcσ, hπσ⟩
  rw [inv_inv]
  exact hassoc

end Rational

end RationalPointFamily

namespace RationalPointFamily

open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj
open GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

/-- The geometric-filtration and proper-standard exclusion inputs of the
extraction task prove the exact rational induced-cuspidal support target. -/
theorem rationalInducedCuspidalSupportCategory_of_extractionInputs
    (hInputs : RationalCuspidalExtractionInputsStatement.{u, v}) :
    RationalInducedCuspidalSupportCategoryStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  obtain ⟨hFilt, hExclude⟩ :=
    hInputs k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM
  exact inducedCuspidalSupportCategory_of_filtration_exclusion.{u, v}
    i ν hStandard hInter hRoots hG hi hν hU hM hN hZ hFilt hExclude

/-- Renard VI.3.5, the whole-category cuspidal splitting at the carrier universe
`max (u + 1) v`, proves the exact rational induced-cuspidal support target. -/
theorem rationalInducedCuspidalSupportCategory_of_wholeStatement
    (hwhole : CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u,
      max (u + 1) v}) :
    RationalInducedCuspidalSupportCategoryStatement.{u, v} :=
  rationalInducedCuspidalSupportCategory_of_extractionInputs.{u, v}
    (rationalCuspidalExtractionInputs_of_wholeStatement.{u, v} hwhole)

set_option linter.defProp false in
/-- The reduction of `RationalInducedCuspidalSupportCategoryStatement` to Renard
VI.3.5, as a declaration whose type is the implication. -/
def rationalInducedCuspidalSupportCategoryOfWholeStatement :
    CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
      RationalInducedCuspidalSupportCategoryStatement.{u, v} :=
  rationalInducedCuspidalSupportCategory_of_wholeStatement.{u, v}

end RationalPointFamily

end Langlands.Aubert.General
