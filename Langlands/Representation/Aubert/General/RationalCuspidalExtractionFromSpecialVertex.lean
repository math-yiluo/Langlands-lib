import Langlands.Representation.Aubert.General.RationalInducedJacquetGeometricFiltration
import Langlands.Representation.Aubert.General.RationalLeviCuspidalEmbedding
import Langlands.Representation.Aubert.General.RationalLeviCuspidalRemainderTransport
import Langlands.Representation.Aubert.General.StandardFamilyStructure
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.Representation.Plancherel.RationalTwistStabilizer
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.Representation.Aubert.General.RationalCompactRestrictionCuspidalProof
import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionProof
import Langlands.Representation.CuspidalSupport.RationalCuspidalInertiaDecompositionReduction
import Langlands.Representation.CuspidalSupport.OpenNormalFamilyProjector
import Langlands.Representation.CompactCoefficient.NormalRestriction
import Langlands.Representation.CompactCoefficient.NormalSubgroupDecomposition
import Langlands.Representation.CompactCoefficient.AllProjectiveLifting
import Langlands.Representation.Plancherel.RationalNormKernelTopology

/-! # Proper-induction exclusion and extraction from one special vertex -/

noncomputable section

set_option maxHeartbeats 800000

open CategoryTheory

namespace Langlands.Aubert.General

universe uK uG uV

section Adjointness

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] {κ : Type uK}
  (P M U : κ → Subgroup G)
  (h : ∀ k, IsSemidirectDecomposition (P k) (M k) (U k))
  (hU : ∀ k, IsClosed (U k : Set G))

/-- First adjointness: every intertwiner from an object cuspidal for the
family into a normalized induction along a member of the family vanishes,
when the unipotent subgroup of that member is unimodular. -/
theorem hom_eq_zero_of_isCuspidalFor_of_induction
    (k : κ) (hδ : IsUnimodularModulus (U k) (hU k))
    (σ : SmoothRep.{0, uG, uV} ℂ (M k))
    (C : SmoothRep.{0, uG, max uG uV} ℂ G) (hC : IsCuspidalFor P M U h hU C)
    (f : C ⟶ (normalizedInductionFunctor (h k) (hU k)).obj σ) : f = 0 := by
  let := hC k
  have hz : FirstAdjointness.equiv (h k) (hU k) hδ C σ (SmoothRep.hom f) = 0 := by
    ext q
    rw [Subsingleton.elim q 0, map_zero, map_zero]
  have hf : SmoothRep.hom f = 0 := by
    apply (FirstAdjointness.equiv (h k) (hU k) hδ C σ).injective
    simpa using hz
  ext v
  exact congrArg (fun F => F v) hf

end Adjointness

section CompactRestriction

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G] [TotallyDisconnectedSpace G]
  (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G))

include hN in
/-- A nonzero subquotient with compact coefficients on an open normal subgroup
forces nonzero compact-restriction vectors in the ambient object: the compact
restriction is projective, so it lifts into the ambient restriction. -/
theorem compactRestrictionSubrepresentation_ne_bot_of_isSubquotient
    {τ V : SmoothRep.{0, uG, uV} ℂ G} [Nontrivial τ]
    (hτ : HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup N τ).representation)
    (hsub : SmoothRep.IsSubquotient τ V) :
    compactRestrictionSubrepresentation N V ≠ ⊥ := by
  let : LocallyCompactSpace N := hN.locallyCompactSpace
  obtain ⟨C, ι, q, hι, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hsub
  let qN : SmoothRep.restrictSubgroup N C ⟶ SmoothRep.restrictSubgroup N τ :=
    SmoothRep.ofHom (SmoothRep.restrictSubgroupMap N (SmoothRep.hom q))
  have : Epi qN := (SmoothRep.epi_iff_surjective qN).mpr hq
  let s := CompactCoefficient.allProjectiveLift (SmoothRep.restrictSubgroup N τ) hτ (𝟙 _) qN
  have hs : s ≫ qN = 𝟙 _ := CompactCoefficient.allProjectiveLift_comp _ hτ _ qN
  let f : (SmoothRep.restrictSubgroup N τ).representation.IntertwiningMap
      (SmoothRep.restrictSubgroup N V).representation :=
    (SmoothRep.restrictSubgroupMap N (SmoothRep.hom ι)).comp (SmoothRep.hom s)
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : τ)
  let w : SmoothRep.restrictSubgroup N τ := w₀
  have hw : w ≠ 0 := hw₀
  intro hbot
  have hmem : f w ∈ compactRestrictionSubrepresentation N V :=
    range_le_compactCoefficientVectors f hτ ⟨w, rfl⟩
  rw [hbot] at hmem
  have hsw : SmoothRep.hom s w = 0 := by
    apply hι
    exact hmem.trans (map_zero (SmoothRep.hom ι)).symm
  have hqs : SmoothRep.hom qN (SmoothRep.hom s w) = w := by
    have h := congrArg (fun F => SmoothRep.hom F w) hs
    simpa using h
  apply hw
  rw [← hqs, hsw, map_zero]

omit [T2Space G] [TotallyDisconnectedSpace G] in
include hN in
/-- The compact-restriction subrepresentation has compact coefficients on the
open subgroup, by extension of smooth functionals. -/
theorem compactRestrictionProperty_compactRestrictionSubrepresentation
    (V : SmoothRep.{0, uG, uV} ℂ G) :
    HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup N
      (SmoothRep.subrepresentation V (compactRestrictionSubrepresentation N V))).representation := by
  change HasCompactSmoothDualCoefficients
    (SmoothRep.restrictSubrepresentation N (compactRestrictionSubrepresentation N V)).toRepresentation
  exact hasCompactSmoothDualCoefficients_subrepresentation_of_le
    (CuspidalSupport.openSubgroup_compactOpenCofinal N hN) (SmoothRep.restrictSubgroup N V)
    (SmoothRep.restrictSubrepresentation N (compactRestrictionSubrepresentation N V)) le_rfl

include hN in
/-- If compact restriction to an open normal subgroup implies a property
`Cusp`, every map from a `Cusp` object to `V` vanishes, and `τ` is nonzero with
compact restriction, then `τ` is not a subquotient of `V`. -/
theorem not_isSubquotient_of_compactRestriction
    (Cusp : SmoothRep.{0, uG, uV} ℂ G → Prop)
    (hconv : ∀ A : SmoothRep.{0, uG, uV} ℂ G,
      HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup N A).representation → Cusp A)
    {τ V : SmoothRep.{0, uG, uV} ℂ G} [Nontrivial τ]
    (hτ : HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup N τ).representation)
    (hHom : ∀ C, Cusp C → ∀ f : C ⟶ V, f = 0) :
    ¬ SmoothRep.IsSubquotient τ V := by
  intro hsub
  apply compactRestrictionSubrepresentation_ne_bot_of_isSubquotient N hN hτ hsub
  have hf := hHom _ (hconv _ (compactRestrictionProperty_compactRestrictionSubrepresentation N hN V))
    (SmoothRep.subtype V (compactRestrictionSubrepresentation N V))
  rw [eq_bot_iff]
  intro v hv
  let v' : SmoothRep.subrepresentation V (compactRestrictionSubrepresentation N V) := ⟨v, hv⟩
  have h0 := congrArg (fun F => SmoothRep.hom F v') hf
  exact h0

end CompactRestriction

namespace RationalPointFamily

universe u v

open _root_.AlgebraicGeometry GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

section Exclusion

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance rationalSpecialVertexExclusionPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hStandard : StandardCocharacterStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))

include hStandard in
/-- Renard VI.5.2 inside every actual standard Levi, from one special vertex
of each standard Levi scheme: a nonzero inside-Levi cuspidal representation is
never a subquotient of a proper normalized standard induction. -/
theorem pointLeviStandardInductionCuspidalExclusion_of_specialVertexInputs
    (hSV : CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{u}) :
    PointLeviStandardInductionCuspidalExclusion.{u, v} i ν hInter hG hi hν hM hU := by
  intro J K hK
  let := (hM J).locallyCompactSpace
  intro ρ τ hτ hcτ hsub
  have : τ.representation.IsIrreducible := hτ
  have : Nontrivial τ := by
    have : Nontrivial τ.representation.asModule :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (levi i ν J)) _
    obtain ⟨w₀, hw₀⟩ := exists_ne (0 : τ.representation.asModule)
    exact nontrivial_of_ne (w₀ : τ) 0 hw₀
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let L := Standard.leviScheme i ν (rootSet i ν J)
  have hL : IsConnectedReductive L :=
    standardLeviScheme_isConnectedReductive i ν hStandard dynamicCentralizerReductive
      hG hi hν J
  have := hL.isAffineHom
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  have := hL.smooth
  let : T2Space k := BruhatTits.localField_t2Space k
  let : TopologicalSpace (rationalPoints L) := pointTopology
  let : LocallyCompactSpace (rationalPoints L) := rationalPoint_locallyCompactSpace k L
  let : NonarchimedeanGroup (rationalPoints L) :=
    Plancherel.rationalPoints_nonarchimedeanGroup L
  let : T2Space (rationalPoints L) := rationalPoint_t2Space k L
  let : TotallyDisconnectedSpace k := BruhatTits.localField_totallyDisconnectedSpace k
  let : TotallyDisconnectedSpace (rationalPoints L) :=
    BruhatTits.rationalPoint_totallyDisconnectedSpace k L
  let iL := standardLeviTorusFactor i ν (rootSet i ν J)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν J))
  have hiL : IsMaximalSplitTorus iL :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν (rootSet i ν J)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν J))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν J))
  have := hiL.isSplitSubtorus.mono
  have hνL : IsGenericCocharacter iL ν :=
    (standardLeviStandardFamilies dynamicLie hStandard k G hG T i hi ν hν
      (rootSet i ν J) (rootSet_subset i ν J) L hL
      (Standard.leviHom i ν (rootSet i ν J))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν J))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν J))).2.1
  have hRootsL : HasRelativeRootSystem iL :=
    Langlands.GroupScheme.relativeRootSystem k L hL T iL hiL
  let := simpleRelativeRootFintype iL hRootsL hiL.isSplitSubtorus.1 ν
  let hUL := isClosed_unipotent_of_isNonarchimedeanLocalField iL ν
  let hOwn := isSemidirectDecomposition_of_standardCocharacterStatement
    iL ν hStandard hL hiL hνL
  let hInner := isSemidirectDecomposition_in_levi i ν hInter hG hi hν J
  let e := leviRationalPointHomeomorph i ν J
  have hcusp (B : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)) :
      IsCuspidal (parabolic iL ν) (levi iL ν) (unipotent iL ν) hOwn hUL
          ((SmoothRep.pullbackFunctor e).obj B) ↔
        IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU J (hM J) hInner B :=
    rationalLeviCuspidalityTransport dynamicLie hStandard k G hG T i hi ν hν J hL
      hU hUL (hM J) hInner hOwn B
  let hUK : IsClosed (((unipotent i ν (leviIndex J K)).subgroupOf (levi i ν J) :
      Subgroup (levi i ν J)) : Set (levi i ν J)) :=
    (hU (leviIndex J K)).preimage continuous_subtype_val
  let V := (normalizedInductionFunctor.{u, max (u + 1) v} (hInner K) hUK).obj ρ
  have hδ := isUnimodularModulus_standardUnipotent_in_levi i ν hG hi hν hStandard hU hM J K
  have hHom (C : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J))
      (hC : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU J (hM J) hInner C)
      (f : C ⟶ V) : f = 0 :=
    hom_eq_zero_of_isCuspidalFor_of_induction
      (fun I : {I : Finset J // I ≠ Finset.univ} =>
        (parabolic i ν (leviIndex J I)).subgroupOf (levi i ν J))
      (fun I => (levi i ν (leviIndex J I)).subgroupOf (levi i ν J))
      (fun I => (unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J))
      (fun I => hInner I) (fun I => (hU (leviIndex J I)).preimage continuous_subtype_val)
      ⟨K, hK⟩ hδ ρ C hC f
  have hHom' (C' : SmoothRep.{0, u, max (u + 1) v} ℂ (rationalPoints L))
      (hC' : IsCuspidal (parabolic iL ν) (levi iL ν) (unipotent iL ν) hOwn hUL C')
      (f' : C' ⟶ (SmoothRep.pullbackFunctor e).obj V) : f' = 0 := by
    have hC : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU J (hM J) hInner
        ((SmoothRep.pullbackFunctor e.symm).obj C') :=
      (hcusp _).mp (hC'.of_iso ((SmoothRep.pullbackEquivalence e).counitIso.app C'))
    have h0 := hHom _ hC ((SmoothRep.pullbackFunctor e.symm).map f' ≫
      ((SmoothRep.pullbackEquivalence e).unitIso.app V).inv)
    ext w
    let w' : (SmoothRep.pullbackFunctor e.symm).obj C' := w
    have h1 := congrArg (fun F => SmoothRep.hom F w') h0
    exact h1
  obtain ⟨D, x, hx, hprops, hbasis, hcover⟩ := hSV k L hL T iL hiL ν hνL
  have hτc := rationalCuspidalCompactRestriction k L hL T iL hiL ν hνL hStandard hRootsL hUL
    D x hx hprops hbasis hcover _ ((hcusp τ).mpr hcτ)
  have : Nontrivial ((SmoothRep.pullbackFunctor e).obj τ) := inferInstanceAs (Nontrivial τ)
  exact not_isSubquotient_of_compactRestriction (Plancherel.rationalCommonNormKernel L)
    (Plancherel.isOpen_rationalCommonNormKernel L)
    (IsCuspidal (parabolic iL ν) (levi iL ν) (unipotent iL ν) hOwn hUL)
    (fun A hA => rationalCompactRestrictionCuspidal k L hL T iL hiL ν hνL hStandard hRootsL
      hUL A hA) hτc hHom' (hsub.pullback e)

end Exclusion

/-- One special vertex for every connected reductive group proves both inputs
of the actual extraction route: the geometric filtration is unconditional and
the proper-standard exclusion follows from the special-vertex inputs applied to
each standard Levi scheme. -/
theorem rationalCuspidalExtractionInputs_of_specialVertexInputs
    (hSV : CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{u}) :
    RationalCuspidalExtractionInputsStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  exact ⟨exists_pointInducedJacquetGeometricFiltration.{u, v}
      i ν hN hZ hStandard hInter hRoots hG hi hν hM hU,
    pointLeviStandardInductionCuspidalExclusion_of_specialVertexInputs.{u, v}
      i ν hStandard hInter hG hi hν hM hU hSV⟩

/-- The exact rational extraction target follows from the special-vertex
inputs. -/
theorem rationalCuspidalJacquetFactorExtraction_of_specialVertexInputs
    (hSV : CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{u}) :
    RationalCuspidalJacquetFactorExtractionStatement.{u, v} :=
  rationalCuspidalJacquetFactorExtraction_of_inputs
    (rationalCuspidalExtractionInputs_of_specialVertexInputs hSV)

/-- The exact rational extraction target follows from the joint
special-compact basis existence statement. -/
theorem rationalCuspidalJacquetFactorExtraction_of_jointBasis
    (hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u}) :
    RationalCuspidalJacquetFactorExtractionStatement.{u, v} :=
  rationalCuspidalJacquetFactorExtraction_of_specialVertexInputs
    (CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis hJoint)

set_option linter.defProp false in
/-- The reduction of the exact rational extraction target to the special-vertex
inputs, as a declaration whose type is the implication. -/
def rationalCuspidalJacquetFactorExtractionOfSpecialVertexInputs :
    CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{u} →
      RationalCuspidalJacquetFactorExtractionStatement.{u, v} :=
  rationalCuspidalJacquetFactorExtraction_of_specialVertexInputs

end RationalPointFamily

end Langlands.Aubert.General
