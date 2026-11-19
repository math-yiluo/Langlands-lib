import Langlands.Representation.Plancherel.DynamicCommonLeviPresentations
import Langlands.Representation.Plancherel.DynamicCommonLeviStructuralComparison
import Langlands.Representation.Plancherel.DynamicCommonLeviCompact
import Langlands.Representation.Plancherel.ParabolicGenericIrreducibilityProof
import Langlands.Representation.Plancherel.SquareIntegrableCentralPullback
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralSubgroupSquareIntegrabilityTransfer

/-! # Open irreducibility for the actual dynamic common-Levi inductions -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviIrreducibility

open Aubert.General Induction StandardIntertwining
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open DynamicCommonLeviComposition DynamicCommonLeviPresentationComparison
open DynamicCommonLeviPresentations DynamicCommonLeviStructuralComparison DynamicCommonLeviCompact

universe u uV

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

/-- There is a nonempty open set of the actual common-Levi parameters
where the indicated dynamic parabolic induction is irreducible. -/
def HasOpenIrreducibilityLocus : Prop :=
  ∃ D : Set (unramifiedCharacters (normCharacters χ)), IsOpen D ∧ D.Nonempty ∧
    ∀ z ∈ D, (UnramifiedLeviInduction (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
      (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible

set_option maxHeartbeats 800000 in
private theorem hasOpenIrreducibilityLocus_of_presentation
    (hG : IsConnectedReductive G) (hA : A.IsIrreducible)
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {a : T.toGrp ⟶ parameterScheme χ} (d : ParabolicData χ ψ T a)
    (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
    [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
    (mu : Measure (levi χ ⧸ C)) [mu.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation mu) :
    HasOpenIrreducibilityLocus χ ψ hψ A := by
  let Ppt := (SubgroupFunctor.range d.p).carrier (Over.mk (𝟙 _))
  let Mpt := parabolicLeviPointSubgroup d.p d.l
  let Upt := (SubgroupFunctor.range (d.n ≫ d.p)).carrier (Over.mk (𝟙 _))
  have eP : Ppt = parabolic ψ := parabolicPoints_eq χ ψ d.realizes
  have eM : Mpt = levi χ := leviPoints_eq χ ψ d.realizes
  have eU : Upt = radical ψ := radicalPoints_eq χ ψ d.realizes
  let e := leviPointComparison χ ψ d.realizes
  have h : IsSemidirectDecomposition Ppt Mpt Upt := by
    rw [eP, eM, eU]
    exact commonDecomposition χ ψ hψ
  have hP : IsClosed (Ppt : Set (rationalPoints G)) := by
    rw [eP]
    exact parabolic_isClosed ψ
  have hM : IsClosed (Mpt : Set (rationalPoints G)) := by
    rw [eM]
    exact levi_isClosed χ
  have hU : IsClosed (Upt : Set (rationalPoints G)) := by
    rw [eU]
    exact radical_isClosed ψ
  have hr : Continuous h.projection := by
    let p := subgroupHomeomorphOfEq eP
    have he : (h.projection : Ppt → Mpt) =
        e.symm ∘ (commonDecomposition χ ψ hψ).projection ∘ p := by
      funext x
      apply e.injective
      change e (h.projection x) = e (e.symm ((commonDecomposition χ ψ hψ).projection (p x)))
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact projectionComparisonOfEq eP eM eU h (commonDecomposition χ ψ hψ) x
    rw [he]
    exact e.symm.continuous.comp ((commonProjection_continuous χ ψ hψ).comp p.continuous)
  let B := presentationRepresentation χ ψ d.realizes A
  have hB : B.IsIrreducible := (isIrreducible_comp_continuousMulEquiv_iff A.representation e).mpr hA
  let C₀ := C.comap e.toMonoidHom
  let : MeasurableSpace (Mpt ⧸ C₀) := borel _
  let : BorelSpace (Mpt ⧸ C₀) := ⟨rfl⟩
  have hC₀ : C₀ ≤ Subgroup.center Mpt := centralSubgroup_comap_le_center e C hC
  let mu₀ := centralSubgroupPullbackMeasure e C mu
  have hsq₀ : IsSquareIntegrableModCentralSubgroup C₀ hC₀ B.representation mu₀ :=
    isSquareIntegrableModCentralSubgroup_pullback e C mu hC A.representation hsq
  let S := (parabolicSplitComponentPointHom d.r).range
  let hS := parabolicSplitComponentPointHom_range_le_center d.r
  let : S.Normal := S.normal_of_le_center hS
  let : MeasurableSpace (Mpt ⧸ S) := borel _
  let : BorelSpace (Mpt ⧸ S) := ⟨rfl⟩
  let : MeasurableSpace (Mpt ⧸ Subgroup.center Mpt) := borel _
  let : BorelSpace (Mpt ⧸ Subgroup.center Mpt) := ⟨rfl⟩
  let : LocallyCompactSpace Mpt := hM.locallyCompactSpace
  let : SecondCountableTopology Mpt := TopologicalSpace.Subtype.secondCountableTopology _
  let : CompactSpace (Subgroup.center Mpt ⧸ S.subgroupOf (Subgroup.center Mpt)) :=
    compactSpace_parabolicCenter_quotient d.r
  let muS : Measure (Mpt ⧸ S) := Measure.haar
  have hsqS : IsSquareIntegrableModCentralSubgroup S hS B.representation muS :=
    isSquareIntegrableModCentralSubgroup_transfer C₀ hC₀ (compactCofinal hM)
      B.representation hB mu₀ hsq₀ S hS (isClosed_parabolicSplitComponentPointHom_range d.r) muS
  obtain ⟨D, hD, hnD, hDirr⟩ := exists_open_irreducible_unconditional d.r d.radical h hU
    hG hP hr B hB muS hsqS
  let Φ := characterComparison χ ψ d.r d.realizes
  refine ⟨Φ ⁻¹' D, hD.preimage Φ.continuous, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hnD
    refine ⟨Φ.symm z, ?_⟩
    change Φ (Φ.symm z) ∈ D
    rw [Φ.apply_symm_apply]
    exact hz
  · intro z hz
    exact SmoothRep.isIrreducible_of_equiv
      (unramifiedInductionComparison χ ψ hψ d.r d.realizes h hU A z) (hDirr (Φ z) hz)

/-- Generic irreducibility applies at each vertex using the same original
coefficient representation and its square integrability modulo a central subgroup. -/
theorem hasOpenIrreducibilityLocus
    (hG : IsConnectedReductive G) (hA : A.IsIrreducible)
    (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
    [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
    (mu : Measure (levi χ ⧸ C)) [mu.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation mu) :
    HasOpenIrreducibilityLocus χ ψ hψ A := by
  obtain ⟨T, a, ha⟩ := (splitComponentStatement F (parameterScheme χ)
    (parameterScheme_isConnectedReductive χ hG)).1
  let d := parabolicData χ ψ hG hψ T a ha
  exact hasOpenIrreducibilityLocus_of_presentation χ ψ hψ A hG hA d C hC mu hsq

end Langlands.Plancherel.DynamicCommonLeviIrreducibility
