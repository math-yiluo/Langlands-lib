import Langlands.Geometry.Building.DepthZero.Statement

/-! # Proof of the depth-zero consumer for valid KP building data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

open BruhatTits.IntegralModels

set_option maxHeartbeats 1200000 in
/-- The depth-zero reduction and compact-induction results for each facet of a KP datum
satisfying the one-group axioms. -/
theorem depthZeroConsumer : DepthZeroConsumerStatement.{u} := by
  intro F _ _ _ _ G _ hG D hD
  dsimp only
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro x
  let M := D.models.facetModels.model x
  let Q := D.quotients.quotient x
  let P := D.parahoric x
  let N := D.parahoricRadical x
  let red := D.parahoricReduction x
  obtain ⟨hrad, hquot, hred⟩ := hD.reductiveQuotients.facets.reductive_quotients x
  have hCompact : IsCompact (P : Set (rationalPoints G)) :=
    M.neutral.isCompact_integralPoints_localField
  have hOpen : IsOpen (P : Set (rationalPoints G)) :=
    (D.parahoricOpenSubgroup x).isOpen
  have hker : red.ker = N := Q.ker_parahoricReduction hquot
  refine ⟨⟨hD.bruhatTitsGroupSchemes.neutral_points (BuildingModelIndex.ofFacet x),
    hCompact, hOpen⟩, ?_, ?_, ?_⟩
  · let : HenselianLocalRing 𝒪[F] := henselianLocalRing_integer
    have hNormal : N.Normal := Q.positivePoints_subgroupOf_normal hquot
    refine ⟨hNormal, ?_⟩
    let : N.Normal := hNormal
    have hRadicalCompact : IsCompact (N : Set P) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' Q.localField_isCompact_positivePoints
        (by
          rw [Subtype.range_coe]
          exact fun _ hg => Q.positivePoints_le_integralPoints hg)
    have hRadicalOpen : IsOpen (N : Set P) :=
      continuous_subtype_val.isOpen_preimage _ Q.localField_isOpen_positivePoints
    refine ⟨hRadicalCompact, hRadicalOpen, Q.parahoricReduction_surjective hrad hquot,
      hker, hred, Q.finite_quotientPoints_of_isConnectedReductive hred, ?_⟩
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (Q.depthZeroQuotientEquiv hrad hquot), fun _ => rfl⟩
  · intro V _ _ σ
    refine ⟨rfl, ?_, (D.depthZeroCompactInduction x σ).isSmooth⟩
    intro n
    apply LinearMap.ext
    intro v
    have hn : (n : P) ∈ red.ker := by
      rw [hker]
      exact n.property
    exact Q.inflation_ker_apply σ hn v
  · intro V W _ _ _ _ _ _ σ τ
    let σP := D.depthZeroInflation x σ
    let τP := D.depthZeroInflation x τ
    let A := D.depthZeroCompactInduction x σ
    let B := D.depthZeroCompactInduction x τ
    have hCongruence := M.localField_isOpen_congruenceSubgroup
    have hσ := Q.isSmooth_inflation hCongruence σ
    let e := Q.depthZeroInductionKernelEquiv hOpen hCongruence σ τ
    let kernel : (A ⟶ B) →ₗ[ℂ] (rationalPoints G → V →ₗ[ℂ] W) := {
      toFun T g :=
        Induction.evalLinearMap P τP g ∘ₗ
          (SmoothRep.hom T).toLinearMap ∘ₗ
            (Induction.unitMap P hOpen σP hσ).toLinearMap
      map_add' T S := by
        funext g
        apply LinearMap.ext
        intro v
        rfl
      map_smul' c T := by
        funext g
        apply LinearMap.ext
        intro v
        rfl }
    have kernel_eq (T : A ⟶ B) : kernel T = (e T).1 := by
      funext g
      apply LinearMap.ext
      intro v
      exact (Q.depthZeroInductionKernelEquiv_apply hOpen hCongruence σ τ T g v).symm
    have finiteSupport := Induction.compactInductionFiniteTypeKernel.{0, u, u, u} ℂ
      (rationalPoints G) P hOpen hCompact σP τP (Q.inflation_asModule_finite σ)
    refine ⟨kernel, ?_, ?_, fun T g v => rfl⟩
    · intro T S h
      apply e.injective
      apply Subtype.ext
      rwa [← kernel_eq T, ← kernel_eq S]
    · intro Φ
      refine Iff.trans ?_ (finiteSupport Φ)
      constructor
      · rintro ⟨T, rfl⟩
        rw [kernel_eq]
        exact (e T).2
      · intro hΦ
        refine ⟨e.symm ⟨Φ, hΦ⟩, ?_⟩
        rw [kernel_eq, e.apply_symm_apply]

end Langlands.Geometry.Building
