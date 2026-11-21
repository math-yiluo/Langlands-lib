import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourceFormalDegree

/-! # Formal degree transport to the actual semistandard Levi model -/

noncomputable section

universe u uV uG uH

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General
open Langlands.Plancherel.DynamicOppositeStandardIntertwining
open Langlands.Plancherel.DynamicOppositeCanonicalScalar

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.SourceDegree

private theorem representationFormalDegree_pullback
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (e : H ≃ₜ* G) (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
    (B : Subgroup H) [B.Normal] (hB : B ≤ Subgroup.center H)
    (hAB : B.map e.toMulEquiv.toMonoidHom = A)
    [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
    [MeasurableSpace (H ⧸ B)] [BorelSpace (H ⧸ B)]
    (μG : Measure (G ⧸ A)) [μG.IsHaarMeasure] [μG.IsInvInvariant]
    (μH : Measure (H ⧸ B)) [μH.IsHaarMeasure] [μH.IsInvInvariant]
    (hμ : μH.map (quotientContinuousMulEquiv e A B hAB) = μG)
    (hcofG : CompactOpenCofinal G) (hcofH : CompactOpenCofinal H)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (hρ : IsSquareIntegrableModCentralSubgroup A hA ρ μG) (hiρ : ρ.IsIrreducible)
    (hσ : IsSquareIntegrableModCentralSubgroup B hB (ρ.comp e.toMonoidHom) μH)
    (hiσ : Representation.IsIrreducible (ρ.comp e.toMonoidHom)) :
    representationFormalDegree A hA μG hcofG hρ hiρ =
      representationFormalDegree B hB μH hcofH hσ hiσ := by
  let cG := Classical.choose hρ.2
  let cH := Classical.choose hσ.2
  let hG : ∀ (a : A) (v : V), ρ a v =
      ((cG.character.comp (Subgroup.inclusion hA)) a : ℂ) • v :=
    fun a v => cG.acts (Subgroup.inclusion hA a) v
  let hH : ∀ (b : B) (v : V), (ρ.comp e.toMonoidHom) b v =
      ((cH.character.comp (Subgroup.inclusion hB)) b : ℂ) • v :=
    fun b v => cH.acts (Subgroup.inclusion hB b) v
  refine formalDegree_unique A hA μG hG hcofG hρ hiρ
    (orthogonalityIntegral_eq_representationFormalDegree A hA μG hcofG hG hρ hiρ) ?_
  intro v₁ ℓ₁ v₂ ℓ₂
  let ℓ₁H : SmoothDual (ρ.comp e.toMonoidHom) :=
    ⟨ℓ₁.val, (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ₁.val).mpr ℓ₁.property⟩
  let ℓ₂H : SmoothDual (ρ.comp e.toMonoidHom) :=
    ⟨ℓ₂.val, (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ₂.val).mpr ℓ₂.property⟩
  have hIntegrand :
      orthogonalityIntegrand B hH hH v₁ ℓ₁H.val v₂ ℓ₂H.val =
        orthogonalityIntegrand A hG hG v₁ ℓ₁.val v₂ ℓ₂.val ∘
          quotientContinuousMulEquiv e A B hAB := by
    funext q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Function.comp_apply, quotientContinuousMulEquiv_mk,
      orthogonalityIntegrand_mk, orthogonalityIntegrand_mk]
    change ℓ₁.val (ρ (e h) v₁) * ℓ₂.val (ρ (e h⁻¹) v₂) =
      ℓ₁.val (ρ (e h) v₁) * ℓ₂.val (ρ ((e h)⁻¹) v₂)
    rw [map_inv e]
  calc
    _ = orthogonalityIntegral B μH hH hH v₁ ℓ₁H v₂ ℓ₂H := by
      unfold orthogonalityIntegral
      rw [hIntegrand, ← hμ]
      exact integral_map_equiv
        (quotientContinuousMulEquiv e A B hAB).toHomeomorph.toMeasurableEquiv _
    _ = _ :=
      orthogonalityIntegral_eq_representationFormalDegree B hB μH hcofH hH hσ hiσ
        v₁ ℓ₁H v₂ ℓ₂H

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
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean

attribute [local instance]
  SourceMeasure.modelAffineHom SourceMeasure.modelAffine SourceMeasure.modelSmooth
  SourceMeasure.modelFiniteType SourceMeasure.modelTopology SourceMeasure.modelNonarchimedean
  SourceMeasure.intrinsicQuotientMeasurable SourceMeasure.intrinsicQuotientBorel

set_option maxHeartbeats 600000 in
set_option maxRecDepth 4096 in
/-- Schur degrees agree under the actual model identification with the prescribed quotient Haar. -/
theorem formalDegreeTransport
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
    {p : SemistandardSpectralIndex i} (model : LeviModel p) (d : CompactData p)
    {A : CommGroupScheme (Spec (CommRingCat.of F))}
    (a : A.toGrp ⟶ model.scheme) (ha : IsSplitComponent a)
    [(model.splitCenter a).Normal] [(rationalPoints.map a).range.Normal]
    [MeasurableSpace (levi p ⧸ model.splitCenter a)] [BorelSpace (levi p ⧸ model.splitCenter a)]
    (mu : Measure (levi p ⧸ model.splitCenter a)) [mu.IsHaarMeasure] [mu.IsInvInvariant] :
    FormalDegreeTransportStatement.{u, uV} model d a ha mu := by
  intro ω
  rcases ω with ⟨ω, hω⟩
  induction ω using Quotient.inductionOn with
  | h π =>
    let C := model.splitCenter a
    let hC := model.splitCenter_le_center a ha
    let CL := (rationalPoints.map a).range
    let hCL := ha.isCentralSplitTorus.isCentral.range_le_center
    let muL := SourceMeasure.intrinsicQuotientHaar model a mu
    let πL := IrreducibleAdmissibleRep.pullback model.pointHomeomorph π
    let hmap := SourceMeasure.map_intrinsicQuotientHaar model a mu
    have hπ : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu := hω
    have hπL : IsSquareIntegrableModCentralSubgroup CL hCL πL.obj.representation muL :=
      (isSquareIntegrableModCentralSubgroup_comp_iff model.pointHomeomorph C hC CL hCL
        rfl mu muL hmap π.obj.representation).mpr hπ
    change discreteSeriesFormalDegree C hC mu (compactOpenCofinal_levi model d)
        (discreteSeriesClass C hC mu π hπ) =
      discreteSeriesFormalDegree CL hCL muL (intrinsicCompactOpenCofinal model d)
        (discreteSeriesClass CL hCL muL πL hπL)
    calc
      _ = representationFormalDegree C hC mu (compactOpenCofinal_levi model d)
            hπ π.property.1 :=
        discreteSeriesFormalDegree_mk C hC mu (compactOpenCofinal_levi model d) π hπ
      _ = representationFormalDegree CL hCL muL (intrinsicCompactOpenCofinal model d)
            hπL πL.property.1 :=
        representationFormalDegree_pullback model.pointHomeomorph C hC CL hCL rfl
          mu muL hmap (compactOpenCofinal_levi model d) (intrinsicCompactOpenCofinal model d)
          hπ π.property.1 hπL πL.property.1
      _ = _ :=
        (discreteSeriesFormalDegree_mk CL hCL muL (intrinsicCompactOpenCofinal model d) πL hπL).symm

end Langlands.HarishChandraSchwartz.RationalSemistandard.SourceDegree
