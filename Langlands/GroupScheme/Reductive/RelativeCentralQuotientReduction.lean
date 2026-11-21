import Langlands.GroupScheme.Reductive.RelativeCentralQuotientStatement
import Langlands.GroupScheme.Reductive.RelativeCentralQuotientGeometryReduction
import Langlands.GroupScheme.Reductive.RelativeCentralQuotientCenter
import Langlands.GroupScheme.Torus.RelativeCentralQuotientPreimage
import Langlands.GroupScheme.SubgroupFunctor.FppfComap

/-! # Reduction of relative central quotients to multiplicative-type inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The three multiplicative-type inputs imply the full unchanged
relative central quotient proposition. -/
def RelativeCentralQuotientReductionStatement : Prop :=
  RelativeMultiplicativeTypeClosedSubgroupStatement.{u} →
  RelativeCentralMultiplicativeTypeQuotientStatement.{u} →
  MultiplicativeTypeNormalCentralStatement.{u} →
  RelativeCentralQuotientStatement.{u}

/-- The full relative central quotient theorem follows from the closed-subgroup,
affine central quotient, and normal-centrality theorems for multiplicative type.
All three remain explicit proposition hypotheses. -/
theorem relativeCentralQuotient_of_multiplicativeType_inputs
    (hsubgroup : RelativeMultiplicativeTypeClosedSubgroupStatement.{u})
    (hquotient : RelativeCentralMultiplicativeTypeQuotientStatement.{u})
    (hnormal : MultiplicativeTypeNormalCentralStatement.{u}) :
    RelativeCentralQuotientStatement.{u} := by
  intro S G hG Z z hz hc _ Q q hq
  dsimp only
  have hZ := centralKernel_isMultiplicativeType_of_closedSubgroups
    hsubgroup hG z hz hc hq
  have hQ := hq.isReductive_target_of_multiplicativeType_geometry
    hsubgroup hquotient hG z hz hc
  refine ⟨hQ,
    hq.center_comap_eq_of_multiplicativeTypeNormalCentral
      hnormal hG hQ z hz hc hZ q,
    ?_, ?_, ?_⟩
  · intro T t ht
    obtain ⟨T', t', p, hT', ht', hm', _, _, _, _, hpre⟩ :=
      exists_relativeMaximalTorus_image_of_centralMultiplicativeTypeQuotients
        hquotient hG hQ z hz hc hZ q hq T t ht.1 ht.2.1 ht.2.2
    exact ⟨T', t', ⟨hT', ht', hm'⟩, hpre⟩
  · intro T' t' ht'
    obtain ⟨T, t, hT, ht, hm, hpre⟩ :=
      exists_relativeMaximalTorus_preimage_of_centralMultiplicativeTypeQuotients
        hquotient hG hQ z hz hc hZ q hq T' t' ht'.1 ht'.2.1 ht'.2.2
    exact ⟨T, t, ⟨hT, ht, hm⟩, hpre⟩
  · intro T₁ T₂ t₁ t₂ h₁ h₂ heq
    let : Flat q.hom.hom.left := hq.1
    let : Surjective q.hom.hom.left := hq.2.1
    let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
    let : IsClosedImmersion t₁.hom.hom.left := h₁.2.1
    let : IsClosedImmersion t₂.hom.hom.left := h₂.2.1
    let : Mono t₁.hom.hom := Over.mono_of_mono_left _
    let : Mono t₂.hom.hom := Over.mono_of_mono_left _
    exact SubgroupFunctor.range_eq_of_comap_eq_of_fppf q t₁ t₂ heq

/-- The named reduction proposition is proved by the full conditional assembly. -/
theorem relativeCentralQuotientReduction : RelativeCentralQuotientReductionStatement.{u} :=
  relativeCentralQuotient_of_multiplicativeType_inputs

end Langlands.GroupScheme
