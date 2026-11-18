import Langlands.GroupScheme.IsomorphismSchemeNormalizedFamilyGeometry
import Langlands.GroupScheme.IsomorphismSchemePrecomposition
import Langlands.GroupScheme.IsomorphismSchemeTransport
import Langlands.GroupScheme.Reductive.AffinePinnedModel
import Langlands.GroupScheme.Reductive.PinnedComparisonLabelDescent
import Langlands.GroupScheme.Reductive.PinnedOuterIsomorphismChartConstruction
import Langlands.GroupScheme.Reductive.RelativePinnedComparisonProof
import Langlands.GroupScheme.Adjoint.ReductiveRelativeExistenceStatement
import Langlands.GroupScheme.Adjoint.RelativeExistenceProof

/-! # Pinned automorphism representatives from representation-free classification -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Representation-free constant-family classification on identity pullbacks
supplies the smooth separated full Aut representatives of all affine pinned
models. Both classification and relative adjoint existence remain hypotheses. -/
theorem affinePinnedAutomorphismRepresentatives_of_normalizedIdentityFamilies
    (hAdj : RelativeAdjointQuotientExistenceStatement.{u})
    (hfamily : ∀ (M : AffinePinnedModel.{u})
      (A : GroupScheme M.base) (q : M.groupOver (𝟙 M.base) ⟶ A)
      (hq : IsRelativeAdjointQuotient q),
      ∃ (D : Type u)
        (e : LocalGroupIso (M.groupOver (𝟙 M.base)) (M.groupOver (𝟙 M.base))
          (GroupIsomorphismScheme.constantParameter M.base D)),
        ∀ T : Over M.base, Function.Bijective
          (fun z : (T ⟶ A.X) ×
            (T ⟶ GroupIsomorphismScheme.constantParameter M.base D) =>
              (e.refine z.2).twist hq.innerAction z.1⁻¹)) :
    ∀ M : AffinePinnedModel.{u},
      ∃ I : GroupIsomorphismScheme M.group M.group,
        Smooth I.parameter.hom ∧ IsSeparated I.parameter.hom := by
  intro M
  obtain ⟨A, q, hq⟩ :=
    (ReductiveRelativeAdjointQuotientExistenceStatement.of_affine hAdj)
      M.base (M.groupOver (𝟙 M.base)) (M.reductive.baseChange (𝟙 M.base))
  obtain ⟨D, e, he⟩ := hfamily M A q hq
  let : Smooth A.X.hom := hq.isReductive_target.smooth
  let : IsAffineHom A.X.hom := hq.isReductive_target.isAffineHom
  let I := GroupIsomorphismScheme.ofNormalizedFamily hq.innerAction e he
  let J : GroupIsomorphismScheme M.group M.group :=
    (I.precompose (baseChangeIdIso M.group).symm).postcompose (baseChangeIdIso M.group)
  refine ⟨J, ?_, ?_⟩
  · change Smooth I.parameter.hom
    infer_instance
  · change IsSeparated I.parameter.hom
    infer_instance

/-- The actual constant pinned family supplies the classification premise in
the preceding reduction. Affine pinning classification, local normalization,
self-label completeness, and adjoint existence remain explicit inputs. -/
theorem affinePinnedAutomorphismRepresentatives_of_pinnedLabelCompleteness
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (hAdj : RelativeAdjointQuotientExistenceStatement.{u})
    (hlocal : AffinePinnedModel.HasFppfLocalPinnedRepresentatives.{u})
    (hcomplete : ∀ M : AffinePinnedModel.{u},
      AffinePinnedModel.OpenPinnedLabelCompleteness M M hAffine) :
    ∀ M : AffinePinnedModel.{u},
      ∃ I : GroupIsomorphismScheme M.group M.group,
        Smooth I.parameter.hom ∧ IsSeparated I.parameter.hom := by
  apply affinePinnedAutomorphismRepresentatives_of_normalizedIdentityFamilies hAdj
  intro M A q hq
  refine ⟨AffinePinnedModel.ComparisonLabel M M,
    AffinePinnedModel.constantPinnedFamily M M hAffine (𝟙 M.base) (𝟙 M.base), ?_⟩
  exact AffinePinnedModel.constantPinnedFamily_orbit_bijective M M hAffine
    (𝟙 M.base) (𝟙 M.base) (hcomplete M) hlocal hq

/-- The exact affine pinned theorem is the only remaining input after applying
the existing local-label completeness, normalization and quotient theorems. -/
theorem affinePinnedAutomorphismRepresentatives_of_pinnedClassification
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u}) :
    ∀ M : AffinePinnedModel.{u},
      ∃ I : GroupIsomorphismScheme M.group M.group,
        Smooth I.parameter.hom ∧ IsSeparated I.parameter.hom :=
  affinePinnedAutomorphismRepresentatives_of_pinnedLabelCompleteness hAffine
    relativeAdjointQuotientExistence
    AffinePinnedModel.hasFppfLocalPinnedRepresentatives
    (fun M => AffinePinnedModel.openPinnedLabelCompleteness hAffine M M)

/-- Select the full representative of a supplied affine pinned model and retain
its smoothness and separatedness, conditional only on exact affine pinning. -/
def affinePinnedAutomorphismSchemeOfPinnedClassification
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (M : AffinePinnedModel.{u}) :
    {I : GroupIsomorphismScheme M.group M.group //
      Smooth I.parameter.hom ∧ IsSeparated I.parameter.hom} :=
  ⟨(affinePinnedAutomorphismRepresentatives_of_pinnedClassification hAffine M).choose,
    (affinePinnedAutomorphismRepresentatives_of_pinnedClassification hAffine M).choose_spec⟩

end Langlands.GroupScheme
