import Langlands.GroupScheme.Reductive.RelativeDerivedDescent
import Langlands.GroupScheme.Reductive.RelativeDerivedKernel
import Langlands.GroupScheme.Reductive.AffinePinnedAtlas

/-! # Reducing relative derived-group existence to split affine models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace RelativeDerived

/-- Admissibility transports through an isomorphism of the ambient group. -/
theorem IsAdmissible.comp_iso {S : Scheme.{u}} {D G G' : GroupScheme S}
    {d : D ⟶ G} (hd : IsAdmissible d) (e : G ≅ G') :
    IsAdmissible (d ≫ e.hom) := by
  refine ⟨hd.1.comp_iso e, ?_, hd.2.2.1, hd.2.2.2.1, ?_⟩
  · rw [SubgroupFunctor.range_comp_iso]
    exact hd.2.1.comap e.inv
  · obtain ⟨Q, q, hQ, hq⟩ := hd.2.2.2.2
    refine ⟨Q, e.inv ≫ q, hQ, ?_⟩
    apply RelativeRoot.IsFppfQuotient.of_iso_square d (d ≫ e.hom) q
      e.symm (Iso.refl D) _ hq
    simp

end RelativeDerived

/-- The existence input on supplied split pinned affine reductive models. -/
def RelativeDerivedSplitExistenceStatement : Prop :=
  ∀ M : AffinePinnedModel.{u},
    ∃ (D : GroupScheme M.base) (d : D ⟶ M.group), RelativeDerived.IsAdmissible d

/-- The equivalent split input formulated as a smooth torus quotient with
semisimple full geometric kernels. -/
def RelativeDerivedSplitTorusQuotientExistenceStatement : Prop :=
  ∀ M : AffinePinnedModel.{u},
    ∃ (Q : GroupScheme M.base) (q : M.group ⟶ Q),
      RelativeDerived.IsSemisimpleTorusQuotient q

/-- The full kernel construction identifies the two split existence inputs. -/
theorem relativeDerivedSplitExistence_iff_torusQuotient :
    RelativeDerivedSplitExistenceStatement.{u} ↔
      RelativeDerivedSplitTorusQuotientExistenceStatement.{u} := by
  constructor
  · intro hsplit M
    obtain ⟨D, d, hd⟩ := hsplit M
    obtain ⟨Q, q, hQ, hq⟩ := hd.2.2.2.2
    exact ⟨Q, q, hd.isSemisimpleTorusQuotient M.reductive hQ hq⟩
  · intro hsplit M
    obtain ⟨Q, q, hq⟩ := hsplit M
    exact ⟨kernel q, kernelι q, RelativeDerived.isAdmissible_kernelι M.reductive hq⟩

/-- Published affine pinned charts and admissible subgroup descent reduce the
arbitrary-base existence problem to the supplied split affine models. -/
theorem relativeDerivedGroupExistence_of_split
    (hperf : RelativeSemisimpleFppfPerfectStatement.{u})
    (hsplit : RelativeDerivedSplitExistenceStatement.{u}) :
    RelativeDerivedGroupExistenceStatement.{u} := by
  intro S G hG
  let A := AffinePinnedAtlas.ofReductive hG
  apply relativeDerivedAdmissibleEtaleDescent hperf S G hG A.cover
  intro s
  obtain ⟨D, d, hd⟩ := hsplit (A.chart s).model
  exact ⟨D, d ≫ (A.chart s).iso.inv, hd.comp_iso (A.chart s).iso.symm⟩

/-- Under the explicit perfectness input, split affine existence is equivalent
to the original existence proposition. -/
theorem relativeDerivedGroupExistence_iff_split
    (hperf : RelativeSemisimpleFppfPerfectStatement.{u}) :
    RelativeDerivedGroupExistenceStatement.{u} ↔
      RelativeDerivedSplitExistenceStatement.{u} := by
  constructor
  · intro hexists M
    exact hexists M.base M.group M.reductive
  · exact relativeDerivedGroupExistence_of_split hperf

/-- A split smooth torus quotient construction suffices for global existence,
retaining only the separate relative semisimple perfectness input. -/
theorem relativeDerivedGroupExistence_of_splitTorusQuotient
    (hperf : RelativeSemisimpleFppfPerfectStatement.{u})
    (hsplit : RelativeDerivedSplitTorusQuotientExistenceStatement.{u}) :
    RelativeDerivedGroupExistenceStatement.{u} :=
  relativeDerivedGroupExistence_of_split hperf
    (relativeDerivedSplitExistence_iff_torusQuotient.mpr hsplit)

end Langlands.GroupScheme
