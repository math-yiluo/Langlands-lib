import Langlands.GroupScheme.PinnedQuotientProjection
import Langlands.GroupScheme.AutomorphicActionBasePointHom
import Langlands.GroupScheme.Reductive.AffinePinnedAutomorphismRepresentatives
import Langlands.GroupScheme.Reductive.AffinePinnedAutomorphismGroupStatement

/-! # Assembling the affine pinned automorphism-group conclusion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace AffinePinnedModel

variable (M : AffinePinnedModel.{u}) {Gad : GroupScheme M.base}
  (c : AutomorphicAction Gad M.group)

/-- The two geometric inputs still needed after pinned full faithfulness.
Factorization uses an actual adjoint base section, through its automorphism. -/
structure AutomorphismSplittingGeometry : Prop where
  factor : ∀ σ : CategoryTheory.Aut M.group,
    ∃ θ ∈ M.basedAutomorphisms, ∃ τ, M.IsPinnedAutomorphism τ θ ∧
      ∃ n ∈ c.basePointHom.range, σ = n * τ
  separate : ∀ {σ θ}, M.IsPinnedAutomorphism σ θ →
    σ ∈ c.basePointHom.range → θ = 1

variable {c}

/-- Combine supplied geometry and full faithfulness into the abstract
representative data. No geometric property is inferred here. -/
theorem automorphismSplittingData
    (hiso : AffinePinnedIsomorphismTheoremStatement.{u})
    (hgeometry : M.AutomorphismSplittingGeometry c) :
    Langlands.PinnedQuotient.SplittingData
      c.basePointHom.range M.basedAutomorphisms M.IsPinnedAutomorphism where
  one := M.isPinnedAutomorphism_one
  mul := IsPinnedAutomorphism.mul M
  based := IsPinnedAutomorphism.based M
  unique := M.existsUnique_pinnedAutomorphism hiso
  factor := hgeometry.factor
  separate := hgeometry.separate

variable (p : M.group ⟶ Gad)
  (hp : RelativeRoot.IsFppfQuotient (center M.group) p)
  (hc : c.restrict p = AutomorphicAction.conjugation (𝟙 M.group))

/-- Projection with the exact kernel, range and pinned values, conditional
on the two explicit geometric inputs and pinned full faithfulness. -/
def automorphismProjection
    (hiso : AffinePinnedIsomorphismTheoremStatement.{u})
    (hgeometry : M.AutomorphismSplittingGeometry c) :
    CategoryTheory.Aut M.group →* RootPairing.Aut M.rootDatum := by
  letI := AutomorphicAction.basePointHom_range_normal_of_center_quotient hp hc
  exact (M.automorphismSplittingData hiso hgeometry).projection

theorem automorphismProjection_ker
    (hiso : AffinePinnedIsomorphismTheoremStatement.{u})
    (hgeometry : M.AutomorphismSplittingGeometry c) :
    (M.automorphismProjection p hp hc hiso hgeometry).ker = c.basePointHom.range := by
  let := AutomorphicAction.basePointHom_range_normal_of_center_quotient hp hc
  exact (M.automorphismSplittingData hiso hgeometry).projection_ker

theorem mem_automorphismProjection_range_iff
    (hiso : AffinePinnedIsomorphismTheoremStatement.{u})
    (hgeometry : M.AutomorphismSplittingGeometry c)
    (θ : RootPairing.Aut M.rootDatum) :
    θ ∈ (M.automorphismProjection p hp hc hiso hgeometry).range ↔
      θ ∈ M.basedAutomorphisms := by
  let := AutomorphicAction.basePointHom_range_normal_of_center_quotient hp hc
  exact (M.automorphismSplittingData hiso hgeometry).mem_projection_range_iff θ

theorem automorphismProjection_pinned
    (hiso : AffinePinnedIsomorphismTheoremStatement.{u})
    (hgeometry : M.AutomorphismSplittingGeometry c)
    {σ : CategoryTheory.Aut M.group} {θ : RootPairing.Aut M.rootDatum}
    (hσ : M.IsPinnedAutomorphism σ θ) :
    M.automorphismProjection p hp hc hiso hgeometry σ = θ := by
  let := AutomorphicAction.basePointHom_range_normal_of_center_quotient hp hc
  exact (M.automorphismSplittingData hiso hgeometry).projection_pinned hσ

end AffinePinnedModel

/-- The unchanged target follows from pinned full faithfulness and the explicit
factorization and separation properties for all connected affine pinned models. -/
theorem affinePinnedAutomorphismGroup_of_splitting
    (hiso : AffinePinnedIsomorphismTheoremStatement.{u})
    (hgeometry : ∀ (M : AffinePinnedModel.{u}) [ConnectedSpace M.base]
      (Gad : GroupScheme M.base) (p : M.group ⟶ Gad),
      RelativeRoot.IsFppfQuotient (center M.group) p →
      ∀ c : AutomorphicAction Gad M.group,
        c.restrict p = AutomorphicAction.conjugation (𝟙 M.group) →
        M.AutomorphismSplittingGeometry c) :
    AffinePinnedAutomorphismGroupStatement.{u} := by
  intro R _ _ G hG I _ i J P hclosed hmax hP hlines b X Gad p hp c hc
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Finite J := hP.finite
  let : Fintype J := Fintype.ofFinite J
  let M : AffinePinnedModel.{u} :=
    { ring := R
      group := G
      reductive := hG
      coordinates := I
      inclusion := i
      closed := hclosed
      maximal := hmax
      rootIndex := J
      rootDatum := P
      fibrewiseRootDatum := hP
      rootLines := hlines
      basis := b
      pinning := X }
  have hgeom : M.AutomorphismSplittingGeometry c := hgeometry M Gad p hp c hc
  refine ⟨c.basePointHom, M.automorphismProjection p hp hc hiso hgeom,
    fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact AutomorphicAction.basePointHom_injective_of_center_quotient hp hc
  · exact M.automorphismProjection_ker p hp hc hiso hgeom
  · exact M.mem_automorphismProjection_range_iff p hp hc hiso hgeom
  · exact M.existsUnique_pinnedAutomorphism hiso
  · exact fun _ _ hσ => M.automorphismProjection_pinned p hp hc hiso hgeom hσ

end Langlands.GroupScheme
