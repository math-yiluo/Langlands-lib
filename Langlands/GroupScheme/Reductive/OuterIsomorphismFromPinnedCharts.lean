import Langlands.GroupScheme.Reductive.PinnedOuterIsomorphismChartStatement
import Langlands.GroupScheme.Reductive.GenericOuterIsomorphismSchemeExistenceStatement
import Langlands.GroupScheme.Reductive.AffinePinnedAtlas
import Langlands.GroupScheme.Adjoint.SourceIsomorphismTransport
import Langlands.GroupScheme.IsomorphismSchemeLocalSection
import Langlands.GroupScheme.OuterIsomorphismConstantSection
import Langlands.GroupScheme.Descent.Data
import Langlands.AlgebraicGeometry.Sites.EtaleFppfComparison

/-! # Outer-isomorphism quotients from the pinned constant-chart statement -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
  Langlands.AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace PinnedOuterIsomorphismChartStatement

variable (hchart : PinnedOuterIsomorphismChartStatement.{u})

include hchart

/-- The pinned chart statement also applies to supplied groups identified with the two models. -/
theorem constantSection_of_isomorphisms
    {S : Scheme.{u}} {G H A : GroupScheme S}
    (M N : AffinePinnedModel.{u}) (f : S ⟶ M.base) (g : S ⟶ N.base)
    (i : G ≅ M.groupOver f) (j : H ≅ N.groupOver g)
    (q : G ⟶ A) (hq : IsRelativeAdjointQuotient q)
    (I : GroupIsomorphismScheme G H) :
    ∃ (D : Type u) (s : GroupIsomorphismScheme.constantParameter S D ⟶ I.parameter),
      ∀ (T : Over S), Function.Bijective
        (fun z : (T ⟶ A.X) ×
            (T ⟶ GroupIsomorphismScheme.constantParameter S D) =>
          lift z.1 (z.2 ≫ s) ≫ I.actionHom hq.innerAction) := by
  let J := (I.precompose i.symm).postcompose j
  let hp := hq.precompose i.symm
  obtain ⟨D, s, hs⟩ := hchart M N S f g A (i.inv ≫ q) hp J
  refine ⟨D, s, fun T => ?_⟩
  have he : ∀ (d : T ⟶ A.X) (p : T ⟶ I.parameter),
      lift d p ≫ J.actionHom hp.innerAction = lift d p ≫ I.actionHom hq.innerAction :=
    fun d p =>
      ((I.precompose i.symm).postcompose_actionHom j hp.innerAction d p).trans
        (I.precompose_actionHom i.symm hq.innerAction hp.innerAction
          (fun _ d g => hq.innerAction_precompose i.symm d g) d p)
  have hf :
      (fun z : (T ⟶ A.X) × (T ⟶ GroupIsomorphismScheme.constantParameter S D) =>
        lift z.1 (z.2 ≫ s) ≫ J.actionHom hp.innerAction) =
      (fun z : (T ⟶ A.X) × (T ⟶ GroupIsomorphismScheme.constantParameter S D) =>
        lift z.1 (z.2 ≫ s) ≫ I.actionHom hq.innerAction) :=
    funext fun z => he z.1 (z.2 ≫ s)
  exact hf ▸ hs T

end PinnedOuterIsomorphismChartStatement

namespace AffinePinnedAtlas

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- The sieve of tests on which the actual group pullback is a supplied pinned model. -/
def modelSieve : Sieve (Over.mk (𝟙 S)) where
  arrows {U} _ :=
    ∃ (M : AffinePinnedModel.{u}) (f : U.left ⟶ M.base),
      Nonempty ((GroupScheme.baseChange U.hom).obj G ≅ M.groupOver f)
  downward_closed {U V} {g} hg t := by
    obtain ⟨M, f, ⟨i⟩⟩ := hg
    refine ⟨M, t.left ≫ f, ⟨?_⟩⟩
    exact (Descent.pullbackComparison U.hom t.left V.hom (Over.w t) G).symm ≪≫
      (GroupScheme.baseChange t.left).mapIso i ≪≫
        (baseChangeCompIso f t.left M.group).symm

/-- The supplied affine pinned atlas gives a covering sieve on the relative base. -/
theorem modelSieve_mem (hG : IsReductive G) :
    modelSieve G ∈ fppfTopology S (Over.mk (𝟙 S)) := by
  let A := AffinePinnedAtlas.ofReductive hG
  let J : Sieve (Over.mk (𝟙 S)) :=
    Sieve.ofArrows (fun s : S => Over.mk (A.chart s).map)
      (fun s => Over.homMk (A.chart s).map (by simp))
  have hJ : J ∈ fppfTopology S (Over.mk (𝟙 S)) := by
    change J ∈ (Scheme.fppfTopology.over S) _
    rw [GrothendieckTopology.mem_over_iff]
    change Sieve.overEquiv _ (Sieve.ofArrows _ _) ∈ Scheme.fppfTopology _
    rw [Sieve.overEquiv_ofArrows]
    exact (Precoverage.toGrothendieck_mono
      Langlands.AlgebraicGeometry.Sites.etalePrecoverage_le_fppfPrecoverage)
        _ A.cover.mem_grothendieckTopology
  apply (fppfTopology S).superset_covering ?_ hJ
  intro U g hg
  obtain ⟨s, t, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  apply (modelSieve G).downward_closed
  refine ⟨(A.chart s).model, 𝟙 _, ⟨?_⟩⟩
  exact (A.chart s).iso ≪≫ (baseChangeIdIso (A.chart s).model.group).symm

end AffinePinnedAtlas

namespace GroupIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}

/-- Pinned constant charts and the actual pinned atlases represent the canonical
action quotient for every supplied reductive Isom representative. -/
def quotientRepresentationOfPinnedOuterCharts
    (hchart : PinnedOuterIsomorphismChartStatement.{u})
    (hG : IsReductive G) (hH : IsReductive H)
    (q : G ⟶ A) (hq : IsRelativeAdjointQuotient q)
    (I : GroupIsomorphismScheme G H) :
    SchemeAction.QuotientRepresentation (I.modObj hq.innerAction) := by
  let : Smooth A.X.hom := hq.isReductive_target.smooth
  have ha : hq.innerAction.IsFaithful :=
    AutomorphicAction.isFaithful_of_isFppfQuotient_center hq.isQuotient
      hq.innerAction hq.innerAction_restrict
  let J := AffinePinnedAtlas.modelSieve G ⊓ AffinePinnedAtlas.modelSieve H
  have hJ : J ∈ fppfTopology S (Over.mk (𝟙 S)) :=
    (fppfTopology S).intersection_covering
      (AffinePinnedAtlas.modelSieve_mem G hG) (AffinePinnedAtlas.modelSieve_mem H hH)
  apply SchemeAction.quotientRepresentationOfLocalSections (I.modObj hq.innerAction)
    (I.actionHom_injective_of_isFaithful _ ha) J hJ
  intro U g hg
  obtain ⟨M, f, ⟨i⟩⟩ := hg.1
  obtain ⟨N, k, ⟨j⟩⟩ := hg.2
  obtain ⟨D, s, hs⟩ := hchart.constantSection_of_isomorphisms M N f k i j
    ((GroupScheme.baseChange U.hom).map q) (hq.baseChange U.hom) (I.baseChange U.hom)
  have hs' : ∀ (T : Over U.left), Function.Bijective
      (fun z : (T ⟶ ((GroupScheme.baseChange U.hom).obj A).X) ×
          (T ⟶ constantParameter U.left D) =>
        lift z.1 (z.2 ≫ s) ≫ (I.baseChange U.hom).actionHom
          (hq.innerAction.baseChange U.hom)) := by
    rw [hq.innerAction_baseChange]
    exact hs
  refine ⟨(Over.map U.hom).obj (constantParameter U.left D),
    LocalSectionBase.projection U.hom (constantParameter U.left D),
    I.localSection U.hom s, ?_, ?_, ?_, ?_⟩
  · change IsSeparated (constantParameter U.left D).hom
    infer_instance
  · change LocallyQuasiFinite (constantParameter U.left D).hom
    infer_instance
  · change LocallyOfFiniteType (constantParameter U.left D).hom
    infer_instance
  · exact I.localSection_bijective hq.innerAction U.hom s hs'

/-- Pinned constant charts and the actual pinned atlases construct the outer quotient
for every supplied reductive Isom representative and full-centre quotient. -/
def outerOfPinnedOuterCharts
    (hchart : PinnedOuterIsomorphismChartStatement.{u})
    (hG : IsReductive G) (hH : IsReductive H)
    (q : G ⟶ A) (hq : IsRelativeAdjointQuotient q)
    (I : GroupIsomorphismScheme G H) :
    OuterIsomorphismScheme I hq.innerAction := by
  let : Smooth A.X.hom := hq.isReductive_target.smooth
  let : IsAffineHom A.X.hom := hq.isReductive_target.isAffineHom
  have ha : hq.innerAction.IsFaithful :=
    AutomorphicAction.isFaithful_of_isFppfQuotient_center hq.isQuotient
      hq.innerAction hq.innerAction_restrict
  exact I.outerOfQuotientRepresentation hq.innerAction ha
    (quotientRepresentationOfPinnedOuterCharts hchart hG hH q hq I)

end GroupIsomorphismScheme

/-- The unchanged generic DVR existence target follows from the explicit pinned chart input. -/
theorem genericOuterIsomorphismSchemeExistence_of_pinnedCharts
    (hchart : PinnedOuterIsomorphismChartStatement.{u}) :
    GenericOuterIsomorphismSchemeExistenceStatement.{u} := by
  intro R _ _ _ K _ _ _ G H hG hH _ A q hq I
  exact ⟨I.outerOfPinnedOuterCharts hchart hG hH q hq⟩

end Langlands.GroupScheme
