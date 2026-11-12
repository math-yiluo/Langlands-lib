import Langlands.Representation.CuspidalSupport.BernsteinLeviSupportPresentation
import Langlands.Representation.CuspidalSupport.BernsteinStandardJacquetStages

/-! # Formal support steps for Bernstein induction and restriction -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance inductionRestrictionReductionAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance inductionRestrictionReductionTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- The literal fibre predicate of the published induction-restriction target. -/
def bernsteinLeviFibreProperty
    (J : Finset (SimpleRoot i ν))
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family) :
    ObjectProperty (SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)) := fun ρ =>
  ∀ τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J),
    τ.IsIrreducible → SmoothRep.IsSubquotient τ ρ →
      ∃ (I : Finset J) (b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
        (h : leviIndex J I = b.roots),
        IsBernsteinInertiaRelated i ν family a b ∧
          SmoothRep.IsSubquotient τ
            ((leviNormalizedInductionFunctor (family.closedLevi J)
              (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
                family.maximalSplitTorus family.genericCocharacter b.roots J
                (h ▸ leviIndex_subset J I))
              (h ▸ family.leviDecomposition J I) (family.closedUnipotent b.roots)).obj
              (bernsteinLiteralLeviRep i ν b.roots b.representation))

/-- Ambient Jacquet exclusion implies the whole restriction assertion of the
published proposition, with no additional inner-Levi support hypothesis. -/
theorem bernsteinLeviFibreProperty_of_jacquetExclusion
    (J : Finset (SimpleRoot i ν))
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hV : BernsteinJacquetExclusion i ν family a V) :
    bernsteinLeviFibreProperty i ν family J a
      ((jacquetFunctor (family.decomposition J) (family.closedUnipotent J)).obj V) := by
  intro τ hτ hτV
  obtain ⟨I, b, h, hbq, hbe⟩ :=
    exists_bernsteinLeviCuspidalDatum_jacquet_quotient_induction_embedding
      i ν family J τ hτ
  rcases b with ⟨K, D, hD, hDc⟩
  dsimp only at h
  subst K
  let b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family :=
    ⟨leviIndex J I, D, hD, hDc⟩
  have hmap := bernsteinLeviJacquet_isSubquotient i ν family J I hτV
  have hbV := smoothSubquotientTransitivity ℂ _ _ _ _ hbq.isSubquotient hmap
  have hbV' := hbV.of_iso_right ((bernsteinStandardJacquetStagesIso i ν family J I).app V)
  have hab : IsBernsteinInertiaRelated i ν family a b := by
    by_contra hab
    exact hV b hab hbV'
  exact ⟨I, b, rfl, hab, hbe.isSubquotient⟩

/-- The published block characterization implies the entire restriction
assertion. Its characterization premise remains explicit. -/
theorem bernsteinLeviFibreProperty_of_blockCharacterization
    (hchar : BernsteinBlockCharacterizationStatement.{uF, uV})
    (J : Finset (SimpleRoot i ν))
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hV : bernsteinSaturatedBlockProperty i ν family
      (bernsteinInertialClass i ν family a) V) :
    bernsteinLeviFibreProperty i ν family J a
      ((jacquetFunctor (family.decomposition J) (family.closedUnipotent J)).obj V) := by
  have hexclusion : BernsteinJacquetExclusion i ν family a V :=
    (hchar F G T i ν family a V).2.2.mp hV
  exact bernsteinLeviFibreProperty_of_jacquetExclusion i ν family J a V hexclusion

/-- The restriction assertion needs only the two remaining source steps
of the published block-characterization reduction. -/
theorem bernsteinLeviFibreProperty_of_embedding_and_exclusion
    (hEmbed : BernsteinFixedLeviBlockEmbedding.{uF, uV} i ν family)
    (hGeom : BernsteinInducedInertiaJacquetExclusion.{uF, uV} i ν family)
    (J : Finset (SimpleRoot i ν))
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hV : bernsteinSaturatedBlockProperty i ν family
      (bernsteinInertialClass i ν family a) V) :
    bernsteinLeviFibreProperty i ν family J a
      ((jacquetFunctor (family.decomposition J) (family.closedUnipotent J)).obj V) := by
  have hexclusion : BernsteinJacquetExclusion i ν family a V :=
    (bernsteinBlockCharacterization_of_embedding_and_exclusion
      i ν family hEmbed hGeom a V).2.2.mp hV
  exact bernsteinLeviFibreProperty_of_jacquetExclusion i ν family J a V hexclusion

private theorem saturatedBlock_of_related_subquotient
    (a b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (V W : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hab : IsBernsteinInertiaRelated i ν family a b)
    (hV : bernsteinSaturatedBlockProperty i ν family
      (bernsteinInertialClass i ν family b) V)
    (hWV : SmoothRep.IsSubquotient W V) :
    bernsteinSaturatedBlockProperty i ν family
      (bernsteinInertialClass i ν family a) W := by
  intro π hπ hπW
  exact (isBernsteinInertialSupport_iff_of_related i ν family hab π).mpr
    (hV π hπ (smoothSubquotientTransitivity ℂ _ V W π hπW hWV))

/-- A single inner cuspidal induction presentation gives the desired ambient
block membership after normalized induction, without a characterization input. -/
theorem bernsteinInduction_mem_block_of_leviPresentation
    (J : Finset (SimpleRoot i ν))
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (I : Finset J) (b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (h : leviIndex J I = b.roots) (hab : IsBernsteinInertiaRelated i ν family a b)
    (ρ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J))
    (hρ : SmoothRep.IsSubquotient ρ
      ((leviNormalizedInductionFunctor (family.closedLevi J)
        (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
          family.maximalSplitTorus family.genericCocharacter b.roots J
          (h ▸ leviIndex_subset J I))
        (h ▸ family.leviDecomposition J I) (family.closedUnipotent b.roots)).obj
        (bernsteinLiteralLeviRep i ν b.roots b.representation))) :
    bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj ρ) := by
  have hρG : SmoothRep.IsSubquotient
      ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj ρ)
      (bernsteinInduction i ν family b) := by
    rcases b with ⟨K, D, hD, hDc⟩
    dsimp only at h
    cases h
    have hstage := bernsteinStandardInduction_stages_isSubquotient.{uF, uV} i ν family J I
      (bernsteinLiteralLeviRep i ν (leviIndex J I) D) ρ
    exact hstage hρ
  exact saturatedBlock_of_related_subquotient i ν family a b
    (bernsteinInduction i ν family b)
    ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj ρ)
    hab (bernsteinInduction_mem_saturatedBlock i ν family b) hρG

/-- The induction assertion for every irreducible fibred input. Extending this
to arbitrary smooth inputs is a separate remaining obligation. -/
theorem bernsteinInduction_mem_block_of_irreducible_fibre
    (J : Finset (SimpleRoot i ν))
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ρ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J))
    (hρ : ρ.IsIrreducible) (hfibre : bernsteinLeviFibreProperty i ν family J a ρ) :
    bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj ρ) := by
  have hself : SmoothRep.IsSubquotient ρ ρ :=
    SmoothRep.IsSubrepresentation.isSubquotient ⟨𝟙 ρ, Function.injective_id⟩
  obtain ⟨I, b, h, hab, hpres⟩ := hfibre ρ hρ hself
  exact bernsteinInduction_mem_block_of_leviPresentation i ν family J a I b h hab ρ hpres

end Langlands.CuspidalSupport
