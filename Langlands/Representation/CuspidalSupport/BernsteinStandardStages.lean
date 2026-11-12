import Langlands.Representation.CuspidalSupport.BernsteinInductionRestrictionStatement
import Langlands.Representation.Aubert.General.RationalInductionStages
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.Representation.Aubert.General.RationalSupportInduction
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-! # Standard induction and Jacquet stages at the Bernstein carrier universes -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

private theorem inductionSubquotientOfStagesIso
    {C : Type*} [Category C]
    {H M : Type*} [Group H] [TopologicalSpace H] [Group M] [TopologicalSpace M]
    (inner : C ⥤ SmoothRep ℂ M)
    (outer : SmoothRep ℂ M ⥤ SmoothRep ℂ H)
    (direct : C ⥤ SmoothRep ℂ H)
    (e : inner ⋙ outer ≅ direct)
    (houter : ∀ {A B}, SmoothRep.IsSubquotient B A →
      SmoothRep.IsSubquotient (outer.obj B) (outer.obj A))
    (σ : C) (τ : SmoothRep ℂ M)
    (hτ : SmoothRep.IsSubquotient τ (inner.obj σ)) :
    SmoothRep.IsSubquotient (outer.obj τ) (direct.obj σ) :=
  SmoothRep.IsSubquotient.of_iso_right (houter hτ) (e.app σ)

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinStandardStagesAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinStandardStagesTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance bernsteinStandardStagesFieldT2 : T2Space F :=
  BruhatTits.localField_t2Space F
local instance bernsteinStandardStagesT2 : T2Space (rationalPoints G) :=
  rationalPoint_t2Space F G

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- Normalized induction in stages at `max uF uV`, without a successor-universe
restriction on the carrier. All normalization inputs follow from the standard family. -/
@[irreducible] def bernsteinStandardInductionStagesIso
    (J : Finset (SimpleRoot i ν)) (I : Finset J) :
    leviNormalizedInductionFunctor.{uF, max uF uV} (family.closedLevi J)
        (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
          family.maximalSplitTorus family.genericCocharacter _ J (leviIndex_subset J I))
        (family.leviDecomposition J I) (family.closedUnipotent (leviIndex J I)) ⋙
      normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J) ≅
    normalizedInductionFunctor (family.decomposition (leviIndex J I))
      (family.closedUnipotent (leviIndex J I)) := by
  exact normalizedInductionStagesIso
    (family.decomposition (leviIndex J I)) (family.decomposition J) (family.closedLevi J)
    (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
      family.maximalSplitTorus family.genericCocharacter _ J (leviIndex_subset J I))
    (family.leviDecomposition J I) (family.closedUnipotent (leviIndex J I))
    (family.closedUnipotent J)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter family.connectedReductive family.maximalSplitTorus
      family.genericCocharacter (leviIndex J I))
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter family.connectedReductive family.maximalSplitTorus
      family.genericCocharacter J)
    (isLimitOfCompactSubgroups_subgroupOf _ _ (family.closedLevi J)
      (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν standardCocharacter family.connectedReductive family.maximalSplitTorus
        family.genericCocharacter (leviIndex J I)))
    (standardJacquetModulus_stages i ν standardLeviIntersection family.connectedReductive
      family.maximalSplitTorus family.genericCocharacter standardCocharacter
      (continuous_standard_projection i ν standardCocharacter family.connectedReductive
        family.maximalSplitTorus family.genericCocharacter) J I
      family.closedUnipotent (family.closedLevi J))
    (parabolic_le_of_subset i ν standardLeviIntersection family.connectedReductive
      family.maximalSplitTorus family.genericCocharacter standardCocharacter
      _ J (leviIndex_subset J I))
    (unipotent_le_of_subset i ν standardLeviIntersection family.connectedReductive
      family.maximalSplitTorus family.genericCocharacter _ J (leviIndex_subset J I))
    (continuous_standard_projection i ν standardCocharacter family.connectedReductive
      family.maximalSplitTorus family.genericCocharacter J)

omit [LocallyOfFiniteType G.X.hom] in
/-- Actual normalized induction preserves subquotients at the saturated
Bernstein carrier universe. -/
theorem bernsteinStandardInduction_isSubquotient
    (J : Finset (SimpleRoot i ν))
    {A B : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)}
    (hBA : SmoothRep.IsSubquotient B A) :
    SmoothRep.IsSubquotient
      ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj B)
      ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj A) := by
  apply ExactSmoothTransport.map_isSubquotient _ _ hBA
  intro A B C f g hf hg hfg
  have h := normalizedInductionFunctor_map_isShortExact
    (compactOpenCofinal_of_nonarchimedean _) (family.decomposition J)
    (family.closedUnipotent J)
    (standardParabolic_isClosed_of_standardCocharacterStatement
      i ν standardCocharacter family.connectedReductive family.maximalSplitTorus
      family.genericCocharacter J)
    (continuous_standard_projection i ν standardCocharacter family.connectedReductive
      family.maximalSplitTorus family.genericCocharacter J) f g ⟨hf, hg, hfg⟩
  exact ⟨h.1, h.2.2, h.2.1⟩

omit [LocallyOfFiniteType G.X.hom] in
set_option backward.isDefEq.respectTransparency.types true in
/-- A Levi subquotient presentation induces to the ambient presentation, at
exactly the universes of the Bernstein induction-restriction target. -/
theorem bernsteinStandardInduction_stages_isSubquotient
    (J : Finset (SimpleRoot i ν)) (I : Finset J)
    (σ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν (leviIndex J I)))
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J))
    (hτ : SmoothRep.IsSubquotient τ
      ((leviNormalizedInductionFunctor (family.closedLevi J)
        (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
          family.maximalSplitTorus family.genericCocharacter _ J (leviIndex_subset J I))
        (family.leviDecomposition J I) (family.closedUnipotent (leviIndex J I))).obj σ)) :
    SmoothRep.IsSubquotient
      ((normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)).obj τ)
      ((normalizedInductionFunctor (family.decomposition (leviIndex J I))
        (family.closedUnipotent (leviIndex J I))).obj σ) := by
  let inner := leviNormalizedInductionFunctor.{uF, max uF uV} (family.closedLevi J)
    (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
      family.maximalSplitTorus family.genericCocharacter _ J (leviIndex_subset J I))
    (family.leviDecomposition J I) (family.closedUnipotent (leviIndex J I))
  let outer := normalizedInductionFunctor.{uF, max uF uV}
    (family.decomposition J) (family.closedUnipotent J)
  let direct := normalizedInductionFunctor.{uF, max uF uV}
    (family.decomposition (leviIndex J I)) (family.closedUnipotent (leviIndex J I))
  exact inductionSubquotientOfStagesIso inner outer direct
    (bernsteinStandardInductionStagesIso i ν family J I)
    (fun {_ _} h => bernsteinStandardInduction_isSubquotient i ν family J h) σ τ hτ

end Langlands.CuspidalSupport
