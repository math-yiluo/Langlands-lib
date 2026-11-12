import Langlands.Representation.CuspidalSupport.BernsteinJacquetInertiaExclusion
import Langlands.Representation.CuspidalSupport.BernsteinSupportComparison
import Langlands.Representation.Aubert.General.JacquetColimits
import Langlands.Representation.Filtration.ExactSmoothSubquotients

/-! # The formal implications in the Bernstein block characterization -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
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

local instance instBernsteinBlockCharacterizationReductionGroupAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance instBernsteinBlockCharacterizationReductionTopology :
    TopologicalSpace (rationalPoints G) := pointTopology
local instance instBernsteinBlockCharacterizationReductionLeviClosedImmersion (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance instBernsteinBlockCharacterizationReductionLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance instBernsteinBlockCharacterizationReductionLeviFiniteType (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance instBernsteinBlockCharacterizationReductionLeviPointTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

omit [LocallyOfFiniteType G.X.hom] in
/-- The actual standard normalized Jacquet functor preserves every actual
subquotient. Compact containment supplies its exactness. -/
theorem bernsteinJacquet_isSubquotient
    (I : Finset (SimpleRoot i ν))
    {V W : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)}
    (hWV : SmoothRep.IsSubquotient W V) :
    SmoothRep.IsSubquotient
      ((jacquetFunctor (family.decomposition I) (family.closedUnipotent I)).obj W)
      ((jacquetFunctor (family.decomposition I) (family.closedUnipotent I)).obj V) := by
  apply ExactSmoothTransport.map_isSubquotient _ _ hWV
  intro A B C f g hf hg hfg
  have h := jacquetFunctor_map_isShortExact (family.decomposition I)
    (family.closedUnipotent I)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter family.connectedReductive family.maximalSplitTorus
      family.genericCocharacter I) f g ⟨hf, hg, hfg⟩
  exact ⟨h.1, h.2.2, h.2.1⟩

/-- Condition (iii) passes to arbitrary actual subquotients. -/
theorem bernsteinJacquetExclusion_of_isSubquotient
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    {V W : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)}
    (hV : BernsteinJacquetExclusion i ν family a V)
    (hWV : SmoothRep.IsSubquotient W V) :
    BernsteinJacquetExclusion i ν family a W := by
  intro b hab hbW
  exact hV b hab (smoothSubquotientTransitivity ℂ _ _ _ _ hbW
    (bernsteinJacquet_isSubquotient i ν family b.roots hWV))

/-- Condition (iii) passes to actual direct sums at the target's index universe.
This uses the proved colimit preservation of normalized Jacquet restriction. -/
theorem bernsteinJacquetExclusion_directSum
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    {κ : Type (max uF uV)} [DecidableEq κ]
    (A : κ → SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hA : ∀ k, BernsteinJacquetExclusion i ν family a (A k)) :
    BernsteinJacquetExclusion i ν family a (SmoothRep.directSum A) := by
  intro b hab hbSum
  let J := jacquetFunctor (family.decomposition b.roots) (family.closedUnipotent b.roots)
  let s : Cofan (fun k => J.obj (A k)) :=
    Cofan.mk (J.obj (SmoothRep.directSum A)) (fun k => J.map (SmoothRep.directSumι A k))
  have hs : IsColimit s :=
    isColimitCofanMkObjOfIsColimit J A (SmoothRep.directSumι A)
      (SmoothRep.directSumIsColimit A)
  let e : SmoothRep.directSum (fun k => J.obj (A k)) ≅ J.obj (SmoothRep.directSum A) :=
    SmoothRep.mkIso (SmoothRep.cofanDirectSumEquiv _ s hs)
  have hirr : (bernsteinLiteralLeviRep i ν b.roots b.representation).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff b.representation.representation
      (leviRationalPointHomeomorph i ν b.roots).symm).mpr b.irreducible
  obtain ⟨k, hk⟩ := SmoothRep.irreducibleSubquotient_directSum
    (fun k => J.obj (A k)) hirr (hbSum.of_iso_right e.symm)
  exact hA k b hab hk

/-- Existence of actual cuspidal support and the published class-level
induction/Jacquet comparison imply (iii) -> membership in the original block. -/
theorem bernsteinSaturatedBlockProperty_of_jacquetExclusion
    (hExist : BernsteinCuspidalSupportExistenceStatement.{uF, uV} i ν family)
    (hCompare : BernsteinInductionJacquetSupportComparisonStatement.{uF, uV} i ν family)
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hV : BernsteinJacquetExclusion i ν family a V) :
    bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a) V := by
  classical
  intro π hπ hπV
  obtain ⟨c, hc⟩ := hExist π hπ
  obtain ⟨b, hb, hbj⟩ := (hCompare (bernsteinInertialClass i ν family c) π).mp hc.inertial
  have hbV : SmoothRep.IsSubquotient (bernsteinLiteralLeviRep i ν b.roots b.representation)
      ((jacquetFunctor (family.decomposition b.roots) (family.closedUnipotent b.roots)).obj V) :=
    smoothSubquotientTransitivity ℂ _ _ _ _ hbj.2
      (bernsteinJacquet_isSubquotient i ν family b.roots hπV)
  have hab : IsBernsteinInertiaRelated i ν family a b := by
    by_contra hab
    exact hV b hab hbV
  have hac : IsBernsteinInertiaRelated i ν family a c :=
    hab.trans ((bernsteinInertialClass_eq_iff i ν family b c).mp hb)
  exact (isBernsteinInertialSupport_representative_iff i ν family a π).mpr ⟨c, hac, hc⟩

/-- The actual sum of normalized inductions from one fixed standard Levi. -/
def bernsteinInertiaInducedSum
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    {κ : Type (max uF uV)} [DecidableEq κ]
    (τ : κ → SmoothRep.{0, uF, max uF uV} ℂ
      (rationalPoints (bernsteinLeviScheme i ν a.roots))) :
    SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) :=
  SmoothRep.directSum fun k =>
    (normalizedInductionFunctor (family.decomposition a.roots)
      (family.closedUnipotent a.roots)).obj (bernsteinLiteralLeviRep i ν a.roots (τ k))

/-- Condition (i), with its actual witnesses and the published inertia property. -/
def BernsteinInertiaInducedEmbedding
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) : Prop :=
  ∃ (κ : Type (max uF uV))
    (τ : κ → SmoothRep.{0, uF, max uF uV} ℂ
      (rationalPoints (bernsteinLeviScheme i ν a.roots))),
    (∀ k, rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots)
      a.representation (τ k)) ∧
    letI := Classical.decEq κ
    SmoothRep.IsSubrepresentation V (bernsteinInertiaInducedSum i ν family a τ)

/-- Condition (ii), with the same actual inducing data as condition (i). -/
def BernsteinInertiaInducedSubquotient
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) : Prop :=
  ∃ (κ : Type (max uF uV))
    (τ : κ → SmoothRep.{0, uF, max uF uV} ℂ
      (rationalPoints (bernsteinLeviScheme i ν a.roots))),
    (∀ k, rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots)
      a.representation (τ k)) ∧
    letI := Classical.decEq κ
    SmoothRep.IsSubquotient V (bernsteinInertiaInducedSum i ν family a τ)

/-- The fixed-Levi embedding step of the source proof, retained explicitly.
It is not proved by the formal reduction below. -/
def BernsteinFixedLeviBlockEmbedding : Prop :=
  ∀ (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)),
    bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a) V →
      BernsteinInertiaInducedEmbedding i ν family a V

/-- The geometric exclusion step, for an arbitrary inducing object in a
single same-Levi inertia block. This target adds no assumed law to the data. -/
def BernsteinInducedInertiaJacquetExclusion : Prop :=
  ∀ (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (τ : SmoothRep.{0, uF, max uF uV} ℂ
      (rationalPoints (bernsteinLeviScheme i ν a.roots))),
    rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation τ →
      BernsteinJacquetExclusion i ν family a
        ((normalizedInductionFunctor (family.decomposition a.roots)
          (family.closedUnipotent a.roots)).obj (bernsteinLiteralLeviRep i ν a.roots τ))

/-- The geometric exclusion and the two published support targets imply the
shared induced-inertia membership bridge needed by Bernstein decomposition. -/
theorem bernsteinInduction_inertiaBlock_mem_saturatedBlock
    (hExist : BernsteinCuspidalSupportExistenceStatement.{uF, uV} i ν family)
    (hCompare : BernsteinInductionJacquetSupportComparisonStatement.{uF, uV} i ν family)
    (hGeom : BernsteinInducedInertiaJacquetExclusion.{uF, uV} i ν family)
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (τ : SmoothRep.{0, uF, max uF uV} ℂ
      (rationalPoints (bernsteinLeviScheme i ν a.roots)))
    (hτ : rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation τ) :
    bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      ((normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj (bernsteinLiteralLeviRep i ν a.roots τ)) :=
  bernsteinSaturatedBlockProperty_of_jacquetExclusion i ν family hExist hCompare a _
    (hGeom a τ hτ)

/-- The elementary implication (i) -> (ii) retains the same family. -/
theorem bernsteinInertiaInducedSubquotient_of_embedding
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (h : BernsteinInertiaInducedEmbedding i ν family a V) :
    BernsteinInertiaInducedSubquotient i ν family a V := by
  obtain ⟨κ, τ, hτ, hV⟩ := h
  exact ⟨κ, τ, hτ, hV.isSubquotient⟩

/-- Exact Jacquet restriction and coproduct preservation extend the single
induction geometric input to (ii) -> (iii), with no finiteness assumption. -/
theorem bernsteinJacquetExclusion_of_inducedSubquotient
    (hGeom : BernsteinInducedInertiaJacquetExclusion.{uF, uV} i ν family)
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (h : BernsteinInertiaInducedSubquotient i ν family a V) :
    BernsteinJacquetExclusion i ν family a V := by
  classical
  obtain ⟨κ, τ, hτ, hV⟩ := h
  exact bernsteinJacquetExclusion_of_isSubquotient i ν family a
    (bernsteinJacquetExclusion_directSum i ν family a _ (fun k => hGeom a (τ k) (hτ k))) hV

/-- The entire chain of equivalences, conditional on the two support targets
and the two remaining source steps. None of those four inputs is discharged. -/
theorem bernsteinBlockCharacterization_of_inputs
    (hExist : BernsteinCuspidalSupportExistenceStatement.{uF, uV} i ν family)
    (hCompare : BernsteinInductionJacquetSupportComparisonStatement.{uF, uV} i ν family)
    (hEmbed : BernsteinFixedLeviBlockEmbedding.{uF, uV} i ν family)
    (hGeom : BernsteinInducedInertiaJacquetExclusion.{uF, uV} i ν family)
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) :
    (bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a) V ↔
      BernsteinInertiaInducedEmbedding i ν family a V) ∧
    (bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a) V ↔
      BernsteinInertiaInducedSubquotient i ν family a V) ∧
    (bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a) V ↔
      BernsteinJacquetExclusion i ν family a V) := by
  have h12 := bernsteinInertiaInducedSubquotient_of_embedding i ν family a V
  have h23 := bernsteinJacquetExclusion_of_inducedSubquotient i ν family hGeom a V
  have h3B := bernsteinSaturatedBlockProperty_of_jacquetExclusion i ν family hExist hCompare a V
  exact ⟨⟨hEmbed a V, fun h => h3B (h23 (h12 h))⟩,
    ⟨fun h => h12 (hEmbed a V h), fun h => h3B (h23 h)⟩,
    ⟨fun h => h23 (h12 (hEmbed a V h)), h3B⟩⟩

/-- The precise global prerequisites for this reduction, at the unchanged
universes of the published characterization. This is a target, not an axiom. -/
def BernsteinBlockCharacterizationPrerequisites : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν),
      BernsteinCuspidalSupportExistenceStatement.{uF, uV} i ν family ∧
      BernsteinInductionJacquetSupportComparisonStatement.{uF, uV} i ν family ∧
      BernsteinFixedLeviBlockEmbedding.{uF, uV} i ν family ∧
      BernsteinInducedInertiaJacquetExclusion.{uF, uV} i ν family

/-- Assemble the conditional proof of the exact published proposition.
The prerequisites remain a genuine additional hypothesis. -/
theorem bernsteinBlockCharacterization_of_prerequisites
    (h : BernsteinBlockCharacterizationPrerequisites.{uF, uV}) :
    BernsteinBlockCharacterizationStatement.{uF, uV} := by
  intro F _ _ _ _ G _ _ T i ν _ _ family a
  dsimp only
  intro V
  obtain ⟨hExist, hCompare, hEmbed, hGeom⟩ := h F G T i ν family
  exact bernsteinBlockCharacterization_of_inputs i ν family hExist hCompare hEmbed hGeom a V

end Langlands.CuspidalSupport
