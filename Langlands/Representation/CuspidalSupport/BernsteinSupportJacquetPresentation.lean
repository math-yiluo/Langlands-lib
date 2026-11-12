import Langlands.Representation.CuspidalSupport.BernsteinCuspidalSupportExistence
import Langlands.Representation.CuspidalSupport.BernsteinBlockCharacterizationReduction
import Langlands.Representation.Aubert.General.FirstAdjointnessConsequences

/-! # Simultaneous induction and Jacquet cuspidal presentations -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

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

local instance supportJacquetAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance supportJacquetAmbientTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance supportJacquetLeviClosedImmersion (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance supportJacquetLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance supportJacquetLeviFiniteType (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance supportJacquetLeviTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

omit [LocallyOfFiniteType G.X.hom] in
/-- The datum of an actual induction embedding is a quotient of the Jacquet
module, by normalized first adjointness and irreducibility of that datum. -/
theorem bernsteinJacquet_isQuotient_of_induction_subrepresentation
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    [Nontrivial π]
    (hπ : SmoothRep.IsSubrepresentation π (bernsteinInduction i ν family a)) :
    SmoothRep.IsQuotient (bernsteinLiteralLeviRep i ν a.roots a.representation)
      ((jacquetFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj π) := by
  obtain ⟨f, hf⟩ := hπ
  have hfn : SmoothRep.hom f ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := exists_ne (0 : π)
    apply hv
    apply hf
    rw [hz]
    rfl
  have ha : (bernsteinLiteralLeviRep i ν a.roots a.representation).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff a.representation.representation
      (leviRationalPointHomeomorph i ν a.roots).symm).mpr a.irreducible
  let hδ := standardUnipotent_isUnimodular_of_standardCocharacterStatement
    i ν standardCocharacter family.connectedReductive family.maximalSplitTorus
    family.genericCocharacter a.roots (family.closedUnipotent a.roots)
  exact ⟨SmoothRep.ofHom (FirstAdjointness.equiv (family.decomposition a.roots)
    (family.closedUnipotent a.roots) hδ π _ (SmoothRep.hom f)),
    FirstAdjointness.equiv_surjective (family.decomposition a.roots)
      (family.closedUnipotent a.roots) hδ π _ ha (SmoothRep.hom f) hfn⟩

/-- Every irreducible has one genuine datum providing both an induction
embedding and a quotient of its actual standard Jacquet module. -/
theorem exists_bernsteinCuspidalDatum_jacquet_quotient_induction_embedding
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hπ : π.IsIrreducible) :
    ∃ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
      SmoothRep.IsQuotient (bernsteinLiteralLeviRep i ν a.roots a.representation)
        ((jacquetFunctor (family.decomposition a.roots)
          (family.closedUnipotent a.roots)).obj π) ∧
      SmoothRep.IsSubrepresentation π (bernsteinInduction i ν family a) := by
  let := hπ
  have : Nontrivial π :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule
  obtain ⟨a, ha⟩ := exists_bernsteinCuspidalDatum_induction_subrepresentation i ν family π hπ
  exact ⟨a, bernsteinJacquet_isQuotient_of_induction_subrepresentation i ν family a π ha, ha⟩

/-- Choose the same datum for induction and Jacquet support, retaining both
actual map-existence witnesses at the original saturated carrier universe. -/
def bernsteinCuspidalJacquetPresentation
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hπ : π.IsIrreducible) :
    { a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family //
      SmoothRep.IsQuotient (bernsteinLiteralLeviRep i ν a.roots a.representation)
        ((jacquetFunctor (family.decomposition a.roots)
          (family.closedUnipotent a.roots)).obj π) ∧
      SmoothRep.IsSubrepresentation π (bernsteinInduction i ν family a) } :=
  Classical.indefiniteDescription _
    (exists_bernsteinCuspidalDatum_jacquet_quotient_induction_embedding i ν family π hπ)

/-- Condition (iii) implies membership in the original saturated Bernstein
block, without a support-comparison or support-uniqueness premise. -/
theorem bernsteinJacquetExclusion_implies_block
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hV : BernsteinJacquetExclusion i ν family a V) :
    bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a) V := by
  intro π hπ hπV
  obtain ⟨b, hbq, hbe⟩ :=
    exists_bernsteinCuspidalDatum_jacquet_quotient_induction_embedding i ν family π hπ
  have hbV := smoothSubquotientTransitivity ℂ _ _ _ _ hbq.isSubquotient
    (bernsteinJacquet_isSubquotient i ν family b.roots hπV)
  have hab : IsBernsteinInertiaRelated i ν family a b := by
    by_contra hab
    exact hV b hab hbV
  exact (isBernsteinInertialSupport_representative_iff i ν family a π).mpr
    ⟨b, hab, hπ, hbe.isSubquotient⟩

/-- The forward class-level support comparison needs only uniqueness of
induction-defined inertial support; simultaneous presentation supplies the
Jacquet witness. -/
theorem bernsteinJacquetInertialSupport_of_support_of_uniqueness
    (hunique : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    (s : BernsteinInertialClass.{uF, max uF uV} i ν family)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hπ : IsBernsteinInertialSupport i ν family s π) :
    IsBernsteinJacquetInertialSupport i ν family s π := by
  obtain ⟨a, ha, hπa⟩ := hπ
  obtain ⟨b, hbq, hbe⟩ :=
    exists_bernsteinCuspidalDatum_jacquet_quotient_induction_embedding i ν family π hπa.1
  have hb : IsBernsteinCuspidalSupport i ν family b π := ⟨hπa.1, hbe.isSubquotient⟩
  have heq := hunique π _ _ hb.inertial ⟨a, ha, hπa⟩
  exact ⟨b, heq, hπa.1, hbq.isSubquotient⟩

/-- Only fixed-Levi embeddings and geometric exclusion remain as inputs to
the three equivalences. Support existence and the reverse implication from
condition (iii) are discharged here. -/
theorem bernsteinBlockCharacterization_of_embedding_and_exclusion
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
  have h3B := bernsteinJacquetExclusion_implies_block i ν family a V
  exact ⟨⟨hEmbed a V, fun h => h3B (h23 (h12 h))⟩,
    ⟨fun h => h12 (hEmbed a V h), fun h => h3B (h23 h)⟩,
    ⟨fun h => h23 (h12 (hEmbed a V h)), h3B⟩⟩

end Langlands.CuspidalSupport
