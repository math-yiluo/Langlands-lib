import Langlands.Representation.CuspidalSupport.BernsteinSupportComparison
import Langlands.Representation.Aubert.General.RationalMinimalJacquetArbitraryCarrier
import Langlands.Representation.Aubert.General.RationalLeviCuspidalJacquet
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction
import Langlands.BruhatTits.Parabolic.QuotientCompactProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardLeviIntersectionProof

/-! # Actual Bernstein cuspidal support at the saturated carrier universe -/

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
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinCuspidalSupportExistenceInstance1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance bernsteinCuspidalSupportExistenceInstance2 : TopologicalSpace (rationalPoints G) := pointTopology
local instance bernsteinCuspidalSupportExistenceInstance3 (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinCuspidalSupportExistenceInstance4 (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinCuspidalSupportExistenceInstance5 (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- Every irreducible at the saturated carrier universe embeds into induction
of an actual Bernstein cuspidal datum at that same carrier universe. -/
theorem exists_bernsteinCuspidalDatum_induction_subrepresentation
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hπ : π.IsIrreducible) :
    ∃ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
      SmoothRep.IsSubrepresentation π (bernsteinInduction i ν family a) := by
  have := family.maximalSplitTorus.isSplitSubtorus.mono
  let := hπ
  have : Nontrivial π :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule
  have hRoots : HasRelativeRootSystem i :=
    relativeRootSystem F G family.connectedReductive T i family.maximalSplitTorus
  obtain ⟨I, hI, hcusp⟩ :=
    exists_nontrivial_isLeviCuspidal_jacquet_arbitraryCarrier i ν standardCocharacter
      standardLeviIntersection hRoots family.connectedReductive family.maximalSplitTorus
      family.genericCocharacter family.closedUnipotent family.closedLevi π
  let := hI
  let := (family.closedLevi I).locallyCompactSpace
  let := compactSpace_leftQuotient_parabolic i ν
    BruhatTits.dynamicParabolicQuotientCompact standardCocharacter
    family.connectedReductive family.maximalSplitTorus family.genericCocharacter I
  have hfg : Module.Finite (MonoidAlgebra ℂ (rationalPoints G))
      π.representation.asModule := inferInstance
  let rI := (jacquetFunctor (family.decomposition I) (family.closedUnipotent I)).obj π
  have hrfg : Module.Finite (MonoidAlgebra ℂ (levi i ν I)) rI.representation.asModule :=
    JacquetFiniteGeneration.finite_of_compactQuotient
      (family.decomposition I) (family.closedUnipotent I) π hfg
  obtain ⟨σ, hσ, q, hq⟩ := CuspidalEmbedding.exists_irreducible_quotient_of_finite rI hrfg
  have hσc : Langlands.Aubert.General.IsLeviCuspidal
      (parabolic i ν) (levi i ν) (unipotent i ν)
      family.closedUnipotent I (family.closedLevi I) (family.leviDecomposition I) σ := by
    intro K
    let := hcusp K
    exact (CuspidalEmbedding.jacquet_map_surjective
      (family.leviDecomposition I K.val)
      ((family.closedUnipotent (leviIndex I K.val)).preimage continuous_subtype_val)
      q hq).subsingleton
  have hσn : Nontrivial σ := by
    let := hσ
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (levi i ν I)) σ.representation.asModule
  let := hσn
  obtain ⟨f, hf⟩ := CuspidalEmbedding.embedding_of_surjective_jacquet_map
    (family.decomposition I) (family.closedUnipotent I)
    (standardUnipotent_isUnimodular_of_standardCocharacterStatement
      i ν standardCocharacter family.connectedReductive family.maximalSplitTorus
      family.genericCocharacter I (family.closedUnipotent I)) π hπ σ q hq
  let e := leviRationalPointHomeomorph i ν I
  let D := SmoothRep.pullback e σ
  have hD : D.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff σ.representation e).mpr hσ
  let cancel : bernsteinLiteralLeviRep i ν I D ≅ σ :=
    SmoothRep.mkIso (equivOfRepresentationEq (by
      ext x v
      change σ.representation (e (e.symm x)) v = σ.representation x v
      rw [e.apply_symm_apply]))
  have hDc : Langlands.Aubert.General.IsLeviCuspidal
      (parabolic i ν) (levi i ν) (unipotent i ν)
      family.closedUnipotent I (family.closedLevi I) (family.leviDecomposition I)
      (bernsteinLiteralLeviRep i ν I D) := by
    intro K
    let t := (SmoothRep.equivOfIso ((jacquetFunctor (family.leviDecomposition I K.val)
      ((family.closedUnipotent (leviIndex I K.val)).preimage continuous_subtype_val)).mapIso
        cancel)).toLinearEquiv
    let := hσc K
    exact t.injective.subsingleton
  let a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family := ⟨I, D, hD, hDc⟩
  let E := (normalizedInductionFunctor (family.decomposition I)
    (family.closedUnipotent I)).mapIso cancel
  exact ⟨a, f ≫ E.inv, (SmoothRep.equivOfIso E.symm).injective.comp hf⟩

/-- A choice of actual cuspidal inducing data, retaining the actual embedding
witness at the saturated carrier universe. -/
def bernsteinCuspidalSupportPresentation
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hπ : π.IsIrreducible) :
    { a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family //
      SmoothRep.IsSubrepresentation π (bernsteinInduction i ν family a) } :=
  Classical.indefiniteDescription _
    (exists_bernsteinCuspidalDatum_induction_subrepresentation i ν family π hπ)

/-- The published actual cuspidal-support existence target holds at exactly
the universes used in the Bernstein characterization. -/
theorem bernsteinCuspidalSupportExistence :
    BernsteinCuspidalSupportExistenceStatement.{uF, uV} i ν family := by
  intro π hπ
  obtain ⟨a, ha⟩ := exists_bernsteinCuspidalDatum_induction_subrepresentation i ν family π hπ
  exact ⟨a, hπ, ha.isSubquotient⟩

end Langlands.CuspidalSupport
