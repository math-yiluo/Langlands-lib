import Langlands.Representation.CuspidalSupport.BernsteinBlockCharacterizationReduction
import Langlands.Representation.Aubert.General.RationalMinimalJacquetArbitraryCarrier
import Langlands.Representation.Aubert.General.RationalCuspidalJacquetSubquotient
import Langlands.Representation.Category.DisjointConstituentCoproduct
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.StandardLeviIntersectionProof

/-! # Actual cuspidal Jacquet data detect nonzero smooth representations -/

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

local instance bernsteinJacquetDetectionInstance1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance bernsteinJacquetDetectionInstance2 : TopologicalSpace (rationalPoints G) := pointTopology
local instance bernsteinJacquetDetectionInstance3 (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinJacquetDetectionInstance4 (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinJacquetDetectionInstance5 (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance bernsteinJacquetDetectionInstance6 (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

omit [LocallyOfFiniteType G.X.hom] in
/-- A nonzero actual smooth representation has an actual cuspidal datum in
one of its standard Jacquet modules, without increasing the carrier universe. -/
theorem exists_bernsteinCuspidalDatum_jacquet_subquotient
    (V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) [Nontrivial V] :
    ∃ b : BernsteinCuspidalDatum.{uF, uV} i ν family,
      SmoothRep.IsSubquotient (bernsteinLiteralLeviRep i ν b.roots b.representation)
        ((jacquetFunctor (family.decomposition b.roots)
          (family.closedUnipotent b.roots)).obj V) := by
  have := family.maximalSplitTorus.isSplitSubtorus.mono
  have hRoots : HasRelativeRootSystem i :=
    relativeRootSystem F G family.connectedReductive T i family.maximalSplitTorus
  obtain ⟨I, hI, hcusp⟩ :=
    exists_nontrivial_isLeviCuspidal_jacquet_arbitraryCarrier i ν standardCocharacter
      standardLeviIntersection hRoots family.connectedReductive family.maximalSplitTorus
      family.genericCocharacter family.closedUnipotent family.closedLevi V
  let := hI
  obtain ⟨σ, hσ, hσJ⟩ := SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial
    ((jacquetFunctor (family.decomposition I) (family.closedUnipotent I)).obj V)
  have hσc : Langlands.Aubert.General.IsLeviCuspidal
      (parabolic i ν) (levi i ν) (unipotent i ν)
      family.closedUnipotent I (family.closedLevi I) (family.leviDecomposition I) σ :=
    Langlands.Aubert.General.IsLeviCuspidal.of_isSubquotient (fun K =>
      isLimitOfCompactSubgroups_subgroupOf _ _ (family.closedLevi I)
        (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
          i ν standardCocharacter family.connectedReductive family.maximalSplitTorus
          family.genericCocharacter (leviIndex I K))) hcusp hσJ
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
    let := (family.closedLevi I).locallyCompactSpace
    intro K
    let t := (SmoothRep.equivOfIso ((jacquetFunctor (family.leviDecomposition I K.val)
      ((family.closedUnipotent (leviIndex I K.val)).preimage continuous_subtype_val)).mapIso
        cancel)).toLinearEquiv
    let := hσc K
    exact t.injective.subsingleton
  exact ⟨⟨I, D, hD, hDc⟩, hσJ.of_iso_left cancel.symm⟩

/-- Choose a genuine Bernstein datum detected in a nonzero object's Jacquet
module, retaining the actual occurrence witness. -/
def bernsteinNonzeroJacquetDatum
    (V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) [Nontrivial V] :
    { b : BernsteinCuspidalDatum.{uF, uV} i ν family //
      SmoothRep.IsSubquotient (bernsteinLiteralLeviRep i ν b.roots b.representation)
        ((jacquetFunctor (family.decomposition b.roots)
          (family.closedUnipotent b.roots)).obj V) } :=
  Classical.indefiniteDescription _
    (exists_bernsteinCuspidalDatum_jacquet_subquotient i ν family V)

omit [LocallyOfFiniteType G.X.hom] in
/-- Actual cuspidal data in standard Jacquet modules jointly detect zero,
at the original independent carrier universe. -/
theorem subsingleton_iff_no_bernsteinCuspidalDatum_jacquet_subquotient
    (V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) :
    Subsingleton V ↔
      ∀ b : BernsteinCuspidalDatum.{uF, uV} i ν family,
        ¬ SmoothRep.IsSubquotient (bernsteinLiteralLeviRep i ν b.roots b.representation)
          ((jacquetFunctor (family.decomposition b.roots)
            (family.closedUnipotent b.roots)).obj V) := by
  constructor
  · intro hV b hb
    let := hV
    have hJ : Subsingleton ((jacquetFunctor (family.decomposition b.roots)
        (family.closedUnipotent b.roots)).obj V) :=
      (Jacquet.Localization.mk_surjective V.representation (unipotent i ν b.roots) 1).subsingleton
    let := hJ
    obtain ⟨B, j, q, hj, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hb
    have : Subsingleton B := hj.subsingleton
    have : Subsingleton b.representation := hq.subsingleton
    let := b.irreducible
    exact (bot_ne_top : (⊥ : Subrepresentation b.representation.representation) ≠ ⊤)
      (Subrepresentation.ext (Subsingleton.elim _ _))
  · intro h
    rcases subsingleton_or_nontrivial V with hV | hV
    · exact hV
    · let := hV
      obtain ⟨b, hb⟩ := exists_bernsteinCuspidalDatum_jacquet_subquotient i ν family V
      exact False.elim (h b hb)

/-- An object satisfying condition (iii) for two distinct actual inertial
classes has zero carrier. No support comparison is assumed. -/
theorem subsingleton_of_bernsteinJacquetExclusion_of_not_inertiaRelated
    (a b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (hab : ¬ IsBernsteinInertiaRelated i ν family a b)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hVa : BernsteinJacquetExclusion i ν family a V)
    (hVb : BernsteinJacquetExclusion i ν family b V) :
    Subsingleton V := by
  classical
  apply (subsingleton_iff_no_bernsteinCuspidalDatum_jacquet_subquotient i ν family V).mpr
  intro c hc
  have hac : IsBernsteinInertiaRelated i ν family a c := by
    by_contra hac
    exact hVa c hac hc
  have hbc : IsBernsteinInertiaRelated i ν family b c := by
    by_contra hbc
    exact hVb c hbc hc
  exact hab (hac.trans hbc.symm)

/-- Objects in distinct condition-(iii) classes have no common irreducible
actual subquotient. -/
theorem no_common_irreducibleSubquotient_of_bernsteinJacquetExclusion
    (a b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (hab : ¬ IsBernsteinInertiaRelated i ν family a b)
    {V W : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)}
    (hV : BernsteinJacquetExclusion i ν family a V)
    (hW : BernsteinJacquetExclusion i ν family b W)
    (D : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hD : D.IsIrreducible)
    (hDV : SmoothRep.IsSubquotient D V) (hDW : SmoothRep.IsSubquotient D W) :
    False := by
  have := subsingleton_of_bernsteinJacquetExclusion_of_not_inertiaRelated i ν family a b hab D
    (bernsteinJacquetExclusion_of_isSubquotient i ν family a hV hDV)
    (bernsteinJacquetExclusion_of_isSubquotient i ν family b hW hDW)
  let := hD
  exact (bot_ne_top : (⊥ : Subrepresentation D.representation) ≠ ⊤)
    (Subrepresentation.ext (Subsingleton.elim _ _))

/-- Every morphism between objects in distinct condition-(iii) classes
vanishes, without any finite-length or decomposition premise. -/
theorem hom_eq_zero_of_bernsteinJacquetExclusion_of_not_inertiaRelated
    (a b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (hab : ¬ IsBernsteinInertiaRelated i ν family a b)
    {V W : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)}
    (hV : BernsteinJacquetExclusion i ν family a V)
    (hW : BernsteinJacquetExclusion i ν family b W) (f : V ⟶ W) :
    f = 0 :=
  SmoothRep.hom_eq_zero_of_no_common_irreducibleSubquotient
    (no_common_irreducibleSubquotient_of_bernsteinJacquetExclusion
      i ν family a b hab hV hW) f

end Langlands.CuspidalSupport
