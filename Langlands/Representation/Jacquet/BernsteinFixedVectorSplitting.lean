import Langlands.Representation.Jacquet.FixedVectorComponentSplitting
import Langlands.Representation.CuspidalSupport.BernsteinDecompositionStatements
import Langlands.Representation.Category.FixedVectorConstituent
import Langlands.Representation.Smooth.FixedVectors.DetectionConsequencesProof

/-! # The fixed-level comparison needed for Bernstein fixed-vector splitting -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open Langlands.CuspidalSupport
open Langlands.Aubert.General.RationalPointFamily
open scoped CategoryTheory.MonObj

universe uF uV

namespace Langlands.Jacquet

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinFixedVectorAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinFixedVectorTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν) (K : OpenSubgroup (rationalPoints G))

/-- At a specified level, having a nonzero fixed vector is constant among
irreducibles with the same actual inertial support. This property is an input;
no assertion is made that it holds for an arbitrary compact open subgroup. -/
def bernsteinFixedVectorVisibility : Prop :=
  ∀ (s : BernsteinInertialClass.{uF,max uF uV} i ν family)
    (π τ : SmoothRep.{0,uF,max uF uV} ℂ (rationalPoints G)),
    IsBernsteinInertialSupport i ν family s π →
    IsBernsteinInertialSupport i ν family s τ →
      (Nontrivial (fixedVectors π.representation K.toSubgroup) ↔
        Nontrivial (fixedVectors τ.representation K.toSubgroup))

/-- Uniform fixed vectors among irreducibles of one inertial class imply the
generated/zero-fixed dichotomy for every actual object of that block. -/
theorem bernsteinBlock_fixedVector_dichotomy
    (hK : IsCompact (K : Set (rationalPoints G)))
    (hvisibility : bernsteinFixedVectorVisibility.{uF,uV} i ν family K)
    (s : BernsteinInertialClass.{uF,max uF uV} i ν family)
    (V : SmoothRep.{0,uF,uV} ℂ (rationalPoints G))
    (hV : bernsteinBlockProperty i ν family s V) :
    fixedVectorGenerated K.toSubgroup V ∨
      fixedVectors V.representation K.toSubgroup = ⊥ := by
  classical
  by_cases hzero : fixedVectors V.representation K.toSubgroup = ⊥
  · exact Or.inr hzero
  · left
    have hfix : Nontrivial (fixedVectors V.representation K.toSubgroup) :=
      Submodule.nontrivial_iff_ne_bot.mpr hzero
    obtain ⟨D, hD, hDV, hDfix⟩ :=
      SmoothRep.hasFixedVectorConstituent_of_nontrivial V K.toSubgroup hfix
    have hdet (E : SmoothRep.{0,uF,uV} ℂ (rationalPoints G))
        (hE : E.IsIrreducible) (hEV : SmoothRep.IsSubquotient E V) :
        ∃ v : E, v ∈ fixedVectors E.representation K.toSubgroup ∧ v ≠ 0 := by
      have hDlift : Nontrivial (fixedVectors
          (SmoothRep.universeLift.{uF} D).representation K.toSubgroup) :=
        (fixedVectorsEquiv (SmoothRep.universeLiftEquiv.{uF} D)
          K.toSubgroup).toEquiv.nontrivial_congr.mp hDfix
      have hElift := (hvisibility s (SmoothRep.universeLift.{uF} D)
        (SmoothRep.universeLift.{uF} E) (hV D hD hDV) (hV E hE hEV)).mp hDlift
      have hEfix : Nontrivial (fixedVectors E.representation K.toSubgroup) :=
        (fixedVectorsEquiv (SmoothRep.universeLiftEquiv.{uF} E)
          K.toSubgroup).toEquiv.nontrivial_congr.mpr hElift
      let := hEfix
      obtain ⟨v, hv⟩ := exists_ne (0 : fixedVectors E.representation K.toSubgroup)
      exact ⟨v.val, v.property, fun hz => hv (Subtype.ext hz)⟩
    exact (compactOpenDetectionConsequences (rationalPoints G) V K hK hdet).2.1 V
      (SmoothRep.IsQuotient.isSubquotient ⟨𝟙 V, Function.surjective_id⟩)

/-- The actual Bernstein component presentation and its explicit irreducible
fixed-level comparison give the splitting used in the smooth-duality proof. -/
theorem fixedVectorSplitting_of_bernstein
    (hK : IsCompact (K : Set (rationalPoints G)))
    (hdec : Renard.EveryObjectIsCoproductOfComponents
      (fun s : BernsteinInertialClass.{uF,max uF uV} i ν family =>
        bernsteinBlockProperty.{uF,uV} i ν family s))
    (hvisibility : bernsteinFixedVectorVisibility.{uF,uV} i ν family K) :
    fixedVectorSplitting.{uF,uV} K :=
  fixedVectorSplitting_of_components K _ hdec
    (bernsteinBlock_fixedVector_dichotomy i ν family K hK hvisibility)

/-- The published global decomposition statement discharges the coproduct
premise; the actual fixed-level comparison remains explicit. -/
theorem fixedVectorSplitting_of_bernsteinDecomposition
    (hBernstein : BernsteinDecompositionStatement.{uF,uV})
    (hK : IsCompact (K : Set (rationalPoints G)))
    (hvisibility : bernsteinFixedVectorVisibility.{uF,uV} i ν family K) :
    fixedVectorSplitting.{uF,uV} K :=
  fixedVectorSplitting_of_bernstein i ν family K hK
    (hBernstein F G T i ν family).1 hvisibility

end Langlands.Jacquet
