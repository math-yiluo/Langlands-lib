import Langlands.Representation.CuspidalSupport.StandardLeviInertialClass
import Langlands.Representation.Aubert.General.RationalInductionStagesGeometry
import Langlands.GroupScheme.Rational.StandardLeviIntersectionProof

/-! # Induction-defined inertial support and its fixed-vector locus inside a standard Levi -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : TopologicalSpace (rationalPoints G) := pointTopology
local instance (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance (I : Finset (SimpleRoot i ν)) : IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν) {J : Finset (SimpleRoot i ν)}

/-- Normalized induction of a nested cuspidal datum inside `M_J(F)`, on the
actual Levi subgroup via the canonical comparison for the inducing action. -/
def standardLeviCuspidalInduction (a : StandardLeviCuspidalDatum.{uF, uV} i ν family J) :
    SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J) := by
  classical
  let I : Finset J := a.val.roots.subtype (· ∈ J)
  have hI : leviIndex J I = a.val.roots := Finset.subtype_map_of_mem a.property
  exact (leviNormalizedInductionFunctor (family.closedLevi J)
    (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
      family.maximalSplitTorus family.genericCocharacter a.val.roots J a.property)
    (hI ▸ family.leviDecomposition J I) (family.closedUnipotent a.val.roots)).obj
    (bernsteinLiteralLeviRep i ν a.val.roots a.val.representation)

/-- The actual induction can be written with any internal label mapping to the
root label of the datum. This is proof irrelevance for the structural inputs. -/
theorem standardLeviCuspidalInduction_eq_of_leviIndex_eq
    (a : StandardLeviCuspidalDatum.{uF, uV} i ν family J)
    (I : Finset J) (hI : leviIndex J I = a.val.roots) :
    standardLeviCuspidalInduction i ν family a =
      (leviNormalizedInductionFunctor (family.closedLevi J)
        (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
          family.maximalSplitTorus family.genericCocharacter a.val.roots J
          (hI ▸ leviIndex_subset J I))
        (hI ▸ family.leviDecomposition J I) (family.closedUnipotent a.val.roots)).obj
        (bernsteinLiteralLeviRep i ν a.val.roots a.val.representation) := rfl

/-- The irreducible representation `τ` occurs in the actual normalized
induction of this particular datum inside `M_J`. -/
def IsStandardLeviCuspidalSupport (a : StandardLeviCuspidalDatum.{uF, uV} i ν family J)
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)) : Prop :=
  τ.IsIrreducible ∧ SmoothRep.IsSubquotient τ (standardLeviCuspidalInduction i ν family a)

variable [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]

/-- The irreducible representation has an induction presentation by some
representative of the specified `M_J`-inertial class. -/
def IsStandardLeviInertialSupport (s : StandardLeviInertialClass.{uF, uV} i ν family J)
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)) : Prop :=
  ∃ a : StandardLeviCuspidalDatum.{uF, uV} i ν family J,
    standardLeviInertialClass i ν family a = s ∧ IsStandardLeviCuspidalSupport i ν family a τ

/-- Renard's `B(M_J)_{K_M}`: an actual subset of the nested inertial quotient. -/
def standardLeviFixedVectorSupportSet (J : Finset (SimpleRoot i ν)) (K_M : Subgroup (levi i ν J)) :
    Set (StandardLeviInertialClass.{uF, uV} i ν family J) :=
  {s | ∃ τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J),
    IsStandardLeviInertialSupport i ν family s τ ∧ Nontrivial (fixedVectors τ.representation K_M)}

end Langlands.CuspidalSupport
