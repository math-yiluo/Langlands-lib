import Langlands.Representation.CuspidalSupport.BernsteinBlock

/-! # Retained actual cuspidal-support comparison targets -/

noncomputable section

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

local instance bernsteinComparisonAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinComparisonAmbientTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance bernsteinComparisonLeviClosedImmersion (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinComparisonLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinComparisonLeviFiniteType (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance bernsteinComparisonLeviTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- Untwisted association uses actual ambient algebraic conjugation and an
actual equivariant isomorphism, with no unramified twist. -/
def AreBernsteinCuspidalDataAssociated
    (a b : BernsteinCuspidalDatum.{uF, uV} i ν family) : Prop :=
  ∃ c : RationalLeviConjugacy
    (Standard.leviHom i ν (rootSet i ν a.roots))
    (Standard.leviHom i ν (rootSet i ν b.roots)),
    Nonempty (a.representation ≅ rationalIsoPullback c.iso b.representation)

/-- Every irreducible has an actual cuspidal induction-subquotient presentation.
This is a target, not an assumption on the data, quotient or blocks. -/
def BernsteinCuspidalSupportExistenceStatement : Prop :=
  ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
    π.IsIrreducible →
      ∃ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
        IsBernsteinCuspidalSupport i ν family a π

/-- A common irreducible constituent of two actual cuspidal inductions implies
actual untwisted association of their data (Renard VI.5.4). -/
def BernsteinCuspidalSupportAssociationStatement : Prop :=
  ∀ (a b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)),
    IsBernsteinCuspidalSupport i ν family a π →
    IsBernsteinCuspidalSupport i ν family b π →
      AreBernsteinCuspidalDataAssociated i ν family a b

/-- Actual untwisted association preserves the irreducible constituents of the
two normalized inductions (Renard VI.5.4). This says nothing about arbitrary
unramified twists of a fixed inducing datum. -/
def BernsteinAssociatedSupportInvarianceStatement : Prop :=
  ∀ (a b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family),
    AreBernsteinCuspidalDataAssociated i ν family a b →
      ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
        IsBernsteinCuspidalSupport i ν family a π ↔
          IsBernsteinCuspidalSupport i ν family b π

/-- Uniqueness of the actual inertial support relation, without choosing a
support map or assuming a partition of irreducibles. -/
def BernsteinInertialSupportUniquenessStatement : Prop :=
  ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (s t : BernsteinInertialClass.{uF, max uF uV} i ν family),
    IsBernsteinInertialSupport i ν family s π →
    IsBernsteinInertialSupport i ν family t π → s = t

/-- The actual normalized-Jacquet constituent relation for a specified datum.
The representation and its Jacquet module share the saturated carrier universe. -/
def IsBernsteinJacquetCuspidalSupport
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) : Prop :=
  π.IsIrreducible ∧
    SmoothRep.IsSubquotient (bernsteinLiteralLeviRep i ν a.roots a.representation)
      ((jacquetFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj π)

/-- Jacquet-defined inertial support ranges over all actual representatives of
the same quotient class, without selecting one. -/
def IsBernsteinJacquetInertialSupport
    (s : BernsteinInertialClass.{uF, max uF uV} i ν family)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) : Prop :=
  ∃ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
    bernsteinInertialClass i ν family a = s ∧
      IsBernsteinJacquetCuspidalSupport i ν family a π

/-- Exact remaining comparison of induction-defined and Jacquet-defined
inertial support, at the class level (Renard VI.5.4 and VI.7.1). -/
def BernsteinInductionJacquetSupportComparisonStatement : Prop :=
  ∀ (s : BernsteinInertialClass.{uF, max uF uV} i ν family)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)),
    IsBernsteinInertialSupport i ν family s π ↔
      IsBernsteinJacquetInertialSupport i ν family s π

variable {i ν family}

/-- Untwisted association implies inertial equivalence through the trivial
unramified character. No support comparison is needed for this implication. -/
theorem AreBernsteinCuspidalDataAssociated.inertia
    {a b : BernsteinCuspidalDatum.{uF, uV} i ν family}
    (h : AreBernsteinCuspidalDataAssociated i ν family a b) :
    IsBernsteinInertiaRelated i ν family a b := by
  obtain ⟨c, ⟨e⟩⟩ := h
  exact ⟨c, IsRationalInertiaRelated.of_iso e⟩

/-- The association target implies the weaker uniqueness target by the proved
quotient criterion. The source association theorem remains an explicit premise. -/
theorem bernsteinInertialSupportUniqueness_of_association
    (h : BernsteinCuspidalSupportAssociationStatement.{uF, uV} i ν family) :
    BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family := by
  intro π s t hs ht
  obtain ⟨a, ha, hπa⟩ := hs
  obtain ⟨b, hb, hπb⟩ := ht
  exact ha.symm.trans
    (((bernsteinInertialClass_eq_iff i ν family a b).mpr
      (h a b π hπa hπb).inertia).trans hb)

/-- Conditional unique existence makes the remaining source inputs explicit;
it supplies no unconditional support function or decomposition instance. -/
theorem bernsteinInertialSupport_existsUnique_of_comparisons
    (hex : BernsteinCuspidalSupportExistenceStatement.{uF, uV} i ν family)
    (hunique : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) (hπ : π.IsIrreducible) :
    ∃! s : BernsteinInertialClass.{uF, max uF uV} i ν family,
      IsBernsteinInertialSupport i ν family s π := by
  obtain ⟨a, ha⟩ := hex π hπ
  exact ⟨bernsteinInertialClass i ν family a, ha.inertial,
    fun t ht => hunique π t _ ht ha.inertial⟩

end Langlands.CuspidalSupport
