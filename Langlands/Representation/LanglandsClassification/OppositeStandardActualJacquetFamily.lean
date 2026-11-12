import Langlands.Representation.LanglandsClassification.StandardActualJacquetFamily
import Langlands.Representation.LanglandsClassification.OppositeLeviParabolic

/-! # Actual opposite Jacquet spectra over all standard Levis

At each actual simple-root subset, take the opposite of the original standard
parabolic with the same Levi scheme, ambient Levi map and chosen split component.
The full subset supplies nonemptiness, and the finite actual-spectrum selector
chooses a maximal value of any supplied norm map.
-/

noncomputable section

universe u v z

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic.OppositeStandardJacquetFamily

open GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

/-- Opposite data for the original standard parabolic, retaining its Levi
scheme and its ambient Levi map exactly. -/
def opposite (J : StandardJacquetFamily.Index i ν) :
    OppositeLeviParabolicData (StandardJacquetFamily.datum i ν hG hi hν J).p
      (StandardJacquetFamily.datum i ν hG hi hν J).l :=
  oppositeLeviParabolic hG
    (StandardJacquetFamily.datum i ν hG hi hν J).p
    (StandardJacquetFamily.datum i ν hG hi hν J).l
    (StandardJacquetFamily.datum i ν hG hi hν J).hp
    (StandardJacquetFamily.datum i ν hG hi hν J).hl

/-- Actual opposite parabolic data with the original standard Levi, for use
in the normalized Jacquet-exponent interface. -/
def datum (J : StandardJacquetFamily.Index i ν) : ParabolicDatum G where
  P := (opposite i ν hG hi hν J).parabolic
  M := (StandardJacquetFamily.datum i ν hG hi hν J).M
  U := (opposite i ν hG hi hν J).radical
  p := (opposite i ν hG hi hν J).inclusion
  l := (opposite i ν hG hi hν J).levi
  r := (opposite i ν hG hi hν J).unipotent
  hp := (opposite i ν hG hi hν J).isParabolic
  hl := (opposite i ν hG hi hν J).isLevi
  hr := (opposite i ν hG hi hν J).isRadical
  hmul := (opposite i ν hG hi hν J).multiplication

/-- The opposite datum has the same standard Levi scheme. -/
@[simp] theorem datum_M (J : StandardJacquetFamily.Index i ν) :
    (datum i ν hG hi hν J).M = Standard.leviScheme i ν J.val := rfl

/-- Its ambient Levi map is the original canonical standard map. -/
@[simp] theorem datum_l_comp_p (J : StandardJacquetFamily.Index i ν) :
    (datum i ν hG hi hν J).l ≫ (datum i ν hG hi hν J).p =
      Standard.leviHom i ν J.val := by
  exact (opposite i ν hG hi hν J).levi_comp.trans
    (Standard.leviToParabolic_comp i ν J.val)

/-- The standard and opposite parabolic point images intersect in precisely
the common standard Levi point image. -/
theorem intersection (J : StandardJacquetFamily.Index i ν) :
    pointImage (StandardJacquetFamily.datum i ν hG hi hν J).p ⊓
        pointImage (datum i ν hG hi hν J).p =
      pointImage (Standard.leviHom i ν J.val) := by
  simpa only [datum, StandardJacquetFamily.datum, ParabolicDatum.standard,
    Standard.leviToParabolic_comp] using
    (opposite i ν hG hi hν J).intersection

/-- Reuse precisely the split component and torus factor already chosen for
the standard Levi; the opposite family makes no new component choice. -/
abbrev component (J : StandardJacquetFamily.Index i ν) :
    StandardJacquetFamily.Component i ν J :=
  StandardJacquetFamily.component i ν hG hi hν J

/-- At the full label the original Levi fills the ambient group, so the
opposite inclusion also has full all-test range and is an isomorphism. -/
theorem isIso_full_p :
    IsIso (datum i ν hG hi hν (StandardJacquetFamily.full i ν)).p := by
  let D := StandardJacquetFamily.datum i ν hG hi hν (StandardJacquetFamily.full i ν)
  let O := opposite i ν hG hi hν (StandardJacquetFamily.full i ν)
  have : IsIso D.p := ParabolicDatum.isIso_standard_full_p i ν hG hi hν
  have : IsIso D.l := D.hl.isIso_of_isIso_parabolic (p := D.p) hG
  have hle := SubgroupFunctor.range_comp_le O.levi O.inclusion
  rw [O.levi_comp, full_range_of_isIso (D.l ≫ D.p)] at hle
  have := O.isParabolic.isClosedSubgroup.mono
  exact isIso_of_full_range O.inclusion (Over.mono_of_mono_left _)
    (SubgroupFunctor.ext fun V => top_le_iff.mp (hle V))

variable [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]

local instance oppositeStandardAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

/-- Actual normalized exponents for the opposites of all standard parabolics,
with the original subset label and chosen standard split-component character. -/
def exponents : Type u :=
  taggedActualJacquetExponents (datum i ν hG hi hν)
    (fun J => (component i ν hG hi hν J).A)
    (fun J => (component i ν hG hi hν J).a)
    (fun J => (component i ν hG hi hν J).ha) π

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The opposite full-label Jacquet module is nonzero for any nonzero
representation, by the actual full-parabolic Jacquet equivalence. -/
theorem nontrivial_full_jacquet (hπ : Nontrivial π) :
    Nontrivial
      ((jacquetFunctor (datum i ν hG hi hν (StandardJacquetFamily.full i ν)).p
        (datum i ν hG hi hν (StandardJacquetFamily.full i ν)).l
        (datum i ν hG hi hν (StandardJacquetFamily.full i ν)).r
        (datum i ν hG hi hν (StandardJacquetFamily.full i ν)).hp
        (datum i ν hG hi hν (StandardJacquetFamily.full i ν)).hr
        (datum i ν hG hi hν (StandardJacquetFamily.full i ν)).hl
        (datum i ν hG hi hν (StandardJacquetFamily.full i ν)).hmul).obj π) := by
  have := hπ
  let D := datum i ν hG hi hν (StandardJacquetFamily.full i ν)
  have : IsIso D.p := isIso_full_p i ν hG hi hν
  let := leviPointTopology D.l D.hl
  exact (fullParabolicLeviJacquetEquiv D.p D.l D.hp D.hl hG D.r D.hr D.hmul
    π).toLinearEquiv.toEquiv.nontrivial

/-- Admissibility and finite length make all tagged opposite exponents finite. -/
theorem finite_exponents (hadm : π.IsAdmissible) (hfl : π.HasFiniteLength) :
    Finite (exponents i ν hG hi hν π) := by
  have := StandardJacquetFamily.finite_index i ν hG hi
  exact finite_taggedActualJacquetExponents _ _ _ _ π hG hadm hfl

/-- The opposite family is nonempty for a nonzero admissible representation. -/
theorem nonempty_exponents (hadm : π.IsAdmissible) (hπ : Nontrivial π) :
    Nonempty (exponents i ν hG hi hν π) := by
  exact (nonempty_taggedActualJacquetExponents_iff _ _ _ _ π hG hadm).mpr
    ⟨StandardJacquetFamily.full i ν, nontrivial_full_jacquet i ν hG hi hν π hπ⟩

variable (hadm : π.IsAdmissible) (hfl : π.HasFiniteLength) (hπ : Nontrivial π)
  {E : Type z} [NormedAddCommGroup E]
  (positive : exponents i ν hG hi hν π → E)

/-- Select an actual opposite exponent maximizing the norm of a supplied map. -/
def maximalExponent : exponents i ν hG hi hν π := by
  have := StandardJacquetFamily.finite_index i ν hG hi
  exact maximalActualJacquetExponent _ _ _ _ π hG hadm hfl
    ⟨StandardJacquetFamily.full i ν, nontrivial_full_jacquet i ν hG hi hν π hπ⟩ positive

/-- Every tagged actual opposite exponent satisfies the selected norm bound. -/
theorem norm_le_maximalExponent (x : exponents i ν hG hi hν π) :
    ‖positive x‖ ≤
      ‖positive (maximalExponent i ν hG hi hν π hadm hfl hπ positive)‖ := by
  have := StandardJacquetFamily.finite_index i ν hG hi
  exact norm_le_maximalActualJacquetExponent _ _ _ _ π hG hadm hfl
    ⟨StandardJacquetFamily.full i ν, nontrivial_full_jacquet i ν hG hi hν π hπ⟩ positive x

end Langlands.Aubert.General.RepresentedParabolic.OppositeStandardJacquetFamily
