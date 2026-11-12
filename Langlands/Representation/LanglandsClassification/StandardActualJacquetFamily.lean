import Langlands.Representation.LanglandsClassification.StandardParabolicDatum
import Langlands.Representation.LanglandsClassification.MaximalActualJacquetExponent
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Mathlib.Data.Set.Finite.Powerset

/-! # A finite nonempty family of actual standard Jacquet exponents

The labels are all subsets of the actual simple relative roots. At every label
we choose a split component of the canonical standard Levi, retaining its
factorization through the given maximal split torus. The full label witnesses
nonemptiness for a nonzero admissible representation.
-/

noncomputable section

universe u v z

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic.StandardJacquetFamily

open GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The actual standard labels, including both the empty and full subsets. -/
def Index : Type u :=
  {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν}

/-- The full simple-root subset is an actual standard label. -/
def full : Index i ν := ⟨simpleRelativeRoots i ν, Set.Subset.rfl⟩

/-- A split component of the original standard Levi, with its actual map into
the fixed maximal split torus and the required ambient factorization. -/
structure Component (J : Index i ν) where
  A : CommGroupScheme (Spec (CommRingCat.of k))
  a : A.toGrp ⟶ Standard.leviScheme i ν J.val
  g : A.toGrp ⟶ T.toGrp
  ha : IsSplitComponent a
  factor : g ≫ i = a ≫ Standard.leviHom i ν J.val

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hG hi in
/-- Finiteness follows from the actual Lie-weight support and finite powersets,
without a supplied abstract root-system realization. -/
theorem finite_index : Finite (Index i ν) := by
  have := hG.smooth
  exact (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).powerset.to_subtype

/-- The canonical standard parabolic data at an actual standard label. -/
abbrev datum (J : Index i ν) : ParabolicDatum G :=
  ParabolicDatum.standard i ν hG hi hν J.val J.property

/-- Choose an actual split component at each standard label. Its factorization
through the fixed torus is retained in the returned data. -/
def component (J : Index i ν) : Component i ν J := Classical.choice (by
  have := hi.isSplitSubtorus.mono
  obtain ⟨A, a, g, ha, hg⟩ :=
    (standardLeviSplitComponentStatement k G hG T i hi ν hν J.val J.property).2
  exact ⟨⟨A, a, g, ha, hg⟩⟩)

variable [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]

local instance standardFamilyAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

/-- Actual standard Jacquet exponents, each retaining its original subset label
and its character on the chosen split component of that standard Levi. -/
def exponents : Type u :=
  taggedActualJacquetExponents (datum i ν hG hi hν)
    (fun J => (component i ν hG hi hν J).A)
    (fun J => (component i ν hG hi hν J).a)
    (fun J => (component i ν hG hi hν J).ha) π

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- For a nonzero representation the full standard label has nonzero Jacquet
module, via the actual full-parabolic Jacquet equivalence. -/
theorem nontrivial_full_jacquet (hπ : Nontrivial π) :
    Nontrivial
      ((jacquetFunctor (datum i ν hG hi hν (full i ν)).p
        (datum i ν hG hi hν (full i ν)).l (datum i ν hG hi hν (full i ν)).r
        (datum i ν hG hi hν (full i ν)).hp (datum i ν hG hi hν (full i ν)).hr
        (datum i ν hG hi hν (full i ν)).hl
        (datum i ν hG hi hν (full i ν)).hmul).obj π) := by
  have := hπ
  let D := datum i ν hG hi hν (full i ν)
  have : IsIso D.p := ParabolicDatum.isIso_standard_full_p i ν hG hi hν
  let := leviPointTopology D.l D.hl
  exact (fullParabolicLeviJacquetEquiv D.p D.l D.hp D.hl hG D.r D.hr D.hmul
    π).toLinearEquiv.toEquiv.nontrivial

/-- Admissibility and finite length give a finite family over all actual
standard labels. -/
theorem finite_exponents (hadm : π.IsAdmissible) (hfl : π.HasFiniteLength) :
    Finite (exponents i ν hG hi hν π) := by
  have := finite_index i ν hG hi
  exact finite_taggedActualJacquetExponents _ _ _ _ π hG hadm hfl

/-- The full actual standard label makes the family nonempty for a nonzero
admissible representation; finite length is unnecessary here. -/
theorem nonempty_exponents (hadm : π.IsAdmissible) (hπ : Nontrivial π) :
    Nonempty (exponents i ν hG hi hν π) := by
  exact (nonempty_taggedActualJacquetExponents_iff _ _ _ _ π hG hadm).mpr
    ⟨full i ν, nontrivial_full_jacquet i ν hG hi hν π hπ⟩

variable (hadm : π.IsAdmissible) (hfl : π.HasFiniteLength) (hπ : Nontrivial π)
  {E : Type z} [NormedAddCommGroup E]
  (positive : exponents i ν hG hi hν π → E)

/-- Select a maximal-norm supplied positive part among all actual standard
Jacquet exponents, with no supplied family-nonemptiness premise. -/
def maximalExponent : exponents i ν hG hi hν π := by
  have := finite_index i ν hG hi
  exact maximalActualJacquetExponent _ _ _ _ π hG hadm hfl
    ⟨full i ν, nontrivial_full_jacquet i ν hG hi hν π hπ⟩ positive

/-- Every actual standard exponent has supplied positive-part norm bounded by
the selected one. -/
theorem norm_le_maximalExponent (x : exponents i ν hG hi hν π) :
    ‖positive x‖ ≤
      ‖positive (maximalExponent i ν hG hi hν π hadm hfl hπ positive)‖ := by
  have := finite_index i ν hG hi
  exact norm_le_maximalActualJacquetExponent _ _ _ _ π hG hadm hfl
    ⟨full i ν, nontrivial_full_jacquet i ν hG hi hν π hπ⟩ positive x

end Langlands.Aubert.General.RepresentedParabolic.StandardJacquetFamily
