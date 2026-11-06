import Langlands.Representation.CuspidalSupport.BernsteinData
import Langlands.Representation.Category.UniverseLift

/-! # Actual irreducible support and the full Bernstein block categories -/

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

local instance bernsteinBlockAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinBlockAmbientTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- Actual normalized induction of the actual cuspidal action. The induction
carrier is explicitly enlarged to `max uF uV`. -/
def bernsteinInduction (a : BernsteinCuspidalDatum.{uF, uV} i ν family) :
    SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) :=
  (normalizedInductionFunctor (family.decomposition a.roots)
    (family.closedUnipotent a.roots)).obj
      (bernsteinLiteralLeviRep i ν a.roots a.representation)

/-- An actual irreducible representation occurs in the normalized induction
of the specified actual cuspidal datum, as an actual subquotient. -/
def IsBernsteinCuspidalSupport (a : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) : Prop :=
  π.IsIrreducible ∧ SmoothRep.IsSubquotient π (bernsteinInduction i ν family a)

/-- Irreducible inertial support is existence of a datum in the specified
proved quotient class whose actual induction contains the representation. -/
def IsBernsteinInertialSupport (s : BernsteinInertialClass.{uF, uV} i ν family)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) : Prop :=
  ∃ a : BernsteinCuspidalDatum.{uF, uV} i ν family,
    bernsteinInertialClass i ν family a = s ∧ IsBernsteinCuspidalSupport i ν family a π

variable {i ν family}

/-- A raw actual support presentation supplies its own inertial class. -/
theorem IsBernsteinCuspidalSupport.inertial
    {a : BernsteinCuspidalDatum.{uF, uV} i ν family}
    {π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)}
    (h : IsBernsteinCuspidalSupport i ν family a π) :
    IsBernsteinInertialSupport i ν family (bernsteinInertialClass i ν family a) π :=
  ⟨a, rfl, h⟩

/-- Changing the actual irreducible representative by an isomorphism preserves
its actual induction-subquotient presentation. -/
theorem IsBernsteinCuspidalSupport.of_iso
    {a : BernsteinCuspidalDatum.{uF, uV} i ν family}
    {π τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)}
    (h : IsBernsteinCuspidalSupport i ν family a π) (e : π ≅ τ) :
    IsBernsteinCuspidalSupport i ν family a τ :=
  ⟨(isIrreducible_iff_of_equiv (SmoothRep.equivOfIso e)).mp h.1,
    SmoothRep.IsSubquotient.of_iso_left e h.2⟩

/-- Inertial support is invariant under an actual isomorphism. -/
theorem IsBernsteinInertialSupport.of_iso
    {s : BernsteinInertialClass.{uF, uV} i ν family}
    {π τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)}
    (h : IsBernsteinInertialSupport i ν family s π) (e : π ≅ τ) :
    IsBernsteinInertialSupport i ν family s τ := by
  obtain ⟨a, ha, hπ⟩ := h
  exact ⟨a, ha, hπ.of_iso e⟩

variable (i ν family)

/-- A class represented by `a` consists of all related data, rather than the
constituents of the induction of only that one fixed datum. -/
theorem isBernsteinInertialSupport_representative_iff
    (a : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) :
    IsBernsteinInertialSupport i ν family (bernsteinInertialClass i ν family a) π ↔
      ∃ b : BernsteinCuspidalDatum.{uF, uV} i ν family,
        IsBernsteinInertiaRelated i ν family a b ∧
          IsBernsteinCuspidalSupport i ν family b π := by
  constructor
  · rintro ⟨b, hb, hπ⟩
    exact ⟨b, (bernsteinInertialClass_eq_iff i ν family a b).mp hb.symm, hπ⟩
  · rintro ⟨b, hab, hπ⟩
    exact ⟨b, ((bernsteinInertialClass_eq_iff i ν family a b).mpr hab).symm, hπ⟩

/-- Changing the representative of an inertial class preserves the saturated
support relation, using the proved quotient equality criterion alone. -/
theorem isBernsteinInertialSupport_iff_of_related
    {a b : BernsteinCuspidalDatum.{uF, uV} i ν family}
    (h : IsBernsteinInertiaRelated i ν family a b)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) :
    IsBernsteinInertialSupport i ν family (bernsteinInertialClass i ν family a) π ↔
      IsBernsteinInertialSupport i ν family (bernsteinInertialClass i ν family b) π := by
  rw [(bernsteinInertialClass_eq_iff i ν family a b).mpr h]

/-- At the common saturated universe, all actual irreducible subquotients have
the prescribed inertial support. There is no length or admissibility premise. -/
def bernsteinSaturatedBlockProperty
    (s : BernsteinInertialClass.{uF, max uF uV} i ν family) :
    ObjectProperty (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) :=
  fun V => ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
    π.IsIrreducible → SmoothRep.IsSubquotient π V →
      IsBernsteinInertialSupport i ν family s π

/-- The full block in the common carrier universe of normalized induction. -/
abbrev BernsteinSaturatedBlock
    (s : BernsteinInertialClass.{uF, max uF uV} i ν family) :=
  (bernsteinSaturatedBlockProperty i ν family s).FullSubcategory

/-- The block property on every object in an arbitrary carrier universe `uV`.
Each irreducible actual subquotient is explicitly lifted by `ULift` to the
common universe of its support presentations. -/
def bernsteinBlockProperty
    (s : BernsteinInertialClass.{uF, max uF uV} i ν family) :
    ObjectProperty (SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) :=
  fun V => ∀ π : SmoothRep.{0, uF, uV} ℂ (rationalPoints G),
    π.IsIrreducible → SmoothRep.IsSubquotient π V →
      IsBernsteinInertialSupport i ν family s (SmoothRep.universeLift.{uF} π)

/-- Renard's full Bernstein block category on arbitrary smooth objects, with
explicit carrier enlargement only in the support comparison. -/
abbrev BernsteinBlock
    (s : BernsteinInertialClass.{uF, max uF uV} i ν family) :=
  (bernsteinBlockProperty.{uF, uV} i ν family s).FullSubcategory

variable {i ν family}

/-- At a saturated universe, lifting a carrier is an actual smooth isomorphism,
so the two block definitions agree. -/
theorem bernsteinBlockProperty_iff_saturated
    (s : BernsteinInertialClass.{uF, max uF uV} i ν family)
    (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)) :
    bernsteinBlockProperty i ν family s V ↔
      bernsteinSaturatedBlockProperty i ν family s V := by
  constructor
  · intro h π hπ hπV
    exact (h π hπ hπV).of_iso
      (SmoothRep.mkIso (SmoothRep.universeLiftEquiv.{uF} π)).symm
  · intro h π hπ hπV
    exact (h π hπ hπV).of_iso
      (SmoothRep.mkIso (SmoothRep.universeLiftEquiv.{uF} π))

variable {s : BernsteinInertialClass.{uF, max uF uV} i ν family}
  {V W : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)}

/-- The full block property is closed under actual subquotients. -/
theorem bernsteinBlockProperty_of_isSubquotient
    (hV : bernsteinBlockProperty i ν family s V) (hWV : SmoothRep.IsSubquotient W V) :
    bernsteinBlockProperty i ν family s W :=
  fun π hπ hπW => hV π hπ (smoothSubquotientTransitivity ℂ _ V W π hπW hWV)

/-- The full block property is preserved by actual isomorphisms. -/
theorem bernsteinBlockProperty_of_iso
    (hV : bernsteinBlockProperty i ν family s V) (e : W ≅ V) :
    bernsteinBlockProperty i ν family s W :=
  fun π hπ hπW => hV π hπ (hπW.of_iso_right e)

/-- The full block property is closed under extensions in the actual invariant
submodule/quotient model, without finite length. -/
theorem bernsteinBlockProperty_of_subrepresentation_quotient
    (S : Subrepresentation V.representation)
    (hS : bernsteinBlockProperty i ν family s (SmoothRep.subrepresentation V S))
    (hQ : bernsteinBlockProperty i ν family s (SmoothRep.quotient V S)) :
    bernsteinBlockProperty i ν family s V :=
  fun π hπ hπV => (SmoothRep.irreducibleSubquotient_dichotomy hπ hπV S).elim
    (hS π hπ) (hQ π hπ)

/-- Block membership is independent of the chosen cuspidal-datum representative. -/
theorem bernsteinBlockProperty_iff_of_related
    {a b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family}
    (h : IsBernsteinInertiaRelated i ν family a b) :
    bernsteinBlockProperty i ν family (bernsteinInertialClass i ν family a) V ↔
      bernsteinBlockProperty i ν family (bernsteinInertialClass i ν family b) V := by
  rw [(bernsteinInertialClass_eq_iff i ν family a b).mpr h]

variable (i ν family)

/-- Every defining induction belongs to the saturated block of its datum. -/
theorem bernsteinInduction_mem_saturatedBlock
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family) :
    bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
      (bernsteinInduction i ν family a) :=
  fun π hπ hπa => ⟨a, rfl, hπ, hπa⟩

/-- The same actual induction belongs to the full block property. -/
theorem bernsteinInduction_mem_block
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family) :
    bernsteinBlockProperty i ν family (bernsteinInertialClass i ν family a)
      (bernsteinInduction i ν family a) :=
  (bernsteinBlockProperty_iff_saturated _ _).mpr
    (bernsteinInduction_mem_saturatedBlock i ν family a)

end Langlands.CuspidalSupport
