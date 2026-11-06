import Langlands.Representation.CuspidalSupport.RationalConjugateInertia
import Langlands.Representation.Aubert.General.RationalLeviNormTopology
import Langlands.Representation.Aubert.General.SupportCategory

/-! # Actual standard cuspidal data and their inertial quotient -/

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
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinAmbientTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- An actual finite standard family. These are structural hypotheses on the
published subgroups, without any representation-theoretic decomposition input. -/
structure BernsteinStandardFamily : Prop where
  connectedReductive : IsConnectedReductive G
  maximalSplitTorus : IsMaximalSplitTorus i
  genericCocharacter : IsGenericCocharacter i ν
  finiteSimpleRoots : Finite (SimpleRoot i ν)
  decomposition : ∀ I, IsSemidirectDecomposition
    (parabolic i ν I) (levi i ν I) (unipotent i ν I)
  closedUnipotent : ∀ I, IsClosed (unipotent i ν I : Set (rationalPoints G))
  closedLevi : ∀ I, IsClosed (levi i ν I : Set (rationalPoints G))
  leviDecomposition : ∀ (J : Finset (SimpleRoot i ν)) (I : Finset J),
    IsSemidirectDecomposition ((parabolic i ν (leviIndex J I)).subgroupOf (levi i ν J))
      ((levi i ν (leviIndex J I)).subgroupOf (levi i ν J))
      ((unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J))

variable (family : BernsteinStandardFamily i ν)

/-- The Levi here is the represented standard subgroup scheme itself. -/
abbrev bernsteinLeviScheme (I : Finset (SimpleRoot i ν)) :=
  Standard.leviScheme i ν (rootSet i ν I)

local instance bernsteinLeviClosedImmersion (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinLeviTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

/-- An action on the scheme's rational points, transported to the literal
standard subgroup by the inverse canonical homeomorphism, on the same carrier. -/
abbrev bernsteinLiteralLeviRep (I : Finset (SimpleRoot i ν))
    (ρ : SmoothRep.{0, uF, uV} ℂ (rationalPoints (bernsteinLeviScheme i ν I))) :
    SmoothRep.{0, uF, uV} ℂ (levi i ν I) :=
  SmoothRep.pullback (leviRationalPointHomeomorph i ν I).symm ρ

/-- An actual standard Levi with an actual smooth irreducible cuspidal action.
Cuspidality is the published normalized-Jacquet vanishing predicate. -/
structure BernsteinCuspidalDatum where
  roots : Finset (SimpleRoot i ν)
  representation : SmoothRep.{0, uF, uV} ℂ
    (rationalPoints (bernsteinLeviScheme i ν roots))
  irreducible : representation.IsIrreducible
  cuspidal : Langlands.Aubert.General.IsLeviCuspidal
    (parabolic i ν) (levi i ν) (unipotent i ν) family.closedUnipotent
    roots (family.closedLevi roots) (family.leviDecomposition roots)
    (bernsteinLiteralLeviRep i ν roots representation)

include family in
/-- Connected reductivity supplies the finite-type hypothesis used by twists. -/
theorem BernsteinStandardFamily.locallyOfFiniteType : LocallyOfFiniteType G.X.hom := by
  have := family.connectedReductive.smooth
  infer_instance

variable [LocallyOfFiniteType G.X.hom]
local instance bernsteinLeviFiniteType (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance

/-- Source-side formulation of actual inertia: algebraic conjugacy of the
embedded Levis and full rational unramified twisting of the actual action. -/
def IsBernsteinInertiaRelated
    (a b : BernsteinCuspidalDatum.{uF, uV} i ν family) : Prop :=
  ∃ c : RationalLeviConjugacy
    (Standard.leviHom i ν (rootSet i ν a.roots))
    (Standard.leviHom i ν (rootSet i ν b.roots)),
    IsRationalInertiaRelated (bernsteinLeviScheme i ν a.roots)
      a.representation (rationalIsoPullback c.iso b.representation)

/-- This is exactly the target-side formulation in Renard VI.7.1:
`ρ₂` is isomorphic to a full unramified twist of the conjugated `ρ₁`. -/
theorem isBernsteinInertiaRelated_iff
    (a b : BernsteinCuspidalDatum.{uF, uV} i ν family) :
    IsBernsteinInertiaRelated i ν family a b ↔
      ∃ c : RationalLeviConjugacy
        (Standard.leviHom i ν (rootSet i ν a.roots))
        (Standard.leviHom i ν (rootSet i ν b.roots)),
        IsRationalInertiaRelated (bernsteinLeviScheme i ν b.roots)
          (rationalIsoPullback c.iso.symm a.representation) b.representation := by
  constructor
  · rintro ⟨c, h⟩
    exact ⟨c, (rationalInertiaRelated_pullback_iff c.iso _ _).mp h⟩
  · rintro ⟨c, h⟩
    exact ⟨c, (rationalInertiaRelated_pullback_iff c.iso _ _).mpr h⟩

variable {i ν family}

/-- The trivial character and identity conjugation prove reflexivity. -/
theorem IsBernsteinInertiaRelated.refl
    (a : BernsteinCuspidalDatum.{uF, uV} i ν family) :
    IsBernsteinInertiaRelated i ν family a a :=
  ⟨RationalLeviConjugacy.refl _,
    IsRationalInertiaRelated.of_iso (rationalIsoPullbackReflIso a.representation).symm⟩

/-- Inverse conjugation and inverse full character prove symmetry. -/
theorem IsBernsteinInertiaRelated.symm
    {a b : BernsteinCuspidalDatum.{uF, uV} i ν family}
    (h : IsBernsteinInertiaRelated i ν family a b) :
    IsBernsteinInertiaRelated i ν family b a := by
  obtain ⟨c, h⟩ := h
  exact ⟨c.symm, ((rationalInertiaRelated_pullback_iff c.iso _ _).mp h).symm⟩

/-- Compose actual conjugating points, algebraic isomorphisms and twists. -/
theorem IsBernsteinInertiaRelated.trans
    {a b d : BernsteinCuspidalDatum.{uF, uV} i ν family}
    (hab : IsBernsteinInertiaRelated i ν family a b)
    (hbd : IsBernsteinInertiaRelated i ν family b d) :
    IsBernsteinInertiaRelated i ν family a d := by
  obtain ⟨c, hab⟩ := hab
  obtain ⟨e, hbd⟩ := hbd
  exact ⟨c.trans e, (hab.trans (hbd.rationalIsoPullback c.iso)).trans
    (IsRationalInertiaRelated.of_iso
      (rationalIsoPullbackTransIso c.iso e.iso d.representation))⟩

variable (i ν family)

/-- The proved equivalence relation on actual standard cuspidal data. -/
def bernsteinInertiaSetoid : Setoid (BernsteinCuspidalDatum.{uF, uV} i ν family) where
  r := IsBernsteinInertiaRelated i ν family
  iseqv := ⟨fun a => .refl a, fun h => h.symm, fun h h' => h.trans h'⟩

/-- Bernstein inertial classes, at an independent representation-carrier universe. -/
def BernsteinInertialClass := Quotient (bernsteinInertiaSetoid.{uF, uV} i ν family)

/-- The class of an actual cuspidal datum. -/
def bernsteinInertialClass (a : BernsteinCuspidalDatum.{uF, uV} i ν family) :
    BernsteinInertialClass.{uF, uV} i ν family :=
  Quotient.mk _ a

/-- Representative equality is exactly actual conjugacy and unramified twisting. -/
theorem bernsteinInertialClass_eq_iff
    (a b : BernsteinCuspidalDatum.{uF, uV} i ν family) :
    bernsteinInertialClass i ν family a = bernsteinInertialClass i ν family b ↔
      IsBernsteinInertiaRelated i ν family a b :=
  Quotient.eq

end Langlands.CuspidalSupport
