import Langlands.Representation.CuspidalSupport.BernsteinData

/-! # The map on Bernstein inertial classes from a standard Levi -/

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

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : TopologicalSpace (rationalPoints G) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- Standard cuspidal data of `M_J`, written in the ambient standard root labels. -/
abbrev StandardLeviCuspidalDatum (J : Finset (SimpleRoot i ν)) :=
  {a : BernsteinCuspidalDatum.{uF, uV} i ν family // a.roots ⊆ J}

local instance (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance (I : Finset (SimpleRoot i ν)) : IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyOfFiniteType G.X.hom]

local instance (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance

/-- Inertia inside `M_J`: the ambient algebraic conjugacy must be given by a
point of `M_J(F)`. The twist is a full unramified character of the inducing Levi. -/
def IsStandardLeviInertiaRelated {J : Finset (SimpleRoot i ν)}
    (a b : StandardLeviCuspidalDatum.{uF, uV} i ν family J) : Prop :=
  ∃ c : RationalLeviConjugacy
      (Standard.leviHom i ν (rootSet i ν a.val.roots))
      (Standard.leviHom i ν (rootSet i ν b.val.roots)),
    c.point ∈ levi i ν J ∧
    IsRationalInertiaRelated (bernsteinLeviScheme i ν a.val.roots)
      a.val.representation (rationalIsoPullback c.iso b.val.representation)

namespace IsStandardLeviInertiaRelated

variable {i ν family} {J : Finset (SimpleRoot i ν)}
  {a b d : StandardLeviCuspidalDatum.{uF, uV} i ν family J}

theorem refl (a : StandardLeviCuspidalDatum.{uF, uV} i ν family J) :
    IsStandardLeviInertiaRelated i ν family a a :=
  ⟨RationalLeviConjugacy.refl _, (levi i ν J).one_mem,
    IsRationalInertiaRelated.of_iso (rationalIsoPullbackReflIso a.val.representation).symm⟩

theorem symm (h : IsStandardLeviInertiaRelated i ν family a b) :
    IsStandardLeviInertiaRelated i ν family b a := by
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c.symm, (levi i ν J).inv_mem hc,
    ((rationalInertiaRelated_pullback_iff c.iso _ _).mp h).symm⟩

theorem trans (hab : IsStandardLeviInertiaRelated i ν family a b)
    (hbd : IsStandardLeviInertiaRelated i ν family b d) :
    IsStandardLeviInertiaRelated i ν family a d := by
  obtain ⟨c, hc, hab⟩ := hab
  obtain ⟨e, he, hbd⟩ := hbd
  exact ⟨c.trans e, (levi i ν J).mul_mem he hc,
    (hab.trans (hbd.rationalIsoPullback c.iso)).trans
      (IsRationalInertiaRelated.of_iso
        (rationalIsoPullbackTransIso c.iso e.iso d.val.representation))⟩

/-- Forgetting that the conjugating point lies in `M_J(F)` gives ambient inertia. -/
theorem toAmbient (h : IsStandardLeviInertiaRelated i ν family a b) :
    IsBernsteinInertiaRelated i ν family a.val b.val := by
  obtain ⟨c, _, h⟩ := h
  exact ⟨c, h⟩

end IsStandardLeviInertiaRelated

/-- The equivalence relation for standard cuspidal data inside `M_J`. -/
def standardLeviInertiaSetoid (J : Finset (SimpleRoot i ν)) :
    Setoid (StandardLeviCuspidalDatum.{uF, uV} i ν family J) where
  r := IsStandardLeviInertiaRelated i ν family
  iseqv := ⟨fun a => .refl a, fun h => h.symm, fun h h' => h.trans h'⟩

/-- Renard's `B(M_J)` in the nested standard-family presentation. -/
def StandardLeviInertialClass (J : Finset (SimpleRoot i ν)) :=
  Quotient (standardLeviInertiaSetoid.{uF, uV} i ν family J)

/-- The `M_J`-inertial class of a nested standard datum. -/
def standardLeviInertialClass {J : Finset (SimpleRoot i ν)}
    (a : StandardLeviCuspidalDatum.{uF, uV} i ν family J) :
    StandardLeviInertialClass.{uF, uV} i ν family J :=
  Quotient.mk _ a

theorem standardLeviInertialClass_eq_iff {J : Finset (SimpleRoot i ν)}
    (a b : StandardLeviCuspidalDatum.{uF, uV} i ν family J) :
    standardLeviInertialClass i ν family a = standardLeviInertialClass i ν family b ↔
      IsStandardLeviInertiaRelated i ν family a b :=
  Quotient.eq

/-- Renard VI.7.3: `i_{M_J G}` on inertial classes sends the class of `(L, σ)`
inside `M_J` to the class of the same datum in `G`. -/
def standardLeviInertialToAmbient (J : Finset (SimpleRoot i ν)) :
    StandardLeviInertialClass.{uF, uV} i ν family J →
      BernsteinInertialClass.{uF, uV} i ν family :=
  Quotient.lift (fun a => bernsteinInertialClass i ν family a.val) (fun a b h =>
    (bernsteinInertialClass_eq_iff i ν family a.val b.val).mpr
      (IsStandardLeviInertiaRelated.toAmbient h))

@[simp] theorem standardLeviInertialToAmbient_class {J : Finset (SimpleRoot i ν)}
    (a : StandardLeviCuspidalDatum.{uF, uV} i ν family J) :
    standardLeviInertialToAmbient i ν family J (standardLeviInertialClass i ν family a) =
      bernsteinInertialClass i ν family a.val := rfl

end Langlands.CuspidalSupport
