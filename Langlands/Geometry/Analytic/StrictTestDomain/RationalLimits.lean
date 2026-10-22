import Langlands.Geometry.Analytic.StrictTestDomain.RationalCategory
import Langlands.Geometry.Analytic.RationalIntersection
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-! # Explicit terminal object and pullbacks of rational inclusions -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalData

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}

omit [CompleteSpace K] in
private theorem hom_unique {d e : RationalData K P} (f g : d ⟶ e) : f = g :=
  (inferInstance : Subsingleton (Inclusion d e)).elim f g

/-- The empty numerator tuple with denominator one presents the whole locus. -/
def whole (K : Type u) [NormedField K] [IsUltrametricDist K]
    (P : PresentedStrictAffinoidAlgebra K) : RationalData K P where
  arity := 0
  denominator := 1
  numerator := Fin.elim0
  no_common_zero x := Or.inl (by
    rw [map_one]
    exact one_ne_zero)

omit [CompleteSpace K] in
@[simp]
theorem locus_whole : (whole K P).locus = Set.univ := by
  ext x
  simp [locus, RationalLocalization.locus, whole]

/-- Every rational locus is included in the whole spectrum. -/
def toWhole (d : RationalData K P) : d ⟶ whole K P :=
  ⟨by rw [locus_whole]; exact Set.subset_univ _⟩

/-- The explicit whole-spectrum presentation is terminal in the inclusion category. -/
def wholeIsTerminal : IsTerminal (whole K P) :=
  IsTerminal.ofUniqueHom (fun d => d.toWhole) (fun _ _ => hom_unique _ _)

/-- Product denominator and pairwise extended numerator products give chosen
rational input for an intersection; no output domain is assumed. -/
def inter (d e : RationalData K P) : RationalData K P where
  arity := (d.arity + 1) * (e.arity + 1)
  denominator := d.denominator * e.denominator
  numerator := RationalIntersection.numerators K P d.arity e.arity
    d.denominator e.denominator d.numerator e.numerator
  no_common_zero :=
    (RationalFactorization.generatesUnitIdeal_iff_no_common_zero _ _ _ _ _).mp
      (RationalIntersection.generatesUnitIdeal _ _ _ _ _ _ _ _
        d.generatesUnitIdeal e.generatesUnitIdeal)

@[simp]
theorem locus_inter (d e : RationalData K P) :
    (d.inter e).locus = d.locus ∩ e.locus :=
  RationalIntersection.locus_eq_inter _ _ _ _ _ _ _ _
    d.generatesUnitIdeal e.generatesUnitIdeal

/-- The first intersection inclusion. -/
def interLeft (d e : RationalData K P) : d.inter e ⟶ d :=
  ⟨by rw [locus_inter]; exact Set.inter_subset_left⟩

/-- The second intersection inclusion. -/
def interRight (d e : RationalData K P) : d.inter e ⟶ e :=
  ⟨by rw [locus_inter]; exact Set.inter_subset_right⟩

/-- Simultaneous inclusion in two rational loci gives inclusion in their
explicit intersection presentation. -/
def interLift {c d e : RationalData K P} (f : c ⟶ d) (g : c ⟶ e) :
    c ⟶ d.inter e :=
  ⟨by rw [locus_inter]; exact fun _ hx => ⟨f.subset hx, g.subset hx⟩⟩

/-- The chosen intersection is a cone over any two inclusions into one locus. -/
def pullbackCone {d e t : RationalData K P} (f : d ⟶ t) (g : e ⟶ t) :
    PullbackCone f g :=
  PullbackCone.mk (interLeft d e) (interRight d e) (hom_unique _ _)

/-- The explicit intersection cone satisfies the categorical pullback
universal property in the rational inclusion category. -/
def pullbackConeIsLimit {d e t : RationalData K P} (f : d ⟶ t) (g : e ⟶ t) :
    IsLimit (pullbackCone f g) :=
  PullbackCone.IsLimit.mk _ (fun s => interLift s.fst s.snd)
    (fun _ => hom_unique _ _) (fun _ => hom_unique _ _)
    (fun _ _ _ _ => hom_unique _ _)

/-- The bounded map induced by the first inclusion is the original
intersection construction's left restriction. -/
theorem interLeft_restriction (d e : RationalData K P) :
    (interLeft d e).restriction =
      RationalIntersection.leftMap K P d.arity e.arity d.denominator e.denominator
        d.numerator e.numerator d.generatesUnitIdeal e.generatesUnitIdeal :=
  ((interLeft d e).restriction_unique
    (RationalIntersection.leftMap_comp_baseMap _ _ _ _ _ _ _ _ _ _)).symm

/-- The bounded map induced by the second inclusion is the original
intersection construction's right restriction. -/
theorem interRight_restriction (d e : RationalData K P) :
    (interRight d e).restriction =
      RationalIntersection.rightMap K P d.arity e.arity d.denominator e.denominator
        d.numerator e.numerator d.generatesUnitIdeal e.generatesUnitIdeal :=
  ((interRight d e).restriction_unique
    (RationalIntersection.rightMap_comp_baseMap _ _ _ _ _ _ _ _ _ _)).symm

end Langlands.Analytic.StrictTestDomain.RationalData
