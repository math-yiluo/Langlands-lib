import Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # Statement: twisted intersections of actual standard Levi subgroup functors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T)

/-- For every minimum double-coset representative and every normalizer lift,
the source-side Levi intersection is the standard Levi indexed by the
intrinsic Coxeter intersection subset. The equality is on all test schemes. -/
def IsStandardLeviTwistedIntersection {CM : CoxeterMatrix (SimpleRoot i ν)}
    (cs : CoxeterSystem CM (relativeWeylGroup i)) : Prop :=
  ∀ (I J : Finset (SimpleRoot i ν)) (w : relativeWeylGroup i),
    IsMinimal cs I J w →
    ∀ n : normalizerPoints i, QuotientGroup.mk n = w →
      standardLevi i ν (rootSet i ν J) ⊓
        (standardLevi i ν (rootSet i ν I)).comap
          (G.innerIso (n : rationalPoints G)).hom =
        standardLevi i ν (rootSet i ν (intersectionSubset cs I J w))

/-- The all-field, all-test twisted standard-Levi intersection target for an
actual relative-Weyl Coxeter realization. This declaration supplies no proof. -/
def StandardLeviTwistedIntersectionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∀ (CM : CoxeterMatrix (SimpleRoot i ν))
        (cs : CoxeterSystem CM (relativeWeylGroup i)),
        IsRelativeWeylCoxeterRealization i ν cs →
          IsStandardLeviTwistedIntersection i ν cs

/-- Evaluating an all-test twisted-Levi equality at the base gives the exact
source-side subgroup equality, with inverse conjugation. -/
theorem standardLeviPoints_twistedIntersection_of_functor_eq
    (I J K : Finset (SimpleRoot i ν)) (n : rationalPoints G)
    (h : standardLevi i ν (rootSet i ν J) ⊓
      (standardLevi i ν (rootSet i ν I)).comap (G.innerIso n).hom =
        standardLevi i ν (rootSet i ν K)) :
    levi i ν J ⊓ (levi i ν I).map (MulAut.conj n⁻¹).toMonoidHom = levi i ν K := by
  have hp := congrArg (fun F : SubgroupFunctor G => F.rationalPoints) h
  change (standardLevi i ν (rootSet i ν J)).rationalPoints ⊓
    ((standardLevi i ν (rootSet i ν I)).comap (G.innerIso n).hom).rationalPoints =
      (standardLevi i ν (rootSet i ν K)).rationalPoints at hp
  rw [SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map] at hp
  exact hp

/-- A proof of the all-test intersection property gives its rational-point
formula for every lift; no section of the quotient is chosen. -/
theorem IsStandardLeviTwistedIntersection.rationalPoints
    {CM : CoxeterMatrix (SimpleRoot i ν)}
    {cs : CoxeterSystem CM (relativeWeylGroup i)}
    (h : IsStandardLeviTwistedIntersection i ν cs)
    (I J : Finset (SimpleRoot i ν)) (w : relativeWeylGroup i)
    (hw : IsMinimal cs I J w) (n : normalizerPoints i) (hn : QuotientGroup.mk n = w) :
    levi i ν J ⊓ (levi i ν I).map
        (MulAut.conj ((n : rationalPoints G)⁻¹)).toMonoidHom =
      levi i ν (intersectionSubset cs I J w) :=
  standardLeviPoints_twistedIntersection_of_functor_eq i ν I J _ n (h I J w hw n hn)

end Langlands.GroupScheme
