import Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.Group.RelativeWeylAssociatedIndexing

/-! # Whole standard families in associated Levis -/

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

/-- The literal standard parabolic indexed by a finite subset of the simple
labels of `J`, restricted to the ambient standard Levi `L_J`. -/
def restrictedStandardParabolic (J : Finset (SimpleRoot i ν)) (I : Finset J) :
    SubgroupFunctor G :=
  standardLevi i ν (rootSet i ν J) ⊓
    standardParabolic i ν
      (rootSet i ν (I.map (Function.Embedding.subtype (· ∈ J))))

/-- The literal standard radical indexed by a finite subset of the simple
labels of `J`, restricted to the ambient standard Levi `L_J`. -/
def restrictedStandardUnipotent (J : Finset (SimpleRoot i ν)) (I : Finset J) :
    SubgroupFunctor G :=
  standardLevi i ν (rootSet i ν J) ⊓
    standardUnipotent i ν
      (rootSet i ν (I.map (Function.Embedding.subtype (· ∈ J))))

/-- Every lift of the specified longest representative transports every
standard parabolic and radical in its associated Levi to the corresponding
standard restriction in the target Levi, on every test scheme. -/
def IsStandardAssociatedParabolicTransport
    [Fintype (SimpleRoot i ν)] [Fintype (relativeWeylGroup i)]
    {CM : CoxeterMatrix (SimpleRoot i ν)}
    (cs : CoxeterSystem CM (relativeWeylGroup i)) : Prop :=
  ∀ (J : Finset (SimpleRoot i ν)) (n : normalizerPoints i),
    QuotientGroup.mk n = longestRep cs J →
    ∀ I : Finset (associatedSubset cs J),
      (restrictedStandardParabolic i ν (associatedSubset cs J) I =
        (restrictedStandardParabolic i ν J (associatedFinsetEquiv cs J I)).comap
          (G.innerIso (n : rationalPoints G)).hom) ∧
      (restrictedStandardUnipotent i ν (associatedSubset cs J) I =
        (restrictedStandardUnipotent i ν J (associatedFinsetEquiv cs J I)).comap
          (G.innerIso (n : rationalPoints G)).hom)

/-- The whole associated-family transport target for connected reductive
groups over every field and for every finite actual Coxeter realization.
This proposition supplies neither the realization nor the transport equalities. -/
def StandardAssociatedParabolicTransportStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∀ [Fintype (SimpleRoot i ν)] [Fintype (relativeWeylGroup i)]
        (CM : CoxeterMatrix (SimpleRoot i ν))
        (cs : CoxeterSystem CM (relativeWeylGroup i)),
        IsRelativeWeylCoxeterRealization i ν cs →
          IsStandardAssociatedParabolicTransport i ν cs

/-- Taking rational points of supplied all-test transport equalities gives
the exact inverse-conjugation images, with the same finite-subset equivalence. -/
theorem IsStandardAssociatedParabolicTransport.rationalPoints
    [Fintype (SimpleRoot i ν)] [Fintype (relativeWeylGroup i)]
    {CM : CoxeterMatrix (SimpleRoot i ν)}
    {cs : CoxeterSystem CM (relativeWeylGroup i)}
    (h : IsStandardAssociatedParabolicTransport i ν cs)
    (J : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
    (hn : QuotientGroup.mk n = longestRep cs J)
    (I : Finset (associatedSubset cs J)) :
    ((restrictedStandardParabolic i ν (associatedSubset cs J) I).rationalPoints =
      (restrictedStandardParabolic i ν J (associatedFinsetEquiv cs J I)).rationalPoints.map
        (MulAut.conj ((n : rationalPoints G)⁻¹)).toMonoidHom) ∧
    ((restrictedStandardUnipotent i ν (associatedSubset cs J) I).rationalPoints =
      (restrictedStandardUnipotent i ν J (associatedFinsetEquiv cs J I)).rationalPoints.map
        (MulAut.conj ((n : rationalPoints G)⁻¹)).toMonoidHom) := by
  obtain ⟨hP, hU⟩ := h J n hn I
  constructor
  · simpa only [SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map] using
      congrArg (fun P : SubgroupFunctor G => P.rationalPoints) hP
  · simpa only [SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map] using
      congrArg (fun U : SubgroupFunctor G => U.rationalPoints) hU

end Langlands.GroupScheme
