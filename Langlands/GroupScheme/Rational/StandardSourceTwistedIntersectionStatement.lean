import Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # Standard source parabolics and radicals of minimum geometric terms -/

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

/-- The source parabolic and radical at a minimum double-coset representative
are the literal standard restrictions inside `L_J`, on every test scheme. -/
def IsStandardSourceTwistedIntersection {CM : CoxeterMatrix (SimpleRoot i ν)}
    (cs : CoxeterSystem CM (relativeWeylGroup i)) : Prop :=
  ∀ (I J : Finset (SimpleRoot i ν)) (w : relativeWeylGroup i),
    IsMinimal cs I J w →
    ∀ n : normalizerPoints i, QuotientGroup.mk n = w →
      (standardLevi i ν (rootSet i ν J) ⊓
        (standardParabolic i ν (rootSet i ν I)).comap
          (G.innerIso (n : rationalPoints G)).hom =
        standardLevi i ν (rootSet i ν J) ⊓
          standardParabolic i ν (rootSet i ν (intersectionSubset cs I J w))) ∧
      (standardLevi i ν (rootSet i ν J) ⊓
        (standardUnipotent i ν (rootSet i ν I)).comap
          (G.innerIso (n : rationalPoints G)).hom =
        standardLevi i ν (rootSet i ν J) ⊓
          standardUnipotent i ν (rootSet i ν (intersectionSubset cs I J w)))

/-- The all-field, all-test source-parabolic and source-radical standardness
target. This definition supplies neither equality. -/
def StandardSourceTwistedIntersectionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∀ (CM : CoxeterMatrix (SimpleRoot i ν))
        (cs : CoxeterSystem CM (relativeWeylGroup i)),
        IsRelativeWeylCoxeterRealization i ν cs →
          IsStandardSourceTwistedIntersection i ν cs

/-- Evaluate supplied all-test source equalities at the base field. The
preimage under `Int(n)` has the inverse-conjugation orientation. -/
theorem standardSourcePoints_twistedIntersection_of_functor_eq
    (I J K : Finset (SimpleRoot i ν)) (n : rationalPoints G)
    (hP : standardLevi i ν (rootSet i ν J) ⊓
      (standardParabolic i ν (rootSet i ν I)).comap (G.innerIso n).hom =
        standardLevi i ν (rootSet i ν J) ⊓ standardParabolic i ν (rootSet i ν K))
    (hU : standardLevi i ν (rootSet i ν J) ⊓
      (standardUnipotent i ν (rootSet i ν I)).comap (G.innerIso n).hom =
        standardLevi i ν (rootSet i ν J) ⊓ standardUnipotent i ν (rootSet i ν K)) :
    (levi i ν J ⊓ (parabolic i ν I).map (MulAut.conj n⁻¹).toMonoidHom =
      levi i ν J ⊓ parabolic i ν K) ∧
    (levi i ν J ⊓ (unipotent i ν I).map (MulAut.conj n⁻¹).toMonoidHom =
      levi i ν J ⊓ unipotent i ν K) := by
  constructor
  · have hp := congrArg (fun F : SubgroupFunctor G => F.rationalPoints) hP
    change (standardLevi i ν (rootSet i ν J)).rationalPoints ⊓
      ((standardParabolic i ν (rootSet i ν I)).comap (G.innerIso n).hom).rationalPoints =
        (standardLevi i ν (rootSet i ν J)).rationalPoints ⊓
          (standardParabolic i ν (rootSet i ν K)).rationalPoints at hp
    rw [SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map] at hp
    exact hp
  · have hu := congrArg (fun F : SubgroupFunctor G => F.rationalPoints) hU
    change (standardLevi i ν (rootSet i ν J)).rationalPoints ⊓
      ((standardUnipotent i ν (rootSet i ν I)).comap (G.innerIso n).hom).rationalPoints =
        (standardLevi i ν (rootSet i ν J)).rationalPoints ⊓
          (standardUnipotent i ν (rootSet i ν K)).rationalPoints at hu
    rw [SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map] at hu
    exact hu

/-- A supplied source-standardness property gives the exact parabolic and
radical subgroups inside `L_J`, for every lift covered by that property. -/
theorem IsStandardSourceTwistedIntersection.subgroupOf
    {CM : CoxeterMatrix (SimpleRoot i ν)}
    {cs : CoxeterSystem CM (relativeWeylGroup i)}
    (h : IsStandardSourceTwistedIntersection i ν cs)
    (I J : Finset (SimpleRoot i ν)) (w : relativeWeylGroup i)
    (hw : IsMinimal cs I J w) (n : normalizerPoints i) (hn : QuotientGroup.mk n = w) :
    ((levi i ν J ⊓ (parabolic i ν I).map
        (MulAut.conj ((n : rationalPoints G)⁻¹)).toMonoidHom).subgroupOf (levi i ν J) =
      (parabolic i ν (intersectionSubset cs I J w)).subgroupOf (levi i ν J)) ∧
    ((levi i ν J ⊓ (unipotent i ν I).map
        (MulAut.conj ((n : rationalPoints G)⁻¹)).toMonoidHom).subgroupOf (levi i ν J) =
      (unipotent i ν (intersectionSubset cs I J w)).subgroupOf (levi i ν J)) := by
  obtain ⟨hP, hU⟩ := h I J w hw n hn
  obtain ⟨hp, hu⟩ :=
    standardSourcePoints_twistedIntersection_of_functor_eq i ν I J _ n hP hU
  exact ⟨by simpa only [Subgroup.inf_subgroupOf_left] using
      congrArg (fun H => H.subgroupOf (levi i ν J)) hp,
    by simpa only [Subgroup.inf_subgroupOf_left] using
      congrArg (fun H => H.subgroupOf (levi i ν J)) hu⟩

end Langlands.GroupScheme
