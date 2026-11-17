import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainIntersection
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainTopology
import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms

/-! # Finite Banach algebras and actual closed-quotient descent data -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K}

/-- The unique original bounded restriction associated to a locus containment. -/
def restriction {E D : Domain K R} (h : E.locus ⊆ D.locus) :
    BoundedAlgHom K D.algebra E.algebra :=
  (Domain.inclusionOfSubset E D h).restriction

theorem restriction_eq {E D : Domain K R} (r : E ⟶ D)
    (h : E.locus ⊆ D.locus) : restriction h = r.restriction :=
  congrArg Domain.Inclusion.restriction (Subsingleton.elim _ _)

theorem restriction_comp {E D F : Domain K R}
    (hED : E.locus ⊆ D.locus) (hDF : D.locus ⊆ F.locus) :
    (restriction hED).comp (restriction hDF) = restriction (hED.trans hDF) :=
  congrArg Domain.Inclusion.restriction
    (@Subsingleton.elim (Domain.Inclusion E F) inferInstance
      (Domain.inclusionOfSubset E D hED ≫
      Domain.inclusionOfSubset D F hDF) (Domain.inclusionOfSubset E F _))

theorem restriction_self (E : Domain K R) :
    restriction (Set.Subset.refl E.locus) = BoundedAlgHom.id K E.algebra :=
  restriction_eq (𝟙 E) _

/-- Actual finite Banach bounded maps over all original cover algebras. -/
structure LocalAlgebras (c : Domain.FiniteCover (Domain.whole K R)) where
  algebra : Fin c.size → PresentedAffinoidAlgebra K
  map : ∀ i, BoundedAlgHom K (c.obj i).algebra (algebra i)
  finite : ∀ i, (map i).IsFiniteBanach

namespace LocalAlgebras

variable {c : Domain.FiniteCover (Domain.whole K R)} (F : LocalAlgebras c)

/-- The closed-quotient base change to any actual full subdomain. -/
abbrev baseChange (i : Fin c.size) (E : Domain K R) (h : E.locus ⊆ (c.obj i).locus) :
    PresentedAffinoidAlgebra K :=
  AffinoidPushout.algebra (F.map i) (restriction h)

def localMap (i : Fin c.size) (E : Domain K R) (h : E.locus ⊆ (c.obj i).locus) :
    BoundedAlgHom K (F.algebra i) (F.baseChange i E h) :=
  AffinoidPushout.leftMap (F.map i) (restriction h)

def baseMap (i : Fin c.size) (E : Domain K R) (h : E.locus ⊆ (c.obj i).locus) :
    BoundedAlgHom K E.algebra (F.baseChange i E h) :=
  AffinoidPushout.rightMap (F.map i) (restriction h)

theorem condition (i : Fin c.size) (E : Domain K R)
    (h : E.locus ⊆ (c.obj i).locus) :
    (F.localMap i E h).comp (F.map i) =
      (F.baseMap i E h).comp (restriction h) :=
  AffinoidPushout.condition _ _

private theorem restrict_compatible (i : Fin c.size) {E D : Domain K R}
    (hED : E.locus ⊆ D.locus) (hDi : D.locus ⊆ (c.obj i).locus) :
    (F.localMap i E (hED.trans hDi)).comp (F.map i) =
      ((F.baseMap i E (hED.trans hDi)).comp (restriction hED)).comp
        (restriction hDi) := by
  rw [BoundedAlgHom.comp_assoc, restriction_comp, F.condition]

/-- The canonical bounded restriction between two original closed quotients. -/
def restrict (i : Fin c.size) {E D : Domain K R}
    (hED : E.locus ⊆ D.locus) (hDi : D.locus ⊆ (c.obj i).locus) :
    BoundedAlgHom K (F.baseChange i D hDi) (F.baseChange i E (hED.trans hDi)) :=
  AffinoidPushout.lift (F.map i) (restriction hDi) _
    (F.localMap i E _) ((F.baseMap i E _).comp (restriction hED))
    (F.restrict_compatible i hED hDi)

theorem restrict_localMap (i : Fin c.size) {E D : Domain K R}
    (hED : E.locus ⊆ D.locus) (hDi : D.locus ⊆ (c.obj i).locus) :
    (F.restrict i hED hDi).comp (F.localMap i D hDi) =
      F.localMap i E (hED.trans hDi) :=
  AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _

theorem restrict_baseMap (i : Fin c.size) {E D : Domain K R}
    (hED : E.locus ⊆ D.locus) (hDi : D.locus ⊆ (c.obj i).locus) :
    (F.restrict i hED hDi).comp (F.baseMap i D hDi) =
      (F.baseMap i E (hED.trans hDi)).comp (restriction hED) :=
  AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _

theorem restrict_self (i : Fin c.size) (E : Domain K R)
    (h : E.locus ⊆ (c.obj i).locus) :
    F.restrict i (Set.Subset.refl E.locus) h =
      BoundedAlgHom.id K (F.baseChange i E h) := by
  apply AffinoidPushout.hom_ext (F.map i) (restriction h)
  · change (F.restrict i (Set.Subset.refl E.locus) h).comp (F.localMap i E h) =
      (BoundedAlgHom.id K _).comp (F.localMap i E h)
    rw [F.restrict_localMap, BoundedAlgHom.id_comp]
  · change (F.restrict i (Set.Subset.refl E.locus) h).comp (F.baseMap i E h) =
      (BoundedAlgHom.id K _).comp (F.baseMap i E h)
    rw [F.restrict_baseMap, restriction_self, BoundedAlgHom.comp_id,
      BoundedAlgHom.id_comp]

/-- The literal intersection domain in the original base. -/
def overlap (_F : LocalAlgebras c) (i j : Fin c.size) : Domain K R :=
  (c.obj i).inter (c.obj j)

theorem overlapLeft (i j : Fin c.size) :
    (F.overlap i j).locus ⊆ (c.obj i).locus := Set.inter_subset_left

theorem overlapRight (i j : Fin c.size) :
    (F.overlap i j).locus ⊆ (c.obj j).locus := Set.inter_subset_right

theorem overlapLeft_restriction (i j : Fin c.size) :
    restriction (F.overlapLeft i j) = ((c.obj i).interLeft (c.obj j)).restriction :=
  restriction_eq _ _

theorem overlapRight_restriction (i j : Fin c.size) :
    restriction (F.overlapRight i j) = ((c.obj i).interRight (c.obj j)).restriction :=
  restriction_eq _ _

end LocalAlgebras

/-- Ordinary pairwise bounded equivalences of actual intersection base changes,
with equality on the entire intersection coefficient algebra. -/
structure PairTransitions {c : Domain.FiniteCover (Domain.whole K R)}
    (F : LocalAlgebras c) where
  equiv : ∀ i j, BoundedAlgEquiv K
    (F.baseChange i (F.overlap i j) (F.overlapLeft i j))
    (F.baseChange j (F.overlap i j) (F.overlapRight i j))
  over_base : ∀ i j, (equiv i j).toBoundedAlgHom.comp
    (F.baseMap i (F.overlap i j) (F.overlapLeft i j)) =
      F.baseMap j (F.overlap i j) (F.overlapRight i j)

namespace PairTransitions

variable {c : Domain.FiniteCover (Domain.whole K R)} {F : LocalAlgebras c}
  (t : PairTransitions F)

private theorem transition_compatible (i j : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) (hj : E.locus ⊆ (c.obj j).locus) :
    (((F.restrict j (show E.locus ⊆ (F.overlap i j).locus from
      fun _ hx => ⟨hi hx, hj hx⟩) (F.overlapRight i j)).comp
        (t.equiv i j).toBoundedAlgHom).comp
          (F.localMap i (F.overlap i j) (F.overlapLeft i j))).comp (F.map i) =
      (F.baseMap j E hj).comp (restriction hi) := by
  rw [BoundedAlgHom.comp_assoc, F.condition]
  rw [← BoundedAlgHom.comp_assoc, BoundedAlgHom.comp_assoc
    (F.restrict j _ _) (t.equiv i j).toBoundedAlgHom]
  rw [t.over_base, F.restrict_baseMap, BoundedAlgHom.comp_assoc, restriction_comp]

/-- Restrict an ordinary pair transition to any further full subdomain.
This is constructed by the pushout, rather than additional descent data. -/
def transition (i j : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) (hj : E.locus ⊆ (c.obj j).locus) :
    BoundedAlgHom K (F.baseChange i E hi) (F.baseChange j E hj) :=
  AffinoidPushout.lift (F.map i) (restriction hi) _
    (((F.restrict j (show E.locus ⊆ (F.overlap i j).locus from
      fun _ hx => ⟨hi hx, hj hx⟩) (F.overlapRight i j)).comp
        (t.equiv i j).toBoundedAlgHom).comp
          (F.localMap i (F.overlap i j) (F.overlapLeft i j)))
    (F.baseMap j E hj) (t.transition_compatible i j E hi hj)

theorem transition_localMap (i j : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) (hj : E.locus ⊆ (c.obj j).locus) :
    (t.transition i j E hi hj).comp (F.localMap i E hi) =
      ((F.restrict j (show E.locus ⊆ (F.overlap i j).locus from
        fun _ hx => ⟨hi hx, hj hx⟩) (F.overlapRight i j)).comp
          (t.equiv i j).toBoundedAlgHom).comp
            (F.localMap i (F.overlap i j) (F.overlapLeft i j)) :=
  AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _

theorem transition_baseMap (i j : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) (hj : E.locus ⊆ (c.obj j).locus) :
    (t.transition i j E hi hj).comp (F.baseMap i E hi) = F.baseMap j E hj :=
  AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _

theorem transition_overlap (i j : Fin c.size) :
    t.transition i j (F.overlap i j) (F.overlapLeft i j) (F.overlapRight i j) =
      (t.equiv i j).toBoundedAlgHom := by
  apply AffinoidPushout.hom_ext (F.map i) (restriction (F.overlapLeft i j))
  · change (t.transition i j (F.overlap i j) _ _).comp
      (F.localMap i (F.overlap i j) _) =
        (t.equiv i j).toBoundedAlgHom.comp (F.localMap i (F.overlap i j) _)
    rw [t.transition_localMap, F.restrict_self, BoundedAlgHom.id_comp]
  · change (t.transition i j (F.overlap i j) _ _).comp
      (F.baseMap i (F.overlap i j) _) =
        (t.equiv i j).toBoundedAlgHom.comp (F.baseMap i (F.overlap i j) _)
    rw [t.transition_baseMap, t.over_base]

end PairTransitions

namespace LocalAlgebras

variable {c : Domain.FiniteCover (Domain.whole K R)} (F : LocalAlgebras c)

/-- The literal repeated intersection used for the triple cocycle. -/
def triple (i j k : Fin c.size) : Domain K R :=
  (F.overlap i j).inter (c.obj k)

theorem tripleFirst (i j k : Fin c.size) :
    (F.triple i j k).locus ⊆ (c.obj i).locus := fun _ hx => hx.1.1

theorem tripleSecond (i j k : Fin c.size) :
    (F.triple i j k).locus ⊆ (c.obj j).locus := fun _ hx => hx.1.2

theorem tripleThird (i j k : Fin c.size) :
    (F.triple i j k).locus ⊆ (c.obj k).locus := fun _ hx => hx.2

end LocalAlgebras

/-- Ordinary finite affinoid algebra descent data: pairwise equivalences over
the intersection algebras, identity, and the triple cocycle on entire maps. -/
structure DescentData {c : Domain.FiniteCover (Domain.whole K R)}
    (F : LocalAlgebras c) extends PairTransitions F where
  identity : ∀ i, (equiv i i).toBoundedAlgHom = BoundedAlgHom.id K _
  cocycle : ∀ i j k,
    (toPairTransitions.transition j k (F.triple i j k)
      (F.tripleSecond i j k) (F.tripleThird i j k)).comp
        (toPairTransitions.transition i j (F.triple i j k)
          (F.tripleFirst i j k) (F.tripleSecond i j k)) =
      toPairTransitions.transition i k (F.triple i j k)
        (F.tripleFirst i j k) (F.tripleThird i j k)

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent
