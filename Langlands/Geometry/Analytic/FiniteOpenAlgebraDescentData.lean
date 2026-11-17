import Langlands.Geometry.Analytic.FiniteOpenBaseChangeRestriction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.LocalData
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Proof

/-! # Actual finite algebra descent data for finite-open pullbacks -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FiniteOpenBaseChangeModels

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas
open FiniteAffinoidAlgebraDescent

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  {f : StrongHom A.saturatedPresentation C.saturatedPresentation}
  {g : StrongHom B.saturatedPresentation C.saturatedPresentation}
  {V : Set A.space} {U : Set C.space} {R : B.atlas.saturatedAtlas.RecognizedSubset}
  (M : FiniteOpenBaseChangeModels f g V U R)

/-- The unchanged finite local algebras supply the exact general effective
descent input, with finite Banachness proved by finite bounded base change. -/
abbrev descentLocalAlgebras : LocalAlgebras M.rightCover.cover where
  algebra := M.algebra
  map := M.rightMap
  finite i := M.rightMap_isFiniteBanach i AffinoidPushout.finiteBanachPushout

/-- The precise canonical base changes of the general descent interface
are compared with our direct local pushouts on the same actual domain. -/
def descentBaseChangeEquiv (i : Fin M.rightCover.cover.size) (E : Domain K R.algebra)
    (hi : E.locus ⊆ (M.rightCover.cover.obj i).locus) :
    BoundedAlgEquiv K (M.descentLocalAlgebras.baseChange i E hi)
      (M.restrictedAlgebra i (Domain.inclusionOfSubset E _ hi)) :=
  M.baseChangeEquiv i (Domain.inclusionOfSubset E _ hi)

theorem descentBaseChangeEquiv_comp_baseMap (i : Fin M.rightCover.cover.size)
    (E : Domain K R.algebra) (hi : E.locus ⊆ (M.rightCover.cover.obj i).locus) :
    (M.descentBaseChangeEquiv i E hi).toBoundedAlgHom.comp
      (M.descentLocalAlgebras.baseMap i E hi) =
        M.restrictedRightMap i (Domain.inclusionOfSubset E _ hi) :=
  M.baseChangeEquiv_comp_right i _

theorem descentBaseChangeEquiv_comp_localMap_left (i : Fin M.rightCover.cover.size)
    (E : Domain K R.algebra) (hi : E.locus ⊆ (M.rightCover.cover.obj i).locus) :
    ((M.descentBaseChangeEquiv i E hi).toBoundedAlgHom.comp
      (M.descentLocalAlgebras.localMap i E hi)).comp (M.leftMap i) =
        M.restrictedLeftMap i (Domain.inclusionOfSubset E _ hi) := by
  rw [BoundedAlgHom.comp_assoc]
  exact M.baseChangeEquiv_comp_left i _

theorem descentBaseChangeEquiv_comp_localMap_right (i : Fin M.rightCover.cover.size)
    (E : Domain K R.algebra) (hi : E.locus ⊆ (M.rightCover.cover.obj i).locus) :
    ((M.descentBaseChangeEquiv i E hi).toBoundedAlgHom.comp
      (M.descentLocalAlgebras.localMap i E hi)).comp (M.rightMap i) =
        (M.restrictedRightMap i (Domain.inclusionOfSubset E _ hi)).comp (restriction hi) := by
  change ((M.descentBaseChangeEquiv i E hi).toBoundedAlgHom.comp
      (M.descentLocalAlgebras.localMap i E hi)).comp (M.descentLocalAlgebras.map i) = _
  rw [BoundedAlgHom.comp_assoc, M.descentLocalAlgebras.condition,
    ← BoundedAlgHom.comp_assoc, M.descentBaseChangeEquiv_comp_baseMap]

/-- Pasting comparisons commute with the exact canonical restrictions
used by general finite algebra descent. -/
theorem descentBaseChangeEquiv_restrict (i : Fin M.rightCover.cover.size)
    {E D : Domain K R.algebra} (hED : E.locus ⊆ D.locus)
    (hDi : D.locus ⊆ (M.rightCover.cover.obj i).locus) :
    (M.descentBaseChangeEquiv i E (hED.trans hDi)).toBoundedAlgHom.comp
      (M.descentLocalAlgebras.restrict i hED hDi) =
        (M.restrictionMap i (Domain.inclusionOfSubset D _ hDi)
          (Domain.inclusionOfSubset E _ (hED.trans hDi))
          (Domain.inclusionOfSubset E D hED)).comp
            (M.descentBaseChangeEquiv i D hDi).toBoundedAlgHom := by
  let r := Domain.inclusionOfSubset D (M.rightCover.cover.obj i) hDi
  let s := Domain.inclusionOfSubset E (M.rightCover.cover.obj i) (hED.trans hDi)
  let q := Domain.inclusionOfSubset E D hED
  let ρ := M.restrictionMap i r s q
  let eD := M.descentBaseChangeEquiv i D hDi
  let eE := M.descentBaseChangeEquiv i E (hED.trans hDi)
  apply AffinoidPushout.hom_ext (M.rightMap i) (restriction hDi)
  · change (eE.toBoundedAlgHom.comp (M.descentLocalAlgebras.restrict i hED hDi)).comp
        (M.descentLocalAlgebras.localMap i D hDi) =
      (ρ.comp eD.toBoundedAlgHom).comp (M.descentLocalAlgebras.localMap i D hDi)
    rw [BoundedAlgHom.comp_assoc, M.descentLocalAlgebras.restrict_localMap,
      BoundedAlgHom.comp_assoc]
    apply AffinoidPushout.hom_ext (M.leftBase i) (M.rightCover.canonicalPullback i)
    · change (eE.toBoundedAlgHom.comp (M.descentLocalAlgebras.localMap i E _)).comp (M.leftMap i) =
        (ρ.comp (eD.toBoundedAlgHom.comp (M.descentLocalAlgebras.localMap i D hDi))).comp (M.leftMap i)
      calc
        _ = M.restrictedLeftMap i s :=
          M.descentBaseChangeEquiv_comp_localMap_left i E (hED.trans hDi)
        _ = ρ.comp (M.restrictedLeftMap i r) := (M.restrictionMap_comp_left i r s q).symm
        _ = ρ.comp ((eD.toBoundedAlgHom.comp (M.descentLocalAlgebras.localMap i D hDi)).comp
            (M.leftMap i)) := congrArg (fun z => ρ.comp z)
              (M.descentBaseChangeEquiv_comp_localMap_left i D hDi).symm
        _ = _ := (BoundedAlgHom.comp_assoc _ _ _).symm
    · change (eE.toBoundedAlgHom.comp (M.descentLocalAlgebras.localMap i E _)).comp (M.rightMap i) =
        (ρ.comp (eD.toBoundedAlgHom.comp (M.descentLocalAlgebras.localMap i D hDi))).comp (M.rightMap i)
      calc
        _ = (M.restrictedRightMap i s).comp (restriction (hED.trans hDi)) :=
          M.descentBaseChangeEquiv_comp_localMap_right i E (hED.trans hDi)
        _ = (M.restrictedRightMap i s).comp ((restriction hED).comp (restriction hDi)) :=
          congrArg (fun z => (M.restrictedRightMap i s).comp z) (restriction_comp hED hDi).symm
        _ = ((M.restrictedRightMap i s).comp q.restriction).comp (restriction hDi) := rfl
        _ = (ρ.comp (M.restrictedRightMap i r)).comp (restriction hDi) :=
          congrArg (fun z => z.comp (restriction hDi)) (M.restrictionMap_comp_right i r s q).symm
        _ = ρ.comp ((M.restrictedRightMap i r).comp (restriction hDi)) := rfl
        _ = ρ.comp ((eD.toBoundedAlgHom.comp (M.descentLocalAlgebras.localMap i D hDi)).comp
            (M.rightMap i)) := congrArg (fun z => ρ.comp z)
              (M.descentBaseChangeEquiv_comp_localMap_right i D hDi).symm
        _ = _ := rfl
  · change (eE.toBoundedAlgHom.comp (M.descentLocalAlgebras.restrict i hED hDi)).comp
        (M.descentLocalAlgebras.baseMap i D hDi) =
      (ρ.comp eD.toBoundedAlgHom).comp (M.descentLocalAlgebras.baseMap i D hDi)
    rw [BoundedAlgHom.comp_assoc, M.descentLocalAlgebras.restrict_baseMap,
      ← BoundedAlgHom.comp_assoc]
    calc
      _ = (M.restrictedRightMap i s).comp (restriction hED) :=
        congrArg (fun z => z.comp (restriction hED))
          (M.descentBaseChangeEquiv_comp_baseMap i E (hED.trans hDi))
      _ = ρ.comp (M.restrictedRightMap i r) := (M.restrictionMap_comp_right i r s q).symm
      _ = ρ.comp (eD.toBoundedAlgHom.comp (M.descentLocalAlgebras.baseMap i D hDi)) :=
        congrArg (fun z => ρ.comp z) (M.descentBaseChangeEquiv_comp_baseMap i D hDi).symm
      _ = _ := rfl

/-- Transport the whole arbitrary-domain transition through actual
bounded pushout-pasting equivalences to the general descent quotients. -/
def descentTransitionEquiv (i j : Fin M.rightCover.cover.size) (E : Domain K R.algebra)
    (hi : E.locus ⊆ (M.rightCover.cover.obj i).locus)
    (hj : E.locus ⊆ (M.rightCover.cover.obj j).locus) :
    BoundedAlgEquiv K (M.descentLocalAlgebras.baseChange i E hi)
      (M.descentLocalAlgebras.baseChange j E hj) :=
  ((M.descentBaseChangeEquiv i E hi).trans
    (M.transitionEquiv j i (Domain.inclusionOfSubset E _ hj) (Domain.inclusionOfSubset E _ hi))).trans
      (M.descentBaseChangeEquiv j E hj).symm

theorem descentTransitionEquiv_comp_baseMap (i j : Fin M.rightCover.cover.size)
    (E : Domain K R.algebra)
    (hi : E.locus ⊆ (M.rightCover.cover.obj i).locus)
    (hj : E.locus ⊆ (M.rightCover.cover.obj j).locus) :
    (M.descentTransitionEquiv i j E hi hj).toBoundedAlgHom.comp
      (M.descentLocalAlgebras.baseMap i E hi) = M.descentLocalAlgebras.baseMap j E hj := by
  change ((M.descentBaseChangeEquiv j E hj).symm.toBoundedAlgHom.comp
    ((M.transitionMap j i (Domain.inclusionOfSubset E _ hj) (Domain.inclusionOfSubset E _ hi)).comp
      (M.descentBaseChangeEquiv i E hi).toBoundedAlgHom)).comp
        (M.descentLocalAlgebras.baseMap i E hi) = _
  rw [BoundedAlgHom.comp_assoc, BoundedAlgHom.comp_assoc,
    M.descentBaseChangeEquiv_comp_baseMap, M.transitionMap_comp_right]
  exact M.baseChangeEquiv_symm_comp_right j _

theorem descentTransitionEquiv_self (i : Fin M.rightCover.cover.size)
    (E : Domain K R.algebra) (hi : E.locus ⊆ (M.rightCover.cover.obj i).locus) :
    (M.descentTransitionEquiv i i E hi hi).toBoundedAlgHom =
      BoundedAlgHom.id K (M.descentLocalAlgebras.baseChange i E hi) := by
  apply BoundedAlgHom.ext
  intro x
  change (M.descentBaseChangeEquiv i E hi).symm
    ((M.transitionMap i i (Domain.inclusionOfSubset E _ hi) (Domain.inclusionOfSubset E _ hi))
      ((M.descentBaseChangeEquiv i E hi) x)) = x
  rw [M.transitionMap_self]
  exact (M.descentBaseChangeEquiv i E hi).symm_apply_apply x

theorem descentTransitionEquiv_comp (i j k : Fin M.rightCover.cover.size)
    (E : Domain K R.algebra)
    (hi : E.locus ⊆ (M.rightCover.cover.obj i).locus)
    (hj : E.locus ⊆ (M.rightCover.cover.obj j).locus)
    (hk : E.locus ⊆ (M.rightCover.cover.obj k).locus) :
    (M.descentTransitionEquiv j k E hj hk).toBoundedAlgHom.comp
      (M.descentTransitionEquiv i j E hi hj).toBoundedAlgHom =
        (M.descentTransitionEquiv i k E hi hk).toBoundedAlgHom := by
  apply BoundedAlgHom.ext
  intro x
  let ri := Domain.inclusionOfSubset E (M.rightCover.cover.obj i) hi
  let rj := Domain.inclusionOfSubset E (M.rightCover.cover.obj j) hj
  let rk := Domain.inclusionOfSubset E (M.rightCover.cover.obj k) hk
  let ei := M.descentBaseChangeEquiv i E hi
  let ej := M.descentBaseChangeEquiv j E hj
  let ek := M.descentBaseChangeEquiv k E hk
  change ek.symm ((M.transitionMap k j rk rj)
      (ej (ej.symm ((M.transitionMap j i rj ri) (ei x))))) =
    ek.symm ((M.transitionMap k i rk ri) (ei x))
  rw [ej.apply_symm_apply]
  exact congrArg ek.symm (congrArg
    (fun q : BoundedAlgHom K (M.restrictedAlgebra i ri) (M.restrictedAlgebra k rk) => q (ei x))
    (M.transitionMap_comp k j i rk rj ri))

/-- The transported equivalence recovers the entire direct transition
after the constructed pasting comparison. -/
theorem descentTransitionEquiv_pasting (i j : Fin M.rightCover.cover.size)
    (E : Domain K R.algebra)
    (hi : E.locus ⊆ (M.rightCover.cover.obj i).locus)
    (hj : E.locus ⊆ (M.rightCover.cover.obj j).locus) :
    (M.descentBaseChangeEquiv j E hj).toBoundedAlgHom.comp
      (M.descentTransitionEquiv i j E hi hj).toBoundedAlgHom =
        (M.transitionMap j i (Domain.inclusionOfSubset E _ hj) (Domain.inclusionOfSubset E _ hi)).comp
          (M.descentBaseChangeEquiv i E hi).toBoundedAlgHom := by
  apply BoundedAlgHom.ext
  intro x
  exact (M.descentBaseChangeEquiv j E hj).apply_symm_apply _

/-- The exact general-descent transitions commute with its canonical
domain restrictions on entire closed-quotient algebras. -/
theorem descentTransitionEquiv_naturality (i j : Fin M.rightCover.cover.size)
    {E D : Domain K R.algebra} (hED : E.locus ⊆ D.locus)
    (hDi : D.locus ⊆ (M.rightCover.cover.obj i).locus)
    (hDj : D.locus ⊆ (M.rightCover.cover.obj j).locus) :
    (M.descentTransitionEquiv i j E (hED.trans hDi) (hED.trans hDj)).toBoundedAlgHom.comp
      (M.descentLocalAlgebras.restrict i hED hDi) =
        (M.descentLocalAlgebras.restrict j hED hDj).comp
          (M.descentTransitionEquiv i j D hDi hDj).toBoundedAlgHom := by
  let riD := Domain.inclusionOfSubset D (M.rightCover.cover.obj i) hDi
  let rjD := Domain.inclusionOfSubset D (M.rightCover.cover.obj j) hDj
  let riE := Domain.inclusionOfSubset E (M.rightCover.cover.obj i) (hED.trans hDi)
  let rjE := Domain.inclusionOfSubset E (M.rightCover.cover.obj j) (hED.trans hDj)
  let q := Domain.inclusionOfSubset E D hED
  let ρi := M.restrictionMap i riD riE q
  let ρj := M.restrictionMap j rjD rjE q
  let eiD := M.descentBaseChangeEquiv i D hDi
  let ejD := M.descentBaseChangeEquiv j D hDj
  let eiE := M.descentBaseChangeEquiv i E (hED.trans hDi)
  let ejE := M.descentBaseChangeEquiv j E (hED.trans hDj)
  let τD := (M.descentTransitionEquiv i j D hDi hDj).toBoundedAlgHom
  let τE := (M.descentTransitionEquiv i j E (hED.trans hDi) (hED.trans hDj)).toBoundedAlgHom
  apply BoundedAlgHom.ext
  intro x
  apply ejE.toAlgEquiv.injective
  change ejE (τE (M.descentLocalAlgebras.restrict i hED hDi x)) =
    ejE (M.descentLocalAlgebras.restrict j hED hDj (τD x))
  calc
    _ = (M.transitionMap j i rjE riE)
        (eiE (M.descentLocalAlgebras.restrict i hED hDi x)) :=
      congrArg (fun z : BoundedAlgHom K (M.descentLocalAlgebras.baseChange i E (hED.trans hDi))
        (M.restrictedAlgebra j rjE) => z (M.descentLocalAlgebras.restrict i hED hDi x))
          (M.descentTransitionEquiv_pasting i j E (hED.trans hDi) (hED.trans hDj))
    _ = (M.transitionMap j i rjE riE) (ρi (eiD x)) :=
      congrArg (M.transitionMap j i rjE riE)
        (congrArg (fun z => z x) (M.descentBaseChangeEquiv_restrict i hED hDi))
    _ = ρj ((M.transitionMap j i rjD riD) (eiD x)) :=
      (congrArg (fun z : BoundedAlgHom K (M.restrictedAlgebra i riD)
        (M.restrictedAlgebra j rjE) => z (eiD x))
          (M.transitionMap_naturality j i rjD riD rjE riE q)).symm
    _ = ρj (ejD (τD x)) :=
      congrArg ρj (congrArg (fun z => z x) (M.descentTransitionEquiv_pasting i j D hDi hDj)).symm
    _ = _ := (congrArg (fun z => z (τD x))
      (M.descentBaseChangeEquiv_restrict j hED hDj)).symm

/-- Actual pairwise equivalences of the literal original intersection
base changes, preserving their full coefficient algebras. -/
def descentPairTransitions : PairTransitions M.descentLocalAlgebras where
  equiv i j := M.descentTransitionEquiv i j (M.descentLocalAlgebras.overlap i j)
    (M.descentLocalAlgebras.overlapLeft i j) (M.descentLocalAlgebras.overlapRight i j)
  over_base i j := M.descentTransitionEquiv_comp_baseMap i j _
    (M.descentLocalAlgebras.overlapLeft i j) (M.descentLocalAlgebras.overlapRight i j)

/-- The general interface's canonically extended pair transition is
exactly the already constructed direct transition under pasting. -/
theorem descentPairTransitions_transition (i j : Fin M.rightCover.cover.size)
    (E : Domain K R.algebra)
    (hi : E.locus ⊆ (M.rightCover.cover.obj i).locus)
    (hj : E.locus ⊆ (M.rightCover.cover.obj j).locus) :
    M.descentPairTransitions.transition i j E hi hj =
      (M.descentTransitionEquiv i j E hi hj).toBoundedAlgHom := by
  let F := M.descentLocalAlgebras
  let O := F.overlap i j
  have hEO : E.locus ⊆ O.locus := fun _ hx => ⟨hi hx, hj hx⟩
  apply AffinoidPushout.hom_ext (F.map i) (restriction hi)
  · change (M.descentPairTransitions.transition i j E hi hj).comp (F.localMap i E hi) =
      (M.descentTransitionEquiv i j E hi hj).toBoundedAlgHom.comp (F.localMap i E hi)
    rw [M.descentPairTransitions.transition_localMap]
    have h := congrArg
      (fun z => z.comp (F.localMap i O (F.overlapLeft i j)))
      (M.descentTransitionEquiv_naturality i j hEO (F.overlapLeft i j) (F.overlapRight i j))
    rw [BoundedAlgHom.comp_assoc, F.restrict_localMap] at h
    exact h.symm
  · change (M.descentPairTransitions.transition i j E hi hj).comp (F.baseMap i E hi) =
      (M.descentTransitionEquiv i j E hi hj).toBoundedAlgHom.comp (F.baseMap i E hi)
    rw [M.descentPairTransitions.transition_baseMap]
    exact (M.descentTransitionEquiv_comp_baseMap i j E hi hj).symm

/-- The exact complete finite-algebra descent data for the actual finite
local pullback algebras, including identity and literal triple cocycle. -/
def algebraDescentData : DescentData M.descentLocalAlgebras where
  toPairTransitions := M.descentPairTransitions
  identity i := M.descentTransitionEquiv_self i _
    (M.descentLocalAlgebras.overlapLeft i i)
  cocycle i j k := by
    rw [M.descentPairTransitions_transition, M.descentPairTransitions_transition,
      M.descentPairTransitions_transition]
    exact M.descentTransitionEquiv_comp i j k _
      (M.descentLocalAlgebras.tripleFirst i j k) (M.descentLocalAlgebras.tripleSecond i j k)
      (M.descentLocalAlgebras.tripleThird i j k)

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FiniteOpenBaseChangeModels
