import Langlands.Geometry.Analytic.GeneralizedAffinoid.AdmissiblePushout
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.LocalData
import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushoutPasting

/-! # Further base change of local algebras and pair transitions -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

namespace AffinoidPushout

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B B' C D : PresentedAffinoidAlgebra K}

section Pasting

variable (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C) (h : BoundedAlgHom K C D)
  (k : BoundedAlgHom K A D) (hk : h.comp g = k)

private def pastingEquivOfComp : BoundedAlgEquiv K (algebra (rightMap f g) h) (algebra f k) :=
  hk ▸ pastingEquiv f g h

private theorem pastingEquivOfComp_right :
    (pastingEquivOfComp f g h k hk).toBoundedAlgHom.comp (rightMap (rightMap f g) h) = rightMap f k := by
  subst k
  exact pastingEquiv_comp_right f g h

private theorem pastingEquivOfComp_left :
    (pastingEquivOfComp f g h k hk).toBoundedAlgHom.comp
      ((leftMap (rightMap f g) h).comp (leftMap f g)) = leftMap f k := by
  subst k
  exact pastingEquiv_comp_left f g h

end Pasting

section Transport

variable (f : BoundedAlgHom K A B) (f' : BoundedAlgHom K A B') (g : BoundedAlgHom K A C)
  (e : BoundedAlgEquiv K B B') (he : e.toBoundedAlgHom.comp f = f')

private theorem transportLeft_inverse :
    (mapOfLeftEquiv f' f g e.symm (leftEquiv_symm_over_base f f' e he)).comp
        (mapOfLeftEquiv f f' g e he) = BoundedAlgHom.id K (algebra f g) := by
  let p := mapOfLeftEquiv f f' g e he
  let q := mapOfLeftEquiv f' f g e.symm (leftEquiv_symm_over_base f f' e he)
  apply hom_ext f g
  · change (q.comp p).comp (leftMap f g) = _
    rw [BoundedAlgHom.comp_assoc, mapOfLeftEquiv_comp_leftMap f f' g e he,
      ← BoundedAlgHom.comp_assoc, mapOfLeftEquiv_comp_leftMap f' f g e.symm,
      BoundedAlgHom.id_comp, BoundedAlgHom.comp_assoc]
    apply BoundedAlgHom.ext
    intro b
    exact congrArg (leftMap f g) (e.symm_apply_apply b)
  · change (q.comp p).comp (rightMap f g) = _
    rw [BoundedAlgHom.comp_assoc, mapOfLeftEquiv_comp_rightMap f f' g e he,
      mapOfLeftEquiv_comp_rightMap f' f g e.symm, BoundedAlgHom.id_comp]

private def transportLeftEquiv : BoundedAlgEquiv K (algebra f g) (algebra f' g) := by
  let q := mapOfLeftEquiv f' f g e.symm (leftEquiv_symm_over_base f f' e he)
  refine BoundedAlgEquiv.ofHomInv (mapOfLeftEquiv f f' g e he) q ?_ ?_
  · intro x
    exact congrArg (fun p : BoundedAlgHom K (algebra f g) (algebra f g) => p x)
      (transportLeft_inverse f f' g e he)
  · intro x
    exact congrArg (fun p : BoundedAlgHom K (algebra f' g) (algebra f' g) => p x)
      (transportLeft_inverse f' f g e.symm (leftEquiv_symm_over_base f f' e he))

end Transport
end AffinoidPushout

namespace FiniteAffinoidAlgebraDescent

open AffinoidPushout

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K} {c : Domain.FiniteCover (Domain.whole K R)}
  (F : LocalAlgebras c)

namespace LocalAlgebras

variable {E D : Domain K R} (i : Fin c.size) (hED : E.locus ⊆ D.locus)
  (hDi : D.locus ⊆ (c.obj i).locus)

/-- Further actual pushout of a local base change canonically identifies
with the direct base change to the smaller original domain. -/
def furtherBaseChangeEquiv :
    BoundedAlgEquiv K (AffinoidPushout.algebra (F.baseMap i D hDi) (restriction hED))
      (F.baseChange i E (hED.trans hDi)) :=
  pastingEquivOfComp (F.map i) (restriction hDi) (restriction hED) (restriction (hED.trans hDi))
    (restriction_comp hED hDi)

@[simp] theorem furtherBaseChangeEquiv_right :
    (F.furtherBaseChangeEquiv i hED hDi).toBoundedAlgHom.comp
      (AffinoidPushout.rightMap (F.baseMap i D hDi) (restriction hED)) =
        F.baseMap i E (hED.trans hDi) :=
  pastingEquivOfComp_right _ _ _ _ _

@[simp] theorem furtherBaseChangeEquiv_left :
    (F.furtherBaseChangeEquiv i hED hDi).toBoundedAlgHom.comp
      (AffinoidPushout.leftMap (F.baseMap i D hDi) (restriction hED)) = F.restrict i hED hDi := by
  let e := F.furtherBaseChangeEquiv i hED hDi
  let l := AffinoidPushout.leftMap (F.baseMap i D hDi) (restriction hED)
  apply AffinoidPushout.hom_ext (F.map i) (restriction hDi)
  · exact (pastingEquivOfComp_left (F.map i) (restriction hDi) (restriction hED)
      (restriction (hED.trans hDi)) (restriction_comp hED hDi)).trans
        (F.restrict_localMap i hED hDi).symm
  · change (e.toBoundedAlgHom.comp l).comp (F.baseMap i D hDi) = _
    have hp := congrArg (fun p => e.toBoundedAlgHom.comp p)
      (AffinoidPushout.condition (F.baseMap i D hDi) (restriction hED))
    exact hp.trans ((congrArg (fun p => p.comp (restriction hED))
      (F.furtherBaseChangeEquiv_right i hED hDi)).trans (F.restrict_baseMap i hED hDi).symm)

end LocalAlgebras

namespace PairTransitions

variable {F} (t : PairTransitions F) (i j : Fin c.size) (E : Domain K R)
  (hi : E.locus ⊆ (c.obj i).locus) (hj : E.locus ⊆ (c.obj j).locus)

include hi hj in
private theorem overlap_containment : E.locus ⊆ (F.overlap i j).locus := fun _ hx => ⟨hi hx, hj hx⟩

/-- The transition on a smaller domain remains an ordinary bounded
algebra equivalence, obtained by base change of the given pair equivalence. -/
def transitionEquiv : BoundedAlgEquiv K (F.baseChange i E hi) (F.baseChange j E hj) :=
  let h := overlap_containment (F := F) i j E hi hj
  let ei := F.furtherBaseChangeEquiv i h (F.overlapLeft i j)
  let ej := F.furtherBaseChangeEquiv j h (F.overlapRight i j)
  ei.symm.trans ((transportLeftEquiv
    (F.baseMap i (F.overlap i j) (F.overlapLeft i j))
    (F.baseMap j (F.overlap i j) (F.overlapRight i j)) (restriction h) (t.equiv i j) (t.over_base i j)).trans ej)

/-- The full bounded map of the transition equivalence is the transition
already defined on the actual local base changes. -/
theorem transitionEquiv_eq :
    (t.transitionEquiv i j E hi hj).toBoundedAlgHom = t.transition i j E hi hj := by
  let h := overlap_containment (F := F) i j E hi hj
  let fi := F.baseMap i (F.overlap i j) (F.overlapLeft i j)
  let fj := F.baseMap j (F.overlap i j) (F.overlapRight i j)
  let g := restriction h
  let ei := F.furtherBaseChangeEquiv i h (F.overlapLeft i j)
  let ej := F.furtherBaseChangeEquiv j h (F.overlapRight i j)
  let T := mapOfLeftEquiv fi fj g (t.equiv i j) (t.over_base i j)
  have hright (a : E.algebra) : ei.symm (F.baseMap i E hi a) = AffinoidPushout.rightMap fi g a := by
    have h := congrArg (fun p => p a) (F.furtherBaseChangeEquiv_right i h (F.overlapLeft i j))
    exact (congrArg ei.symm h).symm.trans (ei.symm_apply_apply _)
  have hleft (x : F.algebra i) :
      ei.symm (F.localMap i E hi x) =
        AffinoidPushout.leftMap fi g (F.localMap i (F.overlap i j) (F.overlapLeft i j) x) := by
    have h₁ := congrArg (fun p => p (F.localMap i (F.overlap i j) (F.overlapLeft i j) x))
      (F.furtherBaseChangeEquiv_left i h (F.overlapLeft i j))
    have h₂ := congrArg (fun p => p x) (F.restrict_localMap i h (F.overlapLeft i j))
    exact (congrArg ei.symm (h₁.trans h₂)).symm.trans (ei.symm_apply_apply _)
  apply AffinoidPushout.hom_ext (F.map i) (restriction hi)
  · apply BoundedAlgHom.ext
    intro x
    change ej (T (ei.symm (F.localMap i E hi x))) = t.transition i j E hi hj (F.localMap i E hi x)
    calc
      _ = ej (T (AffinoidPushout.leftMap fi g (F.localMap i (F.overlap i j) (F.overlapLeft i j) x))) :=
        congrArg (fun y => ej (T y)) (hleft x)
      _ = ej (AffinoidPushout.leftMap fj g ((t.equiv i j)
          (F.localMap i (F.overlap i j) (F.overlapLeft i j) x))) :=
        congrArg ej (congrArg (fun p => p (F.localMap i (F.overlap i j) (F.overlapLeft i j) x))
          (mapOfLeftEquiv_comp_leftMap fi fj g (t.equiv i j) (t.over_base i j)))
      _ = F.restrict j h (F.overlapRight i j) ((t.equiv i j)
          (F.localMap i (F.overlap i j) (F.overlapLeft i j) x)) :=
        congrArg (fun p => p ((t.equiv i j) (F.localMap i (F.overlap i j) (F.overlapLeft i j) x)))
          (F.furtherBaseChangeEquiv_left j h (F.overlapRight i j))
      _ = _ := (congrArg (fun p => p x) (t.transition_localMap i j E hi hj)).symm
  · apply BoundedAlgHom.ext
    intro a
    change ej (T (ei.symm (F.baseMap i E hi a))) = t.transition i j E hi hj (F.baseMap i E hi a)
    calc
      _ = ej (T (AffinoidPushout.rightMap fi g a)) := congrArg (fun y => ej (T y)) (hright a)
      _ = ej (AffinoidPushout.rightMap fj g a) := congrArg ej
        (congrArg (fun p => p a) (mapOfLeftEquiv_comp_rightMap fi fj g (t.equiv i j) (t.over_base i j)))
      _ = F.baseMap j E hj a := congrArg (fun p => p a) (F.furtherBaseChangeEquiv_right j h (F.overlapRight i j))
      _ = _ := (congrArg (fun p => p a) (t.transition_baseMap i j E hi hj)).symm

end PairTransitions
end FiniteAffinoidAlgebraDescent
end Langlands.Analytic.PresentedAffinoidAlgebra
