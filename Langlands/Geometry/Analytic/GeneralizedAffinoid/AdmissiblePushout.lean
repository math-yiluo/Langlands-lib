import Langlands.Geometry.Analytic.GeneralizedAffinoid.ClosedQuotientBaseChange

/-! # Admissible epimorphisms under actual affinoid pushout -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B B' C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (f' : BoundedAlgHom K A B')
  (g : BoundedAlgHom K A C) (e : BoundedAlgEquiv K B B')
  (he : e.toBoundedAlgHom.comp f = f')

/-- Transport the first original pushout algebra through an actual bounded
equivalence over the unchanged base. -/
def mapOfLeftEquiv : BoundedAlgHom K (algebra f g) (algebra f' g) :=
  lift f g _ ((leftMap f' g).comp e.toBoundedAlgHom) (rightMap f' g) (by
    rw [BoundedAlgHom.comp_assoc, he, condition])

theorem mapOfLeftEquiv_comp_leftMap :
    (mapOfLeftEquiv f f' g e he).comp (leftMap f g) =
      (leftMap f' g).comp e.toBoundedAlgHom :=
  lift_comp_leftMap _ _ _ _ _ _

theorem mapOfLeftEquiv_comp_rightMap :
    (mapOfLeftEquiv f f' g e he).comp (rightMap f g) = rightMap f' g :=
  lift_comp_rightMap _ _ _ _ _ _

include he in
omit [CompleteSpace K] in
theorem leftEquiv_symm_over_base :
    e.symm.toBoundedAlgHom.comp f' = f := by
  apply BoundedAlgHom.ext
  intro a
  have h : e (f a) = f' a := congrArg
    (fun h : BoundedAlgHom K A B' => h a) he
  change e.symm (f' a) = f a
  rw [← h, BoundedAlgEquiv.symm_apply_apply]

/-- The inverse transport is constructed by the inverse bounded equivalence. -/
def inverseOfLeftEquiv : BoundedAlgHom K (algebra f' g) (algebra f g) :=
  mapOfLeftEquiv f' f g e.symm (leftEquiv_symm_over_base f f' e he)

theorem mapOfLeftEquiv_comp_inverseOfLeftEquiv :
    (mapOfLeftEquiv f f' g e he).comp (inverseOfLeftEquiv f f' g e he) =
      BoundedAlgHom.id K (algebra f' g) := by
  apply hom_ext f' g _
  · rw [BoundedAlgHom.comp_assoc]
    change (mapOfLeftEquiv f f' g e he).comp
      ((mapOfLeftEquiv f' f g e.symm _).comp (leftMap f' g)) = _
    rw [mapOfLeftEquiv_comp_leftMap, ← BoundedAlgHom.comp_assoc,
      mapOfLeftEquiv_comp_leftMap]
    apply BoundedAlgHom.ext
    intro b
    change leftMap f' g (e (e.symm b)) = leftMap f' g b
    rw [BoundedAlgEquiv.apply_symm_apply]
  · rw [BoundedAlgHom.comp_assoc]
    change (mapOfLeftEquiv f f' g e he).comp
      ((mapOfLeftEquiv f' f g e.symm _).comp (rightMap f' g)) = _
    rw [mapOfLeftEquiv_comp_rightMap, mapOfLeftEquiv_comp_rightMap]
    rfl

include e he in
/-- Admissibility of the unchanged second leg is invariant under a bounded
equivalence of the first algebra over the base. -/
theorem rightMap_isAdmissibleEpi_of_leftEquiv
    (h : (rightMap f g).IsAdmissibleEpi) : (rightMap f' g).IsAdmissibleEpi := by
  rw [← mapOfLeftEquiv_comp_rightMap f f' g e he]
  apply BoundedAlgHom.IsAdmissibleEpi.comp _ _ h
  exact BoundedAlgHom.isAdmissibleEpi_of_bounded_section _
    (inverseOfLeftEquiv f f' g e he)
    (mapOfLeftEquiv_comp_inverseOfLeftEquiv f f' g e he)

variable {f f' g e he}

/-- Every admissible quotient stays an admissible quotient under arbitrary
bounded base change of presented affinoids. -/
theorem rightMap_isAdmissibleEpi (f : BoundedAlgHom K A B)
    (g : BoundedAlgHom K A C) (hf : f.IsAdmissibleEpi) :
    (rightMap f g).IsAdmissibleEpi := by
  let J := RingHom.ker f.toAlgHom.toRingHom
  let : IsClosed (J : Set A) := isClosed_eq f.continuous continuous_const
  let e := ClosedQuotient.equivOfAdmissibleEpi A J f rfl hf
  have he : e.toBoundedAlgHom.comp (ClosedQuotient.map A J) = f :=
    ClosedQuotient.lift_comp_map A J f (fun _ ha => ha)
  exact rightMap_isAdmissibleEpi_of_leftEquiv (ClosedQuotient.map A J) f g e he
    (ClosedQuotient.rightMap_isAdmissibleEpi g J)

end Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout
