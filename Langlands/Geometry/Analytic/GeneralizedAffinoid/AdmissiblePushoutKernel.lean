import Langlands.Geometry.Analytic.GeneralizedAffinoid.AdmissiblePushout

/-! # Exact closed kernels of admissible affinoid pushout legs -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B B' C : PresentedAffinoidAlgebra K}

/-- The actual closed kernel ideal on the second algebra of an affinoid
pushout, with no surjectivity premise on the first leg. -/
def rightKernel (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C) : Ideal C :=
  RingHom.ker (rightMap f g).toAlgHom.toRingHom

omit [CompleteSpace K] in
/-- The stored norm topology makes the actual pushout-leg kernel closed. -/
theorem isClosed_rightKernel (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C) :
    IsClosed (rightKernel f g : Set C) :=
  isClosed_eq (rightMap f g).continuous continuous_const

/-- Changing the first quotient algebra by a bounded equivalence over the
base preserves the exact kernel of the unchanged second pushout leg. -/
theorem ker_rightMap_eq_of_leftEquiv
    (f : BoundedAlgHom K A B) (f' : BoundedAlgHom K A B')
    (g : BoundedAlgHom K A C) (e : BoundedAlgEquiv K B B')
    (he : e.toBoundedAlgHom.comp f = f') :
    RingHom.ker (rightMap f g).toAlgHom.toRingHom =
      RingHom.ker (rightMap f' g).toAlgHom.toRingHom := by
  ext c
  change rightMap f g c = 0 ↔ rightMap f' g c = 0
  have h₁ := congrArg (fun h : BoundedAlgHom K C (algebra f' g) => h c)
    (mapOfLeftEquiv_comp_rightMap f f' g e he)
  have h₂ := congrArg (fun h : BoundedAlgHom K C (algebra f g) => h c)
    (mapOfLeftEquiv_comp_rightMap f' f g e.symm
      (leftEquiv_symm_over_base f f' e he))
  constructor
  · intro hc
    exact h₁.symm.trans ((congrArg (mapOfLeftEquiv f f' g e he) hc).trans (map_zero _))
  · intro hc
    exact h₂.symm.trans ((congrArg
      (mapOfLeftEquiv f' f g e.symm (leftEquiv_symm_over_base f f' e he)) hc).trans
        (map_zero _))

/-- The exact kernel of an arbitrary base-changed admissible quotient is the
closed extension of its original kernel along the original coefficient map. -/
theorem ker_rightMap (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)
    (hf : f.IsAdmissibleEpi) :
    RingHom.ker (rightMap f g).toAlgHom.toRingHom =
      g.closedIdealMap (RingHom.ker f.toAlgHom.toRingHom) := by
  let J := RingHom.ker f.toAlgHom.toRingHom
  let : IsClosed (J : Set A) := isClosed_eq f.continuous continuous_const
  let e := ClosedQuotient.equivOfAdmissibleEpi A J f rfl hf
  have he : e.toBoundedAlgHom.comp (ClosedQuotient.map A J) = f :=
    ClosedQuotient.lift_comp_map A J f (fun _ ha => ha)
  exact (ker_rightMap_eq_of_leftEquiv (ClosedQuotient.map A J) f g e he).symm.trans
    (ClosedQuotient.ker_rightMap g J)

/-- For an admissible first leg the constructed kernel is exactly the closed
extension of its actual original kernel. -/
theorem rightKernel_eq (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)
    (hf : f.IsAdmissibleEpi) :
    rightKernel f g = g.closedIdealMap (RingHom.ker f.toAlgHom.toRingHom) :=
  ker_rightMap f g hf

end Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout
