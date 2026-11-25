/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
public import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.Construction.TwistedActionTopology
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.Construction.TwistedActionCoefficient

/-! # Underlying twisted action site and coefficient sheaf

Source: the agent-formulated twisted variant of Stacks Tag 00W0,
original steps 1, 2, and the coefficient part of 4.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (s : C ≌ C) [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u})
    (a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R)

/-- The underlying integer-labelled site and its coefficient sheaf.

Source: original steps 1, 2, and the coefficient part of step 4 of the agent-formulated
argument motivated by Stacks 00W0, `sites.tex`, proposition-sheaves-on-group
(blueprint: lem-sf-twisted-action-site-core).

Proof: apply the proved integer tensor-power coherence construction to the
endofunctor of s and its chosen inverse. Transport its integer family to the exact
functors (s^n).functor, and use the existing integer-action category on the prescribed
object copy. The zero comparison and shifted-hom composition give the normalized
identities, inclusion and composition formulas. Each integer power preserves and
reflects covers, by continuity of both directions and its equivalence inverse.
Transport the existing integer-action topology to this object copy. Its universal
property identifies it with the required infimum; normalization of labelled arrows
in slices proves the cover and restricted sheaf criteria, hence continuity and
cocontinuity. Extend the given ring comparison to all integer shifts using the proved
integer-shift extension theorem, and compose these comparisons with the original
ring restriction maps. The addition axiom gives the presheaf laws. Its degree-zero
restriction is R, so the sheaf criterion makes it a ring sheaf. The addition identity
at minus one plus one, using the same comparison that defined the positive
generator, recovers exactly the prescribed inverse a. Package these
constructions into Site. The same argument treats empty sites, empty covering
families and the zero ring without extra hypotheses. -/
theorem siteCore [HasPullbacks C] :
    ∃ S : Site J s R a,
      letI := S.category
      S.inclusion.IsCocontinuous J S.topology := by
  let := Construction.category s
  let := Construction.inclusion_continuous s J
  let P := Construction.coefficientPresheaf s J R a
  have hP : Presheaf.IsSheaf (Construction.topology s J) P := by
    apply Construction.ring_isSheaf s J P
    exact (Presheaf.isSheaf_of_iso_iff
      (Construction.coefficientPresheafRestriction s J R a)).mpr R.property
  let S : Site J s R a := {
    category := Construction.category s
    inclusion := Construction.inclusion s
    inclusion_obj X := rfl
    arrows := Construction.arrows s
    powerComp := Construction.powerComp s
    arrows_id := Construction.arrows_id s
    arrows_comp := Construction.arrows_comp s
    arrows_inclusion := Construction.arrows_inclusion s
    topology := Construction.topology s J
    topology_eq := Construction.topology_eq s J
    inclusion_continuous := inferInstance
    coefficient := ⟨P, hP⟩
    coefficientRestriction := {
      hom := ⟨(Construction.coefficientPresheafRestriction s J R a).hom⟩
      inv := ⟨(Construction.coefficientPresheafRestriction s J R a).inv⟩
      hom_inv_id := by
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext X
        exact Iso.hom_inv_id_app _ X
      inv_hom_id := by
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext X
        exact Iso.inv_hom_id_app _ X }
    coefficient_generator := by
      intro X r
      change P.map _ r = _
      rw [Construction.coefficientPresheaf_generator]
      rfl }
  exact ⟨S, (Construction.topology_criterion s J).1⟩

end CategoryTheory.TwistedActionRingedSite
