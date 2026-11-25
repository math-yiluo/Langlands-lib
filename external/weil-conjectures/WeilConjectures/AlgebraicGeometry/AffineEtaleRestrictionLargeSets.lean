/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Topologies 04HR and Sites 03A0.
Proof: every etale scheme has an affine open cover. The full affine inclusion is
fully faithful, so equality and lifting of arrows hold on identity covers.
Finite affine etale coverings are coverings in the full site, and every covering
of an affine etale scheme has a finite affine refinement. These facts identify
fullAffineEtaleTopology with the topology induced from smallEtaleTopology and
make the inclusion a dense subsite. Extend an affine sheaf by compatible families
on affine covers of each etale object; the sheaf condition makes the extension
independent of the cover and gives its restriction back. Conversely the sheaf
condition identifies any full-site sheaf with this extension of its restriction.
These constructions are inverse on morphisms as well as objects. Families and
compatibility conditions lie in Type (u + 1), so this construction works in that
coefficient universe without shrinking the section sets.
(blueprint: lem-stage3-affine-etale-restriction-large-sets) -/
theorem fullAffineEtale_large_sets_equivalence (S : Scheme.{u}) :
    ((fullAffineEtaleInclusion S).sheafPushforwardContinuous (Type (u + 1))
      (fullAffineEtaleTopology S) S.smallEtaleTopology).IsEquivalence := by
  let F := fullAffineEtaleInclusion S
  have h := fullAffineEtale_special_cocontinuity S
  have hK : S.smallEtalePretopology.toPrecoverage.toGrothendieck =
      S.smallEtaleTopology := by
    calc
      S.smallEtalePretopology.toPrecoverage.toGrothendieck =
          S.smallEtalePretopology.toGrothendieck := by
        apply le_antisymm
        · rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
          intro U R hR
          exact ⟨R, hR, Sieve.le_generate R⟩
        · intro U R hR
          obtain ⟨T, hT, hTR⟩ := hR
          exact S.smallEtalePretopology.toPrecoverage.toGrothendieck.superset_covering
            ((Sieve.generate_le_iff T R).mpr hTR) (Precoverage.generate_mem_toGrothendieck hT)
      _ = S.smallEtaleTopology :=
        (S.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology
          (P := @Etale.{u}) (Q := @Etale.{u}) le_rfl).symm
  let : F.Full := inferInstanceAs (ObjectProperty.ι _).Full
  let : F.Faithful := inferInstanceAs (ObjectProperty.ι _).Faithful
  let : F.IsCocontinuous (fullAffineEtaleTopology S) S.smallEtaleTopology := by
    simpa only [hK, F, fullAffineEtaleTopology] using h.1
  let : F.IsCoverDense S.smallEtaleTopology := ⟨fun V ↦ by
    obtain ⟨I, U, f, hf⟩ := h.2.2.2.2.2 V
    apply S.smallEtaleTopology.superset_covering _
      (show Sieve.generate (Presieve.ofArrows (fun i ↦ F.obj (U i)) f) ∈
        S.smallEtaleTopology V from ?_)
    · rw [Sieve.generate_le_iff]
      rintro W g ⟨i⟩
      exact Presieve.in_coverByImage F (f i)
    · rw [← hK]
      exact Precoverage.generate_mem_toGrothendieck hf⟩
  let : F.IsDenseSubsite (fullAffineEtaleTopology S) S.smallEtaleTopology := {
    functorPushforward_mem_iff := by
      intro U R
      constructor
      · intro hR
        simpa only [Sieve.functorPullback_functorPushforward_eq] using
          F.cover_lift (fullAffineEtaleTopology S) S.smallEtaleTopology hR
      · exact (CoverPreserving.of_isContinuous F _ _).cover_preserve }
  exact inferInstanceAs (F.sheafPushforwardContinuous (Type (u + 1))
    (fullAffineEtaleTopology S) S.smallEtaleTopology).IsEquivalence

end AlgebraicGeometry.Scheme
