/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleMorphism
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleAffinePresentations
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalRelativeProjRestrictionComparison

/-! # Local properness of the canonical relative Proj

Source: Stacks Project, Morphisms, Lemmas 01WB and 01WC.
The relative Proj of the restricted module on each affine open of a finite-generator cover is
identified (`exists_canonicalRelativeProj_restrict_iso`) with the restriction of the global
relative Proj; H-projective properness transports across that comparison and glues by
target-locality.
(blueprint: lem-trf-canonical-relative-proj-proper-local).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory

namespace AlgebraicGeometry

private theorem canonicalRelativeProj_member_proper {S : Scheme.{u}} (E : S.Modules)
    (hE : E.IsQuasiCoherentFiniteType) (U : S.Opens) (hU : IsAffineOpen U)
    (hq : (E.restrict U.ι).IsQuasicoherent)
    (hproj : IsHProjective
      (@SymmetricAlgebraSheaf.gradedAlgebraData U.toScheme
        (E.restrict U.ι) hq).relProjHom) :
    IsProper ((@SymmetricAlgebraSheaf.gradedAlgebraData S E hE.1).relProjHom ∣_ U) := by
  have hlocal : IsProper
      (@SymmetricAlgebraSheaf.gradedAlgebraData U.toScheme
        (E.restrict U.ι) hq).relProjHom := hProjective_properness.1 _ hproj
  obtain ⟨e, he⟩ := exists_canonicalRelativeProj_restrict_iso E hE U hU hq
  have hcomp : IsProper (e.hom ≫
      ((@SymmetricAlgebraSheaf.gradedAlgebraData S E hE.1).relProjHom ∣_ U)) := by
    rw [he]
    exact hlocal
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)
    e.hom _).mp hcomp

private theorem canonicalRelativeProj_global_proper {S : Scheme.{u}} (E : S.Modules)
    (hE : E.IsQuasiCoherentFiniteType) :
    IsProper (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE.1).relProjHom := by
  obtain ⟨I, U, n, hU, hlocal⟩ :=
    exists_affine_projectiveBundle_presentations S E hE
  apply IsZariskiLocalAtTarget.of_iSup_eq_top U hU
  intro i
  obtain ⟨hi, ⟨s, hs, hq, hfin, j, hj, hjc, hproj⟩⟩ := hlocal i
  exact canonicalRelativeProj_member_proper E hE (U i) hi hq hproj

/-- The canonical relative Proj is proper after restriction to any affine open of the base.

Source: Stacks Project, Morphisms, Lemmas 01WB and 01WC.
Proof: `exists_affine_projectiveBundle_presentations` gives an affine open cover of `S` on
each member of which the local relative Proj is H-projective, hence proper by
`hProjective_properness`; `exists_canonicalRelativeProj_restrict_iso` identifies it over the
member with the restriction of the global relative Proj, and properness is invariant under
isomorphism of the source.  Properness is local on the target, so the global relative Proj is
proper, and the restriction of a proper morphism to `U` is proper.
The comparison between the restricted canonical Proj and the local relative Proj is isolated
in `exists_canonicalRelativeProj_restrict_iso`.
(blueprint: lem-trf-canonical-relative-proj-proper-local). -/
theorem canonicalRelativeProj_restrict_proper {S : Scheme.{u}} (E : S.Modules)
    (hE : E.IsQuasiCoherentFiniteType) (U : S.Opens) (_hU : IsAffineOpen U) :
    IsProper ((@SymmetricAlgebraSheaf.gradedAlgebraData S E hE.1).relProjHom ∣_ U) := by
  have hglobal := canonicalRelativeProj_global_proper E hE
  exact inferInstance

end AlgebraicGeometry

end
