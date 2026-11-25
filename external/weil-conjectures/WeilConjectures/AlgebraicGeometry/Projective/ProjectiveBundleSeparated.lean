/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic

/-!
# Separatedness of a projective bundle

## References

* Stacks Project, Constructions, Tag 01OD
* Stacks Project, Constructions, Tag 01OD, via Tag 01O2
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The relative projective bundle of a quasi-coherent module has separated structure morphism. -/
theorem isSeparated_projectiveBundle {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] :
    IsSeparated (@SymmetricAlgebraSheaf.gradedAlgebraData S E inferInstance).relProjHom := by
  let A := @SymmetricAlgebraSheaf.gradedAlgebraData S E inferInstance
  change IsSeparated A.relProjHom
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsSeparated) S.directedAffineCover
  intro U
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsSeparated
    (A.isPullback_relProjι U).flip.isoPullback.hom]
  change IsSeparated ((A.isPullback_relProjι U).flip.isoPullback.hom ≫
    CategoryTheory.Limits.pullback.snd A.relProjHom U.1.ι)
  rw [(A.isPullback_relProjι U).flip.isoPullback_hom_snd]
  infer_instance

end AlgebraicGeometry
