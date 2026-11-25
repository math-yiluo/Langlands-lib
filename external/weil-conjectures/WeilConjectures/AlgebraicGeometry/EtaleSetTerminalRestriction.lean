/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction

/-! # The terminal restriction isomorphism for an étale object

Source: Stacks Project, Étale Cohomology, Tag 03S2.
(blueprint: def-weil-pbc-sets-terminal-restriction).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 03S2, paragraph following Definition 03S3.
(blueprint: def-weil-pbc-sets-terminal-restriction).
Evaluate the étale inverse-image/restriction isomorphism at the identity object,
and identify the identity followed by the structure map with the structure map.
Invert this restriction isomorphism to send a section of `H` on `U` to the
terminal sections of its inverse image on `U`. -/
noncomputable def etaleSetTerminalRestriction
    {R : Scheme.{u}} (H : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : R.Etale) :
    H.obj.obj (op U) ≅
      ((Scheme.etaleSetPullback U.hom).obj H).obj.obj
        (op (Scheme.Etale.mk (𝟙 U.left))) :=
  H.obj.mapIso
    (MorphismProperty.Over.isoMk (Iso.refl U.left) (by simp)).op ≪≫
  (asIso (((Classical.choose (etaleSetInverseImageRestriction U.hom)).hom.app H).hom.app
    (op (Scheme.Etale.mk (𝟙 U.left))))).symm

end AlgebraicGeometry
