/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Local ingredients of alternating Čech exactness

Source: Stacks Project, Tags 02FU and 01FM.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Sheafification does not change the explicit intersection-product terms.
Source: Stacks Project, Tag 02FU, direct images of restrictions are sheaves;
finite products are sheaves, as used in the covering resolution.
(blueprint: lem-pc-s3-alternating-cech-presheaf-terms-sheafification).

Proof: For a fixed intersection W, the presheaf V ↦ G(V intersect W) is the
direct image along the inclusion W into X of the restriction of G to W.
The scalar restriction in cechCapModule agrees with the scalar structure
of that direct image. It is therefore a sheaf. Products of these sheaves
are computed as products of presheaves, and the explicit terms are exactly
those finite products. The sheafification unit of an already sheaf
presheaf is an isomorphism, also in the category of module presheaves,
since the forgetful functor reflects isomorphisms. The empty product is
the zero module presheaf and is a sheaf as well.
-/
theorem alternatingCechSheafPresheafTerms_unit_isIso
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (p : ℕ) :
    IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app (alternatingCechSheafPresheafTerms U G p)) :=
  by
    classical
    have hcap (W : X.Opens) : Presheaf.IsSheaf (Opens.grothendieckTopology X)
        (cechCapModule G W).presheaf := by
      let T := Opens.map W.ι.base ⋙ W.ι.opensFunctor
      let e : T ≅ cechCapFunctor W := NatIso.ofComponents (fun V ↦
        eqToIso (by
          change W.ι ''ᵁ W.ι ⁻¹ᵁ V = V ⊓ W
          simp [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_comm]))
      have : (cechCapFunctor W).IsContinuous (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology X) :=
        Functor.isContinuous_of_iso e _ _
      exact (cechCapFunctor W).op_comp_isSheaf_of_isSheaf _ _ G.val.presheaf G.isSheaf
    have ht : Presheaf.IsSheaf (Opens.grothendieckTopology X)
        (alternatingCechSheafPresheafTerms U G p).presheaf := by
      apply PresheafOfModules.isSheaf_of_isLimit (limit.isLimit _)
      intro t
      exact hcap (alternatingCechIntersection U t.as)
    let M : X.Modules := ⟨alternatingCechSheafPresheafTerms U G p, ht⟩
    apply (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).isIso_unit_app_of_iso (X := M)
    exact Iso.refl _

end AlgebraicGeometry
