/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageTransitions
import WeilConjectures.AlgebraicGeometry.CartesianHigherImageAffineSectionLocalVanishing

/-! # Eventual vanishing of affine relative higher-image sections

Source: Stacks Project, Tag 0EYM, second proof.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- An affine section killed by the relative limit comparison dies at a later stage.
Source: Stacks Project, Tag 0EYM, second proof, injectivity on affine etale objects.
(blueprint: lem-sc-cartesian-higher-image-affine-section-vanishing)

Proof: Lift the section locally to the cohomology presheaf of the stage cartesian
source. Its zero limit image becomes zero in this presheaf after an etale refinement,
by local injectivity of sheafification. Refine by affine objects and descend these
finitely presented objects and arrows to a common stage. Base change the source
system to each descended affine object and apply cohomology continuity (09YQ);
each zero limit class is killed at a later stage. Naturality of the presheaf
comparison, exact inverse image and exchange pasting identify these images with
the displayed transition. Quasi-compactness of U supplies a finite subcover, and
cofilteredness supplies one common killing arrow, equalizing the finitely many
parallel arrows if needed. The transitioned section is zero on this cover, hence
zero by sheaf separatedness. Empty U and zero sections give the identity witness;
q = 0 is the same equality-of-sections argument. No stage exchange is assumed
invertible. -/
theorem exists_cartesianHigherImage_affine_section_eq_zero
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (U : c.pt.left.Etale) [IsAffine U.left] (i : I)
    (x : (cartesianHigherImageStage D c f F q i).obj.obj (Opposite.op U))
    (hx : (cartesianHigherImageLeg D c f F q i).hom.app (Opposite.op U) x = 0) :
    ∃ (j : I) (a : j ⟶ i),
      (cartesianHigherImageTransition D c f F q a).hom.app (Opposite.op U) x = 0 := by
  classical
  obtain ⟨j, a, J, _, V, r, hcover, hzero⟩ :=
    exists_cartesianHigherImage_affine_section_local_zero D c hc f F q U i x hx
  refine ⟨j, a, ?_⟩
  exact cartesianHigherImage_section_eq_zero_of_finite_cover
    D c f F q U i j a x J V r hcover hzero

end AlgebraicGeometry.Etale
