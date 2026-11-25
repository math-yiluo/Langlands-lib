/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure

/-! # Naturality of the shared derived tensor symmetry
Source: Stacks Project, Cohomology, Tag 0FPB.
(blueprint: lem-sc-scheme-derived-tensor-symmetry).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry

private theorem naturalDerivedSymmetry {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [BraidedCategory C] (F : C ⥤ D) (W : MorphismProperty C)
    [F.IsLocalization W] [W.ContainsIdentities] [F.HasDerivedMonoidalCategory W] :
    ∃ s : ∀ K L : DerivedMonoidal F W, K ⊗ L ≅ L ⊗ K,
      ∀ (K K' L L' : DerivedMonoidal F W) (a : K ⟶ K') (b : L ⟶ L'),
        (a ⊗ₘ b) ≫ (s K' L').hom = (s K L).hom ≫ (b ⊗ₘ a) := by
  refine ⟨DerivedMonoidal.braiding' F W, ?_⟩
  intro K K' L L' a b
  rw [tensorHom_def, Category.assoc,
    DerivedMonoidal.braiding_naturality_right,
    ← Category.assoc, DerivedMonoidal.braiding_naturality_left,
    Category.assoc, ← tensorHom_def']

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The shared derived tensor has a natural symmetry.
Source: Stacks Project, cohomology.tex, Lemma cohomology-lemma-symmetric-monoidal-derived,
Tag 0FPB, using Tag 064K for invariance under K-flat replacement.
(blueprint: lem-sc-scheme-derived-tensor-symmetry).

Proof: Choose K-flat resolutions P and Q of K and L. On the (p,q) summand of
Tot(P tensor Q), use the sheaf tensor symmetry multiplied by (-1)^(pq).
The total differential's signs make this a chain isomorphism to Tot(Q tensor P).
Both total complexes compute the shared derived tensor, so localization gives
K tensor^L L isomorphic to L tensor^L K. The maps commute with maps of complexes
on each summand. A quasi-isomorphism tensored with a K-flat complex remains a
quasi-isomorphism: its cone is the tensor of the acyclic cone and is acyclic
by K-flatness. Common K-flat resolutions thus identify the symmetries for different
representatives. Represent derived morphisms by roofs and use this independence
to descend the termwise naturality square to all derived morphisms. Equivalently,
use DerivedMonoidal.braiding' of the shared localization Qh and its two naturality
lemmas; this is exactly the Koszul braiding just described. -/
theorem exists_schemeDerivedTensorSymmetry (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    ∃ s : ∀ K L : schemeDerivedCategory X, K ⊗ L ≅ L ⊗ K,
      ∀ (K K' L L' : schemeDerivedCategory X) (a : K ⟶ K') (b : L ⟶ L'),
        (a ⊗ₘ b) ≫ (s K' L').hom = (s K L).hom ≫ (b ⊗ₘ a) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have : CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    CategoryTheory.Limits.hasColimitsOfSizeShrink.{0, 0, u, u} _
  have := schemeModule_hasFunctorialFlatResolution X
  have := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  exact naturalDerivedSymmetry
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))

end AlgebraicGeometry
