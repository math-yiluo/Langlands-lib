/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Adjunction.Basic

import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound
import WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison
import WeilConjectures.AlgebraicGeometry.AffineDerivedUnitHomologyIsIso

/-! # The derived affine unit

Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5.
(blueprint: lem-pc-affine-derived-unit-isomorphism).
-/

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

/-- The unit of the affine derived tilde-sections adjunction is invertible.
Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5, unit calculation.
(blueprint: lem-pc-affine-derived-unit-isomorphism).

Proof: Construct the canonical sections comparison as follows. Global sections
preserves products as a right adjoint, and scalar transport through ΓSpecIso is
exact and preserves products. Affine vanishing gives cohomological bound one.
Apply the unbounded bound to τ_{≤ -1}E: derived sections vanish in degrees zero
and one. The truncation triangle identifies H^0(RΓ(E)) with H^0(RΓ(τ_{≥ 0}E));
left exactness identifies the latter with Γ(H^0(E)). These identifications come
from the truncation maps and the right-derived-functor unit on complexes, and
are natural. Shifts give them in every degree. This constructs the comparison
with its canonical maps, rather than selecting an arbitrary natural isomorphism.
For a complex P of A-modules choose a K-injective resolution s : tilde(P) → I.
The canonical derived unit is represented by the ordinary termwise unit
P → Γ(tilde(P)), followed by Γ(s). The truncation comparison is induced by the
right-derived-functor unit on complexes. Its naturality for s identifies the map
on H^n with H^n(P) → Γ(tilde(H^n(P))) → Γ(H^n(I)). Here the first map is the
ordinary module unit and the second is Γ(H^n(s)), after the exact tilde
comparison of `affineDerivedTilde_homology_comparison`. Both maps are invertible:
tilde is fully faithful, and s is a quasi-isomorphism. Thus the derived unit
induces an isomorphism in every degree and is itself invertible by the derived
cohomology criterion. Every object of D(A) is represented by a complex P.
Descend hF through the localization Q and transport the canonical adjunction
using hG. Uniqueness of right adjoints identifies any adjunction on F and G with
this one and preserves invertibility of its unit. No counit invertibility is
used. The truncation comparison applies to unbounded complexes; the zero ring
and zero complex are included. -/
theorem affineDerivedUnit_isIso (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ schemeDerivedQCohCategory (Spec (.of A)))
    (G : schemeDerivedQCohCategory (Spec (.of A)) ⥤ DerivedCategory (ModuleCat.{u} A))
    (adj : F ⊣ G)
    (hF : Nonempty (DerivedCategory.Q ⋙ F ⋙
        (schemeDerivedQCohProperty (Spec (.of A))).ι ≅
        @Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q))
    (hG : Nonempty (G ≅ (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        (RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor))
    (M : DerivedCategory (ModuleCat.{u} A)) : IsIso (adj.unit.app M) := by
  apply (DerivedCategory.isIso_iff _ _).2
  intro n
  exact affineDerivedUnit_homology_isIso A F G adj hF hG M n

end AlgebraicGeometry
