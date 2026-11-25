/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback

import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullbackIdentity
import WeilConjectures.AlgebraicGeometry.Structure.StructureSheafCohomologyPullbackComposition

/-!
# Functoriality of pullback on structure sheaf cohomology

Source: Stacks Project, Cohomology of Sheaves, Section 01F7, equation-functorial
(blueprint: lem-sc-structure-sheaf-cohomology-pullback-functorial).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Canonical pullback on structure sheaf cohomology preserves identities and reverses
composition. Source: Stacks Project, Cohomology of Sheaves, Section 01F7,
equation-functorial and Remark 20.14.2
(blueprint: lem-sc-structure-sheaf-cohomology-pullback-functorial).

Proof: Regard the structure ring map of each scheme morphism as a map of abelian sheaves
into the direct image. On injective resolutions, lift this map as in Remark 20.14.2 and
apply global sections. For the identity, the identity resolution map is a lift and induces
the identity on cohomology. For two composable morphisms, compose the lifted maps after
pushforward; the composite lifts the structure ring map of their composite, since scheme
structure maps compose. Any two such lifts give the same derived map, by the comparison
and homotopy uniqueness theorem for resolutions. Thus their induced cohomology maps
compose in the displayed order. Finally compare this resolution construction with the
Ext construction used in structureSheafCohomologyPullback: the exact inverse image,
its constant-integer-sheaf comparison, and the adjoint structure map induce the same
map of derived global sections. Naturality of the adjunction and of the constant-sheaf
comparison identifies the composite Ext map with the resolution map. This gives both
identities for every degree, including degree zero. -/
theorem structureSheafCohomologyPullback_functorial :
    (∀ (X : Scheme.{u}) (n : ℕ),
      structureSheafCohomologyPullback (𝟙 X) n =
        AddMonoidHom.id (Sheaf.H (structureSheafAb X) n)) ∧
    (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ),
      structureSheafCohomologyPullback (f ≫ g) n =
        (structureSheafCohomologyPullback f n).comp
          (structureSheafCohomologyPullback g n)) := by
  constructor
  · intro X n
    exact structureSheafCohomologyPullback_identity X n
  · intro X Y Z f g n
    exact structureSheafCohomologyPullback_comp f g n

end AlgebraicGeometry.Scheme
