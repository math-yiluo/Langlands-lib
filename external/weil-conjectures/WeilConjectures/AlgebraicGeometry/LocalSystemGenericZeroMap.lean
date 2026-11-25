/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.GenericStalkVanishingPropagation
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! # Generic detection of maps into a local system -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A morphism into a local system vanishes if it vanishes at the geometric generic point.
Source: Stacks Project, Tag 09BG, the persistence of a nonzero constant germ used
in the generic-neighbourhood argument of Tag 09BH (3).
(blueprint: lem-weil-pbc-local-system-generic-zero-map).

Proof: If the morphism is nonzero, conservativity of geometric stalks and exactness
of those stalks give a germ whose image in G is nonzero. Pull back to an etale
trivialization of G and represent this germ by a section on a pointed etale
neighbourhood. Refine the neighbourhood until its image in the constant target is
a fixed nonzero constant section. The neighbourhood has nonempty open image in X.
Since X is irreducible with generic point eta, this image contains eta. Its fibre
over a geometric generic point is nonempty and etale, and hence has a geometric
point after passing to a separably closed field. At this point the same constant
section has a nonzero germ, whereas the hypothesis says the morphism has zero
stalk map there. This contradiction shows all image stalks vanish. Conservativity
then makes the image sheaf zero and the morphism zero. The zero target and zero
source are automatic; an empty X cannot supply eta. No finiteness of the modules
or Noetherianity of X or the ring is used in this detection argument. -/
theorem eq_zero_of_generic_sheafFiber_eq_zero
    {X : Scheme.{u}} [IrreducibleSpace X] {Λ : Type (u + 1)} [CommRing Λ]
    (η : X) (hη : IsGenericPoint η Set.univ)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    [IsLocallyConstantSheaf G] (φ : F ⟶ G)
    (hφ : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      s (IsLocalRing.closedPoint Ω) = η → (pointSmallEtale s).sheafFiber.map φ = 0) :
    φ = 0 := by
  have : Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro x
  have : ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).Additive :=
    (pointSmallEtale (X.algClosurePoint x)).sheafFiber_additive
  simpa only [Functor.map_zero] using
    all_sheafFiber_map_eq_zero_of_generic η hη φ hφ _ (X.algClosurePoint x)

end AlgebraicGeometry.Scheme
