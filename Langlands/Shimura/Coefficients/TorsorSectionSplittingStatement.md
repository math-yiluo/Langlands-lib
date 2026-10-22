# Geometric torsor splitting of sheaf sections

Author: Worker 155. This module defines a predicate and a proposition target;
it does not prove that geometric torsors satisfy the predicate.

`Langlands.Shimura.Coefficients.TorsorSectionSplitting` is defined for a category
`C : Type w` with `Category.{v} C` and binary products, a Grothendieck topology
`J` on `C`, a commutative ring `R : Type u`, a group `G : Type u`, and an action
`Y : Action C G`. Its explicit arguments are `J` and `Y`; the ring is supplied
as `(R := R)`. These universes agree with `Coefficients.Associated`, including
the independent object and morphism universes of the site.

The predicate quantifies every sheaf `F` of `R`-modules with carriers in
`Type u`, and every object `U` of `Over Y.V`. Write `p : U.left ⟶ Y.V` for
`U.hom`. It asserts that the canonical function

```text
F(Y.V × U.left) → (G → F(U.left))
s ↦ (g ↦ F(prod.lift (p ≫ Y.ρ g) (𝟙 U.left))(s))
```

is bijective. Here `F(f)` denotes the contravariant restriction map, implemented
as `F.obj.map f.op`. The first coordinate of the graph is `p ≫ Y.ρ g`,
with `g` itself rather than its inverse. The second coordinate is the identity.
The displayed product is the categorical binary product in `C`. Bijectivity
asserts unique gluing of every group-indexed family along these graph maps,
without choosing an inverse function. The quantifier covers arbitrary module
sheaves, with no constant-sheaf hypothesis or action on `F`.

`Langlands.Shimura.Coefficients.EtaleTorsorSectionSplittingStatement` quantifies
every scheme `X : Scheme.{u}`, group `G : Type u`, action `Y : Action X.Etale G`,
and commutative ring `R : Type u`. Under the unchanged
`IsFiniteGeometricTorsor X Y`, its conclusion is
`TorsorSectionSplitting (R := R) (Scheme.smallEtaleTopology X) Y`.
In this specialization the categorical product is over `X`. The existing
torsor predicate requires finite `G`, a finite surjective etale cover, and
unique transport between lifts of geometric points over separably closed
fields. It is the only additional mathematical premise of the target.
No action-map isomorphism, section-splitting witness, or associated-sheaf
trivialization is assumed.

This is a derived internal geometric prerequisite for the existing
`EtaleAssociatedTrivializationStatement` in
`Langlands.Shimura.Coefficients.TrivializationStatement`. That target concerns
the associated invariant sheaf constructed in `Coefficients.Associated` and
specialized in `Coefficients.Etale`. The present target isolates the expected
splitting of ordinary sheaf sections needed by the subsequent invariant-sheaf
argument. It does not itself assert that argument, its naturality, or the
associated-sheaf trivialization. Its provenance is this explicit decomposition
of the existing geometric torsor and local-trivialization interfaces; no
quotation or direct statement from the original literature is claimed.

The module imports `Langlands.Shimura.Coefficients.Etale`, preserving every
existing declaration. Formal dependencies include Mathlib's categories of
sheaves, module objects, actions, slice categories, binary products, and the
small etale site. Environment: Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
