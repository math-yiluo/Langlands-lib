# Restriction and the fibration of actual continuous actions

This internal topological construction uses the published category
`VariableContinuousAction`. Its objects retain an actual topological group
and an actual jointly continuous action on a topological space. A morphism
retains a continuous group homomorphism and an equivariant continuous space
map, both in the source-to-target direction. The motivating convention is
Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
1996 manuscript), section 1.1, printed/PDF pages 2–3. The assertion on page 3
that analytic spaces with operators form a fibered category motivates this
derived topological prerequisite.

`groupForget` retains the original topological operator group and sends each
arrow to its existing continuous group homomorphism, with values in
`Langlands.Topology.TopologicalGroup`. Identity and composition are preserved
by extensionality of continuous homomorphisms.

For any continuous homomorphism `f : H → X.groupType`, `restrict X f` uses
Mathlib's `ContAction.res TopCat f`. This retains the original space and
replaces the action of `h` by the action of `f h`. Mathlib proves joint
continuity by composing the original action with the continuous map
`(h, x) ↦ (f h, x)`. The canonical arrow `restrictionMap X f` has group
component `f` and identity continuous space map. Its equivariance follows
from the restricted action formula.

Identity restriction and successive restriction have comparison isomorphisms
whose group and space components are identity maps. The category laws and
equivariance of these comparisons follow directly from the action formulas.
`restrictionMap_comp` identifies the full successive canonical arrow with
the canonical arrow for the composite, after this comparison.

For an actual arrow `h : Z → X` and a continuous homomorphism
`k : Z.groupType → H` satisfying `f.comp k = h.groupHom`,
`restrictionLift f h k hgroup` has group component `k` and the original
continuous space map of `h`. Substitution of the group equality into
`h.equivariant` proves its equivariance for the restricted action.
Composition with `restrictionMap X f` recovers the complete arrow `h`.
Conversely, a prescribed group component and this factorization determine
both components of the lift: the group component is prescribed and the
space component follows by projection of the factorization and composition
with the identity space map. This proves `restrictionLift_unique` and
`restrictionLift_existsUnique`. `restrictionHomEquiv` expresses the same
construction as an equivalence between the morphism sets over the specified
group maps.

`restrictionMap_isStronglyCartesian` converts this full unique-lift property
to Mathlib's `Functor.IsStronglyCartesian`, translating `IsHomLift` into
equality of the actual continuous group homomorphisms. The factorization
and uniqueness concern the entire arrows, including their continuous space
maps. `groupForget_isFibered` applies Mathlib's constructor from strongly
Cartesian lifts. It therefore supplies Cartesian lifts and composition
closure in Mathlib's definition of a fibered category.

Neither a fibration nor a desired lift is assumed as an object field. Space
carriers have universe `u`, independently of the operator-group universe
`v`. The continuous group map need not be injective, open or surjective.
There is no separation or local compactness hypothesis on the spaces.

The original source is registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`;
the PDF member has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The source supplies the operator-group convention and analytic motivation;
the actual topological construction and proof here are internally derived
from Mathlib's continuous actions and the published varying-group category.
This module defines no analytic spaces, analytic automorphism topology,
analytic atlases, étale morphisms or sites. Its role is to provide the
continuous-action target for compatibility with the actual quotient-spectrum
fibration.
