# Fixed-group continuous actions and the actual group-forget fibers

For an actual bundled topological group `G`, this module constructs an
equivalence from Mathlib's category `ContAction TopCat G` to the standard fiber
`Functor.Fiber groupForget G` of the varying-group continuous-action category.
The fixed-group objects have their original jointly continuous actions, and
their arrows are continuous equivariant maps. A standard fiber object is a
varying-group action whose bundled group equals `G`; a fiber arrow lifts the
identity of `G`.

The motivation is Berkovich, *Étale equivariant sheaves on p-adic analytic
spaces* (unfinished 1996 manuscript), section 1.1, printed/PDF page 3, first
paragraph before Example 1.1.3. It describes fixed-group morphisms by an
identity operator-group component and denotes the fiber over `G` by `G-An`.
Registered source:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
PDF member *Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf*, SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The present continuous-space equivalence is an internally derived topological
prerequisite, using the existing concrete category and Mathlib's fiber.

`ofFixed_comp_groupForget` proves the strict constant-group equality for the
existing fixed-group inclusion. `ofFixedToFiber` applies
`Functor.Fiber.inducedFunctor` to it. Composing with the fiber inclusion
recovers `ofFixed` by reflexivity, retaining the original action and continuous
space map and using the identity group map.

`ofFixedFiberPreimage` constructs an inverse on each morphism set.
`IsHomLift.eq_of_isHomLift` identifies the group component of a fiber arrow
between these images with the identity. Substitution into its equivariance
equation yields an actual fixed-group equivariant map, with unchanged
continuous space map as recorded by `ofFixedFiberPreimage_spaceMap`.
`ofFixedToFiber_map_preimage` proves one inverse law by extensionality on the
group and space components. `ofFixedFiberPreimage_map` proves the other by
extensionality of fixed-group action morphisms. The resulting functor is full
and faithful.

`ofFixedToFiber_obj_surjective` eliminates the equality of bundled groups in
an arbitrary fiber object. Its retained action then gives a fixed-group object
mapping to that same fiber object; structure and subtype extensionality prove
equality. Surjectivity on objects supplies essential surjectivity, and the
full, faithful and essentially surjective functor is an `IsEquivalence`.
`fixedGroupFiberEquivalence` packages it with `asEquivalence`, whose inverse
uses Mathlib's choice construction. `fixedGroupFibers` explicitly supplies the
existing fixed-group categories as `HasFibers groupForget`. It is an
instance-reducible definition that a consumer can choose locally.

Space and group carriers have independent universes `u` and `v`. The action
uses the original topology on the space through the identity `TopCat`
self-forgetful instance. The group has its original topology and continuous
operations; no separation or local compactness is assumed. These constructions
concern jointly continuous topological actions. General analytic atlases,
étale sites, and comparison with the analytic automorphism topology of
Berkovich's manuscript remain separate constructions.
