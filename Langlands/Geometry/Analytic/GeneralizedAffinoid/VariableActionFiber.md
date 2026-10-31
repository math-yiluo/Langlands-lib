# Fixed-group quotient actions and the actual group-forget fibers

For an ultrametric normed field `K` and an actual bundled topological group `G`,
this module identifies the existing category `NormContinuousSpace K G` with
Mathlib's standard fiber `Functor.Fiber groupForget G`. The former is the
opposite category of norm-continuous `G`-actions on finite positive-polyradius
Tate quotients by closed ideals. Its geometric arrows are contravariant bounded
algebra maps commuting with the fixed group action. The standard fiber consists
of variable-group quotient actions whose bundled operator group equals `G`,
and arrows lifting the identity of `G`.

The motivating convention is Berkovich, *Étale equivariant sheaves on p-adic
analytic spaces* (unfinished 1996 manuscript), section 1.1, printed/PDF page 3,
first paragraph before Example 1.1.3. It defines fixed-group morphisms using
the identity operator-group map and denotes the fiber over `G` by `G-An`.
Registered source:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
PDF member *Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf*, SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The exact equivalence for the concrete quotient category is internally derived
from its definitions and Mathlib's fiber construction.

`ofFixed_comp_groupForget` proves that the existing fixed-group inclusion
composes strictly to the constant group functor. `ofFixedToFiber` uses
`Functor.Fiber.inducedFunctor` to factor that inclusion through the standard
fiber. Composing it with `fiberInclusion` recovers `ofFixed` by reflexivity.
Thus its objects retain the original quotient action, and its arrows retain the
original bounded algebra map with identity group component.

`ofFixedFiberPreimage` constructs an inverse on each morphism set. For an arrow
between images of fixed-group objects, `IsHomLift.eq_of_isHomLift` proves that
its group component equals the identity continuous homomorphism. Substituting
this equality in its existing equivariance equation gives a morphism of the
fixed-group algebra actions. Taking the opposite gives the required geometric
arrow and preserves its bounded algebra map. `ofFixedToFiber_map_preimage`
and `ofFixedFiberPreimage_map` prove both inverse laws by extensionality of
complete variable-group arrows and fixed-group bounded algebra maps,
respectively. These give the `Full` and `Faithful` instances.

`ofFixedToFiber_obj_surjective` eliminates the equality identifying an arbitrary
fiber object's bundled group with `G`. The opposite of its retained algebra
action then maps to that same fiber object; structure and subtype
extensionality prove equality. Consequently the functor is surjective on
objects, hence essentially surjective, and `ofFixedToFiber_isEquivalence`
combines these properties. `fixedGroupFiberEquivalence` packages the resulting
equivalence using `asEquivalence`. Its forward functor is the concrete functor
above; its categorical inverse uses Mathlib's choice construction.

`fixedGroupFibers` supplies the existing fixed-group categories and inclusions
as `HasFibers groupForget`. Its equivalence field is exactly the proved
`ofFixedToFiber_isEquivalence`. It is an explicit, instance-reducible definition,
so a consumer can choose it locally without installing a competing global
`HasFibers` instance.

The coefficient field has universe `u`, and the operator-group carrier has
independent universe `v`. The only field assumptions are `NormedField K` and
`IsUltrametricDist K`; the group has its original topology and continuous group
operations. This is quotient-category infrastructure for the analytic
construction. General analytic atlases and étale sites, and a comparison of
norm-orbit continuity with Berkovich's analytic automorphism topology, remain
separate obligations.
