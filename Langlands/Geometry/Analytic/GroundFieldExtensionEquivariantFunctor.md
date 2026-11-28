# Equivariant analytic scalar extension on morphisms

For an isometric ground-field embedding `e : K ⟶ L`,
`scalarExtendedFunctor e` applies localized analytic scalar extension to
objects and maps and includes them into `SpaceOverField` over `L`.
`scalarExtendedFunctor_projection` identifies its natural map to the original
objects, using the identity and composition comparisons for scalar extension.

An isometric automorphism of `L` over `K` acts on each extended space by the
Cartesian lift of the inverse field automorphism. For a map over `K`, the two
possible composites of its extension with the lifts lie over the same field
map and have equal composites with the projection. The projection's
Cartesian property proves `scalarExtendedFunctor_coefficientLift`. The
functor `coefficientEquivariantScalarExtension` packages the resulting
objects and equivariant maps in the category of actions of the coefficient
group. Restriction of the group along the action on a completed algebraic
closure gives the corresponding absolute Galois actions and equivariant maps.

The description of analytic scalar extension and its projection is from
Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
§1.4, printed pp. 29–30 (PDF pp. 26–27). The retained original
`berkovich-1993-etale-cohomology` has SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The category with a specified ground field and the canonical Galois action
are described in Berkovich's *Étale equivariant sheaves on p-adic analytic
spaces* (unfinished 1995–1996 manuscript), §1.1 and Example 1.1.1(i),
printed and PDF pp. 1–2. The retained literature folder
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
has SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
and its PDF member has SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
