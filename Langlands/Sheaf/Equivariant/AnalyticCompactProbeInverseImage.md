# Inverse image and invariant sections for compact-probe quasi-étale sheaves

Let `X` be an analytic `GSpace` over a complete ultrametric normed field.
The equivariant site uses families of equivariant morphisms and the twisted
site uses the ordinary test objects with arrows labelled by the action.
Both topologies are constructed from the compact-probe rule.
The ground field, spaces and group have universes `u`, `v` and `z`.
The commutative coefficient ring and modules use universe
`max u (v + 1) z uR`, large enough for the site and the Kan extension.

The geometric input `HasImagePullbacks` concerns the forgetful functor on
equivariant test objects. With this input the forgetful functor is continuous,
as is its composite with the embedding in the twisted site. The
natural-action construction forms `compactProbeQuasiEtaleInvariantSheaf`
using actual invariant sections on each equivariant test object. The
underlying presheaf is canonically identified with the original
`NaturalAction.sheafInvariantFunctor`. `compactProbeQuasiEtaleInverseImage` is the
sheafification of the left Kan extension of the inflated coefficient
presheaf. The size lemmas and Mathlib give the needed sheafification and the
existing action construction supplies the left Kan extension. The
natural-action adjunction restricts to these sheaf categories. Its left
image lands in sheaves on the twisted site. Discreteness of its local
sections is a separate comparison property.

The source of the construction is Berkovich, *Étale equivariant sheaves on
p-adic analytic spaces* (1995–1996), §1.2, printed p. 3, which describes the
inverse image by a colimit followed by sheafification, and §1.4, Theorem
1.4.2, proof A.1 and A.4, pp. 8–9, which uses this colimit and invariant
sections. The implementation is the module-valued version using the
Library's compact-probe sites.
Literature ID `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The retained PDF *Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf*
has SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
