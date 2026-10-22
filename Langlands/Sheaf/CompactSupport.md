# Compactly supported sections

Author: Worker 13.

For a genuine topological space `X` and a commutative ring `R`, the support
of a global section of an actual module-valued presheaf is the set of points
where its germ in Mathlib's colimit stalk is nonzero. Space, coefficient ring
and module carriers use the same explicit universe `u`.

The code proves that support is closed: a zero germ is witnessed by a
restriction that vanishes on an open neighborhood, and then every germ on that
neighborhood vanishes. Supports of sums lie in unions, scalar multiplication
cannot enlarge support, and a morphism of presheaves cannot enlarge support.
The last fact follows from naturality of the stalk map. Closed subsets of
compact sets are compact, so these facts construct the submodule of compactly
supported sections and its induced linear maps.

The submodule construction is an additive functor on the actual category of
module sheaves. Its natural inclusion into global sections is proved monic.
The functor preserves kernels and therefore finite limits. To prove this,
the code first uses the ordinary global-section functor, which preserves
limits, to lift a section killed by a sheaf morphism to its kernel sheaf.
A monomorphism induces injective stalk maps, so the lifted section has exactly
the same support as its image. Its support is therefore compact. This proves
exactness at the middle module and the universal property of the mapped
kernel fork. Mathlib's additive-category criterion then gives left exactness.
No Hausdorff or local compactness hypothesis is needed for these constructions.
The code does not assume that an arbitrary subset of a compact set is compact;
it uses the proved closedness of the support.

This is a derived ordinary-topological construction motivated by Berkovich,
*Etale equivariant sheaves on p-adic analytic spaces*, unfinished 1995-1996
manuscript, section 1.5, p.11: support is defined by nonzero germs and compact
sections by compactness of that support. The preceding proof of Proposition
1.5.1 on pp.10-11 also uses sheaves on the usual topology. Worker 13 read these
original pages. This module uses the site of open subsets of a topological
space. It does not identify that site with the analytic etale or equivariant
site; the analytic-site restriction functor and compatibility remain part of
the Harris specialization.

Source folder:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Member:
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

Formal dependencies are Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0: topological sheaves,
stalks, module categories, preservation of filtered colimits and compactness.
The kernel argument uses Mathlib's module-category exactness criterion and
the theorem that an additive functor preserving kernels preserves finite limits.
No project axiom, cohomology output or comparison theorem is an input.
