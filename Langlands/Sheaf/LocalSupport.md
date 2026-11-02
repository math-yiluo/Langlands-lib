# Compact sections from actual local vanishing

Author: Worker 13. This is an internal reformulation of the existing ordinary
topological support construction. It uses genuine neighborhood restrictions
and proves agreement with the existing stalk construction where its universe
parameters apply.

The space `X`, commutative ring `R`, and module category have independent
universes `u`, `r`, and `w`. The input `F` is any module-valued presheaf on the
ordinary opens of `X`. No sheaf condition is required for these constructions.
`restrict` is its actual map from the largest open to the named open.
`VanishesNear F s x` means that this restriction is zero for some open
neighborhood of `x`. `support` is the complement of this local vanishing locus.
These are definitions using the original presheaf, not supplied support data.

Functoriality of restrictions proves `restrict_of_le` and
`restrict_zero_of_le`. One vanishing open works at all its points, proving
closedness of support. The intersection of two vanishing neighborhoods works
for the sum of sections; a vanishing neighborhood also works after scalar
multiplication. These facts prove the support containment laws and that every
compactly supported section belongs to the actual `submodule` of global
sections. Closedness ensures that the smaller supports used in these
submodule proofs remain compact; no Hausdorff assumption is imposed.

Naturality of a genuine presheaf morphism proves `vanishesNear_map` and the
support containment for its actual global component. Restricting this component
constructs `map` on compact sections, the `presheafFunctor` to modules, and its
natural `inclusion` into global sections. No support-preservation or exactness
hypothesis is supplied as an extra field.

The `StalkComparison` section specializes to a ring and module carrier in the
space universe, as required by the existing Mathlib-based stalk construction.
`vanishesNear_iff_germ_zero` proves that a zero neighborhood restriction has
zero germ and that a zero germ is witnessed by an actual neighborhood. The
first direction uses compatibility of germ maps with restriction and their
zero-preservation. The second uses Mathlib's germ equality criterion for the
section and zero. Negating this equivalence gives `support_eq_stalkSupport`;
extensionality gives `submodule_eq_stalkSubmodule`. Thus the local definition
agrees with the existing support and compact-section submodule wherever that
stalk implementation applies. No generalized stalk or universe equivalence
is assumed or constructed.

The provenance is internal: the module reuses `Langlands.Sheaf.CompactSupport`
and its pinned Mathlib stalk, restriction, compactness and module APIs. It
makes no new original-literature assertion. The new general local definition
avoids identifying the independent original universes, while its explicit
stalk comparison has the stated aligned universes. Moving-space equivariance,
locally constant function comparison, smoothness, analytic or etale comparison,
derived functors and Harris specialization remain separate obligations.
