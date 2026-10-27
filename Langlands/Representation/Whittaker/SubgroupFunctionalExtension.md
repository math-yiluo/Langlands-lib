# Functional extension from a subgroup representation

Author: Worker 643.

This is an internal consequence of the published character-localization
exactness and coefficient-image constructions. It uses no external source
theorem beyond those already implemented in its imported modules.

`functionalsRestrictionEquiv` identifies the character-equivariant
functionals for an ambient representation with those for its restriction
to the acting subgroup, localized at that subgroup's top subgroup.
Both directions keep the same linear functional. The covariance conditions
differ only by the redundant top-subgroup subtype.

`isLimitOfCompactSubgroups_top` transports compact containment along the
homeomorphism between the top subgroup of `U` and `U`. Given a compact set
in the top subgroup, it maps that set into `U`, applies the given compact
containment condition, and pulls the resulting compact subgroup back.

For a smooth complex representation `rho` of a topological group `G`,
let `U` satisfy compact containment and let `theta` be locally constant
as a complex-valued function. Suppose `tau` is a representation of `U`,
and an injective `U`-intertwiner maps it into `rho` restricted to `U`.
Every `theta`-equivariant functional on `tau` extends to a functional
on `rho` with the same `U`-equivariance. The proof restricts smoothness
to `U`, applies the published
`functionalsComap_surjective_of_smooth` to its top subgroup, and removes
the top-subgroup subtype through `functionalsRestrictionEquiv`.

`extendSubgroupFunctional` chooses one such extension. Its evaluation
lemma states that it agrees with the original functional on every
vector in the injected representation. The extension need not be unique.
The injection is only required to intertwine the action of `U`.

`exists_coefficientModel_extension` takes a vector `w` of `tau` and
a family of ambient elements `g(t)`. If every translated vector
`rho(g(t))(i(w))` has a specified preimage `w'(t)`, the chosen extension
has an actual coefficient in `coefficientModel rho L` with values
`L(rho(g(t))(i(w))) = ell(w'(t))`. The coefficient is constructed as
`modelMap rho L (i(w))`; it is in the actual image by construction.
`exists_whittakerSet_extension` specializes this result to the standard
upper-unipotent character and the published Rankin--Selberg
`whittakerSet`. This final specialization assumes a field, as required by
the published definition of that set; the preceding constructions apply
to arbitrary topological groups.

The field, ambient group, coefficient modules, and index set have
independent universes. No irreducibility or faithful coefficient
realization is needed. The injection's injectivity, ambient smoothness,
compact containment, local constancy, equivariance of the original
functional, and the specified translated preimages remain explicit
hypotheses.

This helper does not prove the JPSS two-block extension proposition.
It constructs neither the compact cell sections nor their subgroup
action, scalar integral, character covariance, Fourier transform, or
determinant factor. Those inputs must be proved before applying it to
the actual induced representation.
