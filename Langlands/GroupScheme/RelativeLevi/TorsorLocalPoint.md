# An affine étale local point of the Levi presheaf

This internal helper supplies a local point suitable for affine cocycle
descent. Over an affine base, a Zariski sheaf with sections on an étale
cover has a section on one affine surjective étale test scheme.

First the arbitrary local sections glue on the disjoint coproduct of the
cover components. Sheaf separation gives at most one section on an empty
test, so the sections agree on every overlap between distinct components;
monomorphy of a component inclusion handles overlaps within that component.
The coproduct maps surjectively and étale to the original base. The
published affine étale refinement theorem, using compactness of the base,
provides an affine test scheme mapping into that coproduct while still
covering the original base. Restrict the coproduct section to this test.

For the actual Levi presheaf, the published étale-local dynamic description
of a relative parabolic supplies the initial local points. The dynamic
centralizer represents an actual Levi subgroup, by the published dynamic
relative Levi theorem. This construction assumes only the Zariski sheaf
condition for assembling the local points; it does not assume a section
over the original affine base. The geometric provenance is Conrad,
*Reductive group schemes* (2014), the discussion after Definition 5.4.2,
p.174, and Corollary 5.4.6, p.178, source identifier
`conrad-2014-reductive-group-schemes`.
