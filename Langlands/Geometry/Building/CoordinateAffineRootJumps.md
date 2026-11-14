# Actual affine-root membership from supplied coordinate depths

This internal helper connects supplied coordinate depth formulas with the
ordinary affine roots of `KPApartmentData`. It derives directly from the
published definitions and membership lemmas in `KPApartment`, together with
the published coordinate interfaces. It does not construct coordinate maps
or prove that an actual apartment has the supplied depth formulas.

For a group `P`, a function `depth : P → WithTop ℝ`, a subgroup `K`, and a real
number `r`, `CoordinateDepthJump depth K r` means that the closed depth ball
`{p | r ≤ depth p}` is not contained in the product of the strict depth ball
`{p | r < depth p}` with `K`. No valuation or subgroup-closure condition is
imposed on `depth`. When `K` is trivial, this predicate is equivalent to
attainment of the finite value `r`.

The generic apartment comparison assumes a relative root `a`, a group
isomorphism `e : P ≃* U_a(k)`, an apartment point `x`, equality
`x.val a (e p) = depth p` for every coordinate `p`, and identification of
the actual double-root subgroup with the image of `K`. For an affine
functional `ψ` with derivative `rootForm i a`, the closed-versus-strict
product inclusion in the definition of an ordinary affine root is
equivalent to its coordinate version. The proof transfers the two factors
of a product in each direction through `e`; injectivity recovers their
coordinate product.

If the reduced root forms distinguish relative roots, membership
`ψ ∈ D.affineRoots` is therefore equivalent to
`CoordinateDepthJump depth K (ψ x)`. The injectivity assumption identifies
the existential root direction in the published definition with `a`.

The unitary specialization assumes a split torus, a relative root `a`
whose double is a relative root, supplied `RootUnitaryCoordinates`, an
additive valuation `w` of their extension field, and the exact depth formula
at `x`. It identifies ordinary affine-root membership with the coordinate
depth jump for `depthA w` modulo the literal zero-first-coordinate subgroup.
The coordinate interface supplies the required image description of the
double-root subgroup. This bridge does not require conjugation invariance
of `w`, because the exact depth formula is a hypothesis.

The field specialization assumes a split torus, a relative root `a` whose
double is absent, supplied `RootFieldCoordinates`, an additive valuation `w`
of their extension field, and the exact formula
`x.val a (e t) = w t`. It gives membership if and only if some nonzero `t`
has `w t = ψ x`. Here the double-root subgroup is trivial; the generic
trivial-subgroup criterion gives an attained value, and the valuation of
zero is infinite, so its witness is nonzero.

Both specializations reuse the published
`Langlands.BruhatTits.SpecialCompact.rootForm_injective_of_split`. The
statements impose no field-characteristic, residue-characteristic or
residue-perfection conditions. They retain their explicit supplied-coordinate
and depth-equality hypotheses and do not prove the host quasi-split
indivisible-derivative-lift statement.
