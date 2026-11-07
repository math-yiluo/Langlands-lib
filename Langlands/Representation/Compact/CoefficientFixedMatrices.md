# Fixed matrices under coefficient specialization

The construction `specializedBasis` takes a basis over a commutative
coefficient ring `R` of the fixed vectors of a smooth complex representation
`ρ`. The coefficient action on `ρ` commutes with its complex scalars and group
action. A complex intertwiner `f` into another smooth representation `τ`
satisfies the scalar evaluation law for a supplied algebra map `R → ℂ`.
The full scalar extension of `f` is assumed bijective. The existing
`fixedScalarExtensionEquiv` then identifies the scalar extension of the
actual fixed module, at a compact open subgroup `K`, with the actual
`K`-fixed space of `τ`.

Extend the supplied coefficient basis to `ℂ` and transport it through this
canonical equivalence. This defines `specializedBasis`; its index type is
unchanged and need not be finite for the construction. The group,
coefficient ring, two representation carriers and index type have
independent universes.

The theorem `specializedBasis_apply` identifies each resulting basis vector
with the actual evaluation `f` of the original vector.
`specializedBasis_repr` proves that the coordinates of any evaluated fixed
vector are the evaluated coefficient coordinates. Its proof applies the
inverse of the fixed scalar-extension equivalence to the vector, obtaining
the pure tensor `1 ⊗ v`, and uses the standard coordinates of a scalar-extended
basis.

When the index type is finite and a left Haar measure is supplied,
`specializedBasis_fixedMatrix` computes every entry of the actual
`UnitarizabilityContinuation.fixedMatrix` in this basis. The entry at `g,i,j`
is the image under `R → ℂ` of the `i`-th coefficient coordinate of the
normalized compact-fixed projection of `ρ(g)(e(j))`. The intertwining law
for `f` moves the group action across evaluation, and naturality of the
normalized Hecke projection moves the projection across it. The coordinate
formula then gives the claim. Both sides use the published actual Hecke
projection; no comparison with a different averaging operator is needed.

This is an internal derived construction from the published coefficient
specialization and Hecke projection results and the standard tensor-product
basis. It supplies a matrix formula under an explicit scalar-extension
bijection and coefficient basis. Existence of these data for a given family,
continuity of the coefficient evaluations, detection of all irreducible
subquotients and nonemptiness of an irreducibility locus remain separate
obligations.
