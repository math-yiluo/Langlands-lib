# Regular centralizers and torus norm images

The module identifies the centralizer of a regular point of a rational Weyl torus
with the torus subgroup. If `a` is the regular element used to define the torus,
all its points commute by `glCentralizer_mul_comm`. For a regular point `γ` of
the same torus, its centralizer is also commutative and contains `a`, so each of
its elements centralizes `a` and belongs to the torus.

After base change to a finite reduced algebra, membership in `T.points E`
implies commutation with the base change of `γ`. In the other direction,
`commute_of_commute_baseChange` shows that any element commuting with the
base change of `γ` commutes with every base-changed rational torus point.

For an exact norm equality `N(δ) = γ_E`, applying the entrywise automorphism to
both sides gives `γ_E = δ⁻¹ * γ_E * δ`. Here `γ_E` is fixed and the cyclic
automorphism raised to its degree is the identity. The resulting commutation
puts `δ` in `T.points E`. An ambient norm can first be made exact by twisted
conjugation using its association witness. Conversely, a torus lift with
exact norm is an ambient norm with association witness `1`.

These are consequences of the Library's centralizer and cyclic norm identities.
The norm-image equivalence identifies the regular integration domain of
Henniart–Lemaire (2011), II.2.10, formula (1), with the ambient norm condition
used by concordance.
