# Actual mirabolic coefficient and support adapters

This internal construction connects the actual matrix predicates in
`WhittakerTypeKirillovStatement` with the published `MirabolicModels` functions.
It proves no minimality or Kirillov surjectivity theorem. Its definitions and
elementary laws are derived from the published coefficient, smooth-part,
induction, and mirabolic subgroup constructions.

The coefficient intertwiner sends a vector `v` to the function
`q ↦ ℓ (ρ q v)` on the actual last-row mirabolic group. Covariance uses the
published standard character without inversion or normalization, and equivariance
uses right translation. Pullback along the continuous subgroup inclusion
preserves smoothness. The smooth-part lift therefore places the coefficient
map in smooth induction. Its invariant image is nonzero when the functional is
nonzero, as evaluation at the identity recovers the functional.

The restriction constructor takes an ambient function, its left unipotent
covariance on the mirabolic subgroup, and a single ambient open right
stabilizer. The inverse image of that stabilizer in the mirabolic group is open.
For compact support, intersect the supplied ambient compact witness with the
closed mirabolic subgroup. If `q = u c`, both `q` and `u` lie in the mirabolic
group, so `c = u⁻¹ q` does too. The projected support is contained in the compact
image of this intersection in the actual left coset space. It is closed by
`Induction.isClosed_quotientSupport`, so is compact. The resulting compact
function evaluates to the original ambient function at every mirabolic matrix.

These arguments apply over a commutative topological ring, with Hausdorffness
needed only for compact support. They retain independent field and vector-space
universes and every `n : ℕ`, including `n = 0`. The constructors form the
elementary adapter layer for the JPSS (1983), Section 2.2, printed page 386
target and the Bernstein–Zelevinsky (1976), Proposition 5.15(c), printed pages
49–50 minimality target already documented in their published statement pairs.
No new assertion from either source is used here.
