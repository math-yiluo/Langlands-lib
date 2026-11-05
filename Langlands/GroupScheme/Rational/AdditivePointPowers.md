# Compact powers of actual additive points

This is an internal auxiliary construction for the anisotropic spectral-integrality
proof. It uses the existing polynomial-point homeomorphism, the canonical topology
on actual identity-test rational points, and Mathlib's compact valuation balls.
No external group-theoretic assertion is used.

For a commutative ring `R`, `VectorGroup.rationalPointOfCoordinates R n a` is the
actual rational point of the vector group obtained from polynomial evaluation at
`a : Fin n → R`. Its underlying map is the spectrum of `MvPolynomial.aeval a`.
Naturality of the canonical global-sections isomorphism shows that its `i`-th
`VectorGroup.coordinates` value is the image of `a i` in the global sections of
`Spec R`. Consequently its `k`-th power has scalar coordinates `k • a`. The tuple
whose entries are all one agrees with the exact point
`(VectorGroup.coordinates _ _ _).symm (Multiplicative.ofAdd (fun _ => 1))`.

If `R` is a topological ring, the map from scalar coordinate tuples to rational
points is continuous. The proof composes the inverses of the polynomial-point,
spectrum-algebra-point, and identity-test-point homeomorphisms, using the same
underlying equivalences as the construction.

For a nonarchimedean local field `F`, every natural number has valuation at most
one: this follows by induction from the ultrametric addition inequality. The
closed valuation ball of radius one is compact. For a fixed tuple `a`, its image
under the continuous map `x ↦ rationalPointOfCoordinates F n (fun i ↦ x * a i)`
is therefore a compact set containing every nonnegative power of the associated
point, including power zero. Specializing to the tuple of ones gives compact
containment for the exact generator above.

Finally `exists_isCompact_powers_map_coordinateOne` sends this compact set through
any vector-group morphism into an affine group scheme. Functoriality of the
canonical rational-point topology makes its image compact, and the point
homomorphism preserves all powers. This result works at arbitrary field universe,
for every `n` including zero, in both mixed and equal characteristic. It asserts
compact containment of these powers, without asserting compactness of the whole
target group or the general anisotropic reductive theorem.
