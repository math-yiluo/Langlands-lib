# Rank-one coordinate origins and depths

This internal comparison is derived from the existing apartment action, the
opposite-factor-pair displacement theorem, and integer centralizer compatibility
V6. It applies over an arbitrary field `k` to a supplied apartment with these
properties. It does not construct an algebraic rank-one map or assert that its
Weyl matrix normalizes the prescribed maximal split torus.

`KPApartmentData.normalizerMidpoint n x` defines the midpoint of `x` and
`n • x`, a candidate origin used by the rank-one comparison.
`smul_normalizerMidpoint_eq_self` proves that this origin is fixed when the
square of `n` fixes `x`. The underlying
`KPApartmentData.smul_midpoint_eq_self_of_square` says that, if a normalizer
point `n` has `n • (n • x) = x`, it fixes the midpoint of `x` and `n • x`.
The implemented proof applies `AffineEquiv.map_midpoint` to the supplied
`normalizerAffineEquiv`, replaces the second iterate using the hypothesis,
and uses symmetry of the midpoint.

`KPApartmentData.val_eq_half_centralizer_of_pair` assumes connected reductivity,
maximal splitness, and full integer `IsOmegaCompatible` for the supplied
centralizer datum `C`. Let `u` be a nonidentity point of the root group of an
actual relative root `a`, and let `p` be an actual `IsOppositeFactorPair` for
`u`. Suppose its normalizer representative `p.1 * u * p.2` equals
`C.toNormalizer z * n`, where `n` fixes an apartment point `x`. Then

`x.val a u = eval S a (centralizerValuation v C.s C.bijective z).toAdd / 2`,

with the real right hand side coerced to `WithTop ℝ`.

The proof first uses the root-valuation axiom `eq_top_iff` to make the value
finite. `rootForm_oppositeFactorPair_vsub` identifies the root form of the
representative's displacement as minus twice this value. The factorization,
fixed-point hypothesis, and `IntegerValuation.IsOmegaCompatible.smul_eq_vadd`
express the same displacement as the centralizer translation. The identity
`centralizerTranslation_toAdd` changes it to the negative of the positive
centralizer valuation. The resulting equality of real numbers gives the
formula by linear arithmetic.

Both results are internal adapters between published interfaces. Their
mathematical content follows from the named Library theorems; no new
source-level assertion or additional existence premise is introduced.
