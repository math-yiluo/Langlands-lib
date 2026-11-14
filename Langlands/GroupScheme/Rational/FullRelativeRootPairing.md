# Full actual-root pairings on the rational root span

This internal supporting construction removes an assumed root-system property
from a root pairing with the full actual-root image. The pairing may have an
arbitrary rational coroot module and any perfect pairing permitted by
`RootPairing`; it need not be specified as evaluation on the dual.

The roots span the actual rational root span by its definition. For a split
torus in an affine group locally of finite type over a field, its actual Lie
weights form a finite set. The full-image equality and injectivity of the
root embedding therefore make the pairing's index type finite.
`fullRelativeRootImageFintype` constructs a finite enumeration of this type;
it makes no canonical choice of ordering. Mathlib's
finite root-pairing result over the ordered field of rational numbers says
that the roots span if and only if the coroots span. These two span equalities
prove `P.IsRootSystem` in `isRootSystem_of_full_relativeRoot_image` without
any crystallographic or reducedness premise.

For an almost-simple group, smoothness supplies the local finite-type
hypothesis. The constructed root-system property then allows the invariant
actual-root partition result to prove irreducibility when the maximal split
torus has a nonempty actual root set. This works over every ground-field
characteristic, including 2. The proof is an internal deduction from actual
Lie-weight finiteness, the definition of the rational root span and Mathlib's
root-pairing linear algebra, followed by the commuting-partition theorem.
It does not prove the local affine-diagram target.
