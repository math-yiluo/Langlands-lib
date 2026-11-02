# Full-field diagonal in actual curve-place adeles

Authored by Worker 208 using the published `CurvePlaceFinitePolesProof`
and `CurvePlaceAdeleCongr` modules.

For fields k and F in an arbitrary common universe, with k perfect and a
specified compatible finite extension of RatFunc k giving the one-variable
function field structure, the
coordinate maps to all actual curve-place completions define a unital
ring homomorphism from the whole field to `CurvePlaceAdeleRing k F`.
The finite-poles theorem proves the needed cofinite integrality rather
than assuming it. These diagonal maps give the F-algebra and k-algebra
structures, with their compatible scalar tower.

The local completion map reflects and preserves integrality. Consequently,
a diagonal field element belongs to a level exactly when it belongs to
the actual outside-S integers, and every field element belongs to some
such integer ring. The full diagonal restricts to the previously published
level diagonal.

The specified k-algebra presentation equivalence commutes with the full
diagonal, by the published local completion formula. Hence the adelic
ring equivalence also respects the diagonal k-action and upgrades to
a k-algebra equivalence.

This is derived arithmetic infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Section 2,
printed p.1: the adelic ring, its open levels, and the maps from outside-S
integers. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The full diagonal is constructed from the finite-poles theorem, including
finite perfect constant fields and inseparable supplied presentations.
The local integrality equivalence itself requires only fields k and F
with Algebra k F. Global-place realization, local compactness, identity
and composition laws for the comparisons, and geometric point-space
comparisons remain separate obligations. This contribution does not
assert injectivity or discreteness.
