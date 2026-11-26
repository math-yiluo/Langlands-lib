# Archimedean arithmetic and adelic rational finiteness

`ArithmeticHarishChandraFinitenessStatement` is the fixed-data finiteness
assertion on the actual archimedean group `G(F_∞)`. A finite adelic point
`b` and compact open level `L` specify `arithmeticInfiniteLevelGroup F G L b`.
It is the image at infinity of the rational points whose finite component
belongs to \(b L b^{-1}\). For a fixed maximal compact subgroup \(H\), a
finite-dimensional subspace of functions on \(H\), and a cofinite ideal of the
archimedean enveloping center, the statement bounds the span of the smooth
functions invariant on the left by that arithmetic subgroup. Every function
has moderate growth, is killed by the ideal, and has every right compact
profile in the fixed subspace. The growth bound uses the normalized matrix
height at \((x,1)\), so at positive matrix rank its finite factors are one.

`RationalHarishChandraFinitenessStatement` gives the corresponding bound on
`G(F) \ G(𝔸)`. The finite right level here is any open subgroup and the
moderate-growth condition is the adelic one. The same ideal kills every
archimedean slice. Both statements use the actual point groups and their
existing plot-smooth center action at universe `u`.

`rationalHarishChandraFiniteness_of_arithmetic` proves the adelic assertion
assuming the archimedean arithmetic one. It intersects the open finite level
with a compact open subgroup. The finite-translate Siegel height reduction
provides a compact set containing the finite component of some rational
translate of every point. The compact set meets finitely many cosets of the
smaller level. At each representative \(b\), the infinite slice is invariant
under the specified arithmetic subgroup: multiplying on the left by a
rational point moves the finite component by an element of \(b L\), which
can be removed using right-level invariance. The archimedean slice is smooth
and annihilated by the same ideal by the adelic hypotheses. Its growth bound
uses the single right translate by the included finite point \(b\). Its
compact profile is the original compact profile at \((x,b)\). The joint
restriction is a linear map into the finite product of the slice spans.
Rational and finite-level invariance recover every original value from
these slices, so the map is injective.

The statements use the arithmetic quotients and finiteness in Borel–Jacquet,
*Automorphic forms and automorphic representations* (1979), §§1.3, 1.6–1.7,
4.2–4.3, printed pp. 190–191 and 195, PDF pp. 185–186 and 190. The registered
source `borel-jacquet-1979-automorphic` has SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
In §4.3 (1), \(G_\infty\) is the real group of the restriction of scalars
and \(\Gamma_b\) is obtained from \(G(F)\cap b G_\infty L b^{-1}\).
Conjugating a compact open level preserves the arithmetic condition, since
any two compact open subgroups are commensurable. The compact profiles used
here give one common finite set of compact types by taking the span of all
profiles and using its left-translation invariance, as in the explanation
of compact types in `GroupSchemeHarishChandraFinitenessStatement`.
The proof implements the restriction and recovery direction of §4.3 (2).
The archimedean arithmetic finiteness proposition is a premise of the proof.
