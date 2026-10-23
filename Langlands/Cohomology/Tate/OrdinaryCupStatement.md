# Normalization and naturality of the ordinary cup

Author: Worker 45.

`Langlands.Tate.OrdinaryCupLaws` is the exact target for two laws of the
published `ordinaryCup`. It concerns Mathlib's actual ordinary group cohomology
and the product descended from the explicit inhomogeneous cochain cup. The
ring `R`, group `G`, and representation carriers share an arbitrary universe
`u`. The assumptions are `CommRing R` and `Group G`; neither finiteness nor
flatness is assumed.

The first clause says that the product of the degree-zero classes of invariant
vectors `a` and `b` is the degree-zero class of `φ(a,b)`. The classes are
specified using the inverses of Mathlib's `H0Iso` identifications. Its output
is in degree `0 + 0 = 0`. This is ordinary degree-zero cohomology, so the
statement makes no quotient by norms.

The second clause concerns coefficient maps `f : A → A'`, `g : B → B'`, and
`h : C → C'` which intertwine the two given equivariant pairings: for all
vectors, `h(φ(a,b)) = φ'(f(a),g(b))`. In every pair of natural degrees `p,q`,
the map induced by `h` sends the ordinary cup to the ordinary cup of the
classes mapped by `f` and `g`. All three induced maps are Mathlib's actual
`groupCohomology.map` with the identity group homomorphism. In particular this
includes postcomposition of the coefficient pairing, by taking `f` and `g`
to be identities; no assumed cup operation is quantified over.

This is an internal compatibility specification for the published cochain
construction. Its degree-zero formula is the empty-tuple specialization of
`ordinaryCupCocycles_apply`, and its naturality requirement expresses
postcomposition of that formula and passage to actual cocycle classes. Serre,
*Local Fields* (1979), VIII §3, Proposition 5(i)–(ii), printed p.131 (PDF p.137),
provides the naturality and invariant-vector normalization conventions for
Tate products; printed p.132 (PDF p.138) fixes equivariant coefficient
pairings. These pages concern finite-group Tate cohomology. The present
arbitrary-group ordinary-cohomology formulation, including its commutative-ring
linear refinement and explicit `H0Iso` maps, is an internal target for the
independently constructed ordinary product, not a claim that those pages
state this broader result. The file states the two laws and contains no proof.
The tensor boundary laws and the ordinary-to-Tate comparison are separate
targets.
