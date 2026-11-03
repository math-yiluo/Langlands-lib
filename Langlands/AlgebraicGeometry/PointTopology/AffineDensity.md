# Elementary Zariski density toolkit for actual rational points: proof

`rationalPointDensityToolkit` proves the exact proposition
`RationalPointDensityToolkitStatement` in
`Langlands.AlgebraicGeometry.PointTopology.RationalDensityStatement`,
at arbitrary universe `u`. The individual lemmas are reusable for actual
schemes and actual morphisms over `Spec k`.

`dense_polynomial_evaluation_primes` tests Zariski density on principal
basic opens of `Spec (MvPolynomial n k)`. Nonemptiness implies that the
defining polynomial is nonzero. Mathlib's `MvPolynomial.funext` over an
infinite field gives a vector where the polynomial does not vanish.
The prime obtained by pulling back the zero ideal under evaluation at
that vector lies in the basic open.

`hasDenseRationalPoints_polynomialSpec` realizes each of these evaluation
primes as the image of an actual morphism `Spec k → Spec (MvPolynomial n k)`
over `Spec k`. The equality `eval ∘ C = id` verifies that the morphism
is over the field. `hasDenseRationalPoints_affineSpace` then transports
density through Mathlib's actual `AffineSpace.SpecIso`, whose inverse
commutes with the structural morphisms. Every index type `n : Type u`
is allowed, including the empty type.

`hasDenseRationalPoints_of_denseRange` uses continuity to send a dense set
to a dense subset of a target when the morphism has dense image. It checks
membership by composing the actual source rational point with the
given morphism over `Spec k`. This lemma needs only a field, not its
infinitude.

`hasDenseRationalPoints_open` first takes the preimage of the dense set
under the open-subscheme inclusion, an open map. If a rational point
meets the open, its entire image lies in the open because the prime
spectrum of a field has one point. The universal property of an open
immersion factors the rational point through the open subscheme; the
factorization remains over `Spec k`. Injectivity of the inclusion gives
the required point in the open. The argument includes empty opens and
requires no finiteness or separation hypotheses.

The final theorem packages these three conclusions in the order of
the exact statement. This is an elementary derived proof of the
geometric toolkit used in the unirationality route to Milne,
*Algebraic Groups* (2017), Theorem 17.93(b). It proves no additional
torus or reductive group structure theorem.
