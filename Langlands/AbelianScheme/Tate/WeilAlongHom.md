# Integral Weil pairings along actual homomorphisms to the dual

This internal construction pulls the existing integral Weil pairings back
in the second variable along an actual abelian-scheme homomorphism
`lam : A → A^dual`. The dual is the constructed
`dualAbelianSchemeFromEvaluation`. Its geometry, the inverse Poincare
bundle and evaluation, and the seven tensor/Picard propositions remain
explicit inputs. Inverse-limit pairings additionally retain the explicit
`RelativeFiniteWeilTransitionStatement`.

The finite comparison lemma identifies the existing finite level pairing
on `x` and `lam[n](y)` with `finiteWeilAlongHomBilinearMap` transported
through the actual torsion-kernel equivalences and roots-of-unity
equivalence. Its proof uses surjectivity of the kernel equivalences and
`kernelLevelEquiv_map`. Thus the pullback uses exactly the already
constructed finite scheme pairing, with value beta(lam[n](y))(x).

`integralWeilAlongHomBilinearMap` composes the second input of the actual
integral Weil bilinear map with `fullLinearMap` of `groupHom lam`.
This gives bilinearity over the existing full profinite-integer ring on
every selected divisibility system. The application lemma is exactly
`e(x, T(lam)(y))`. The coordinate lemma identifies each value with the
finite along-homomorphism pairing just described.

`awayWeilAlongHomBilinearMap` makes the same construction with the away
scalar ring and `awayLinearMap`. Its value is the selected integral
pairing on the orders coprime to the modulus. Restriction from full
orders to those orders commutes with the pairing, since all maps are
defined coordinatewise. The modulus can be any natural number.

`primeWeilAlongHomBilinearMap` composes the actual prime-adic pairing
with `PrimeAdic.map` of `groupHom lam`. It is bilinear over the p-adic
integers, with `Fact p.Prime`. Its coordinates are the same finite
along-homomorphism pairing at orders p^n. Prime extraction from any
selected system retaining every p^n commutes with this pullback
pairing; full and away specializations follow by selecting those
predicates.

Both joint continuity lemmas compose the two continuous coordinate
projections with the finite pairing after the actual torsion map. Each
pair of input levels is discrete. Continuity into the product of root
levels and then its coherent subgroup gives the claimed continuity.
They use the existing inverse-limit topologies, with no finiteness assertion.

The provenance is the internal pullback of the intrinsic Weil pairing
along the existing functorial Tate maps, together with the kernel-point
comparison above. A polarization can be substituted for `lam`. No
polarization predicate is needed for these constructions alone. This
unit asserts no alternation, perfectness, nondegeneracy, rational pairing,
or monodromy equivariance, and makes no choice of roots or twist basis.
