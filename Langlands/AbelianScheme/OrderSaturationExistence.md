# Integral order models under a finite-fibre affine-open criterion

This internal adapter combines the exact scaled-action construction, actual
finite étale torsion-image sums, geometric quotient existence, and the two
factorizations of `OrderSaturation`. It retains an explicit geometric
criterion on the original abelian scheme.

`IntegralOrderModel α` packages an actual abelian scheme `B` over the same
base, an actual unital integral action `O →+* End B`, and actual homomorphisms
in both directions whose composites are the same positive integer multiple
of the identities. The forward map is a finite, flat, surjective isogeny
and is étale. Its rationalization intertwines the integral action with the
original rational action `α` on `A`.

`integralOrderModelOfForallFinsetFibre` constructs such a model when:

- `S` is locally noetherian and has a structural map to the spectrum of a
  characteristic-zero field;
- `O` is a possibly noncommutative ring with a supplied finite integer basis;
- `α : O →+* Rationalization.End A` is the original rational ring action;
- every finite set of points of `A` over a single point of `S` is contained
  in one affine open of `A`;
- the published proposition `TorsionFiniteEtaleStatement` is supplied.

The construction first chooses an exact scaled lift and normalizes its sign.
Its positive natural index casts to the exact signed denominator. That index
is invertible in the characteristic-zero field and hence in global sections
of `S`. The supplied torsion statement gives the finite and étale instances
for the actual torsion scheme. The published quotient-existence helper uses
the finite-fibre affine-open criterion to construct the quotient of the
actual sum of the scaled basis maps' torsion images. Invertible
multiplication supplies the required isogeny for the first factorization.
`OrderSaturation.action`, `inverseData` and `action_rational_fac` then give
all the packaged outputs.

The proof is an internal deduction from the imported Library constructions.
It requires no global projective embedding, imposes no torsion-freeness on
integral Hom, and remains valid for disconnected, nonreduced and empty bases.
It does not establish the affine-open criterion for arbitrary polarized
families, extend the order action to a rational algebra, transport a
polarization, determinant, dimension or level structure, or prove any moduli
representability statement.
