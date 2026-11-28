# Transport of irreducible ℓ-adic Galois classes to the local Weil group

`Langlands.Henniart.ladicWeilTransport` proves
`Langlands.Henniart.LadicWeilTransportStatement` at its three independent
universes. For a nonarchimedean local field of either characteristic, a
prime ℓ different from the residue characteristic, and an embedding
`ι : PadicAlgCl ℓ →+* ℂ`, it certifies that the prescribed transport of an
irreducible ℓ-adic class is a continuous irreducible Weil class of the
same rank.

Take a representative `A` of the input class, with its continuity,
finite-coefficient, irreducibility and rank certificates. Write `E` for
`PadicAlgCl ℓ`. The proof constructs the complex representative by
restricting along `localProjection K Ω` and applying
`ladicScalarExtension ℓ ι` to the resulting Weil action.

## Continuity

`ladicFiniteInertia` gives finite image on absolute inertia. The projection
sends Weil inertia into absolute inertia, so the restricted ℓ-adic action
has finite image on Weil inertia. This action is continuous and its
endomorphism space is Hausdorff, as can be seen from the coordinates of a
finite basis. The kernel is therefore closed. The finite-range kernel
criterion makes it open in inertia, and openness of Weil inertia makes the
kernel of the restricted action open in the Weil group. The base-change
homomorphism sends the identity endomorphism to the identity, so the
complex action also has open kernel. The open-kernel continuity criterion
then gives continuity for the complex module topology.

## Irreducibility and rank

For a subspace stable under the restricted Weil action, take a vector in
the subspace and a linear form in its annihilator. Evaluating the linear
form on the Galois translates of the vector gives a continuous scalar
function because evaluation is linear on the endomorphism space with its
module topology. The function vanishes on the dense image of the Weil
group, so it vanishes on the Galois group. Linear forms in the annihilator
characterize membership in the subspace, which is therefore Galois stable
and is either zero or the whole space. The restricted action has the same
nonzero carrier, so it is irreducible.

The tensor unit equivalence identifies scalar extension from `E` to
itself with the original restricted action. Since `E` is algebraically
closed, `irreducible_extendCoefficients_of_isAlgClosed` applies. That
theorem uses Burnside's theorem and base change of endomorphisms, giving
irreducibility after extension to `ℂ` along `ι`. Restriction keeps the
carrier, and `rank_extendCoefficients` supplies the rank of the complex
action. The isomorphism class of this certified representative forgets to
`LocalNumerical.ladicWeilTransport` of the underlying ℓ-adic class by the definitions of
the quotient maps.

## Sources

- G. Henniart, *La conjecture de Langlands locale numérique pour GL(n)*
  (1988), `henniart-1988-numerical`, §§4.1–4.2, pp. 509–510. Section 4.2
  compares coefficient fields for finite-image representations. The proof
  here implements restriction and scalar extension under the hypotheses of
  the transport statement. Retained PDF SHA-256
  `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`.
  [Transport statement](HenniartLadicStatement.md)
- G. Henniart, *Représentations du groupe de Weil d'un corps local*
  (1980), `henniart-1980-weil-representations`, §2.1, p. 158, gives the
  open inertia topology and the dense map to the Galois group.
  Retained PDF SHA-256
  `451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`.
