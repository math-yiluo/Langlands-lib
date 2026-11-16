# Actual rank-one centralizers over a ring

This is an internally derived prerequisite for the local split Isomorphism
Theorem. It reuses the actual relative cocharacter centralizer from
`Torus/RelativeCocharacterCentralizers`; it introduces no alternative group
model and asserts no new correspondence with an external source.

Let `R` be any commutative ring, `I` a finite index type, `G` an affine group
scheme over `Spec R`, `i` a homomorphism from the coordinate split torus, and
`mu : I → ℤ`. Write `C` for the actual centralizer of the cocharacter with
exponent `mu`. The existing API supplies its closed inclusion `C → G` and
the factored torus map `t : T → C`, with composite `i`.

`LocalSplitCell.IsRootParametrization.of_comp` reflects a root parametrization
through any closed subgroup: if `v : Ga R → C` composes to an actual root
parametrization `w : Ga R → G`, and `t` composes to `i`, then `v` parametrizes
the intrinsic root subgroup of `C` for the same exponent. Monomorphism of the
inclusion reflects the torus equivariance. Equivariance puts every point of
`v` in the intrinsic root subgroup. Conversely, functoriality maps each point
of that root subgroup into the ambient root subgroup, whose representation
by `w` supplies a preimage; monomorphism identifies this preimage with the
original point. Closedness follows by cancellation of the closed inclusion.

In `splitTorus.RelativeCocharacterCentralizer`, `isReductive` proves that
`C` is reductive whenever `G` is reductive. The existing smoothness theorem
provides smoothness over `R`. Base change of the represented centralizer
identifies each geometric fibre with a cocharacter centralizer in a connected
reductive group, so dynamic centralizer reductivity gives reductivity of that
fibre. `isFibrewiseMaximalTorus` proves that a fibrewise maximal torus of `G`
remains fibrewise maximal in `C`, by reflecting maximality through the closed
inclusion on each residue-field fibre.

For an actual root parametrization `w` of exponent `a` satisfying
`∑ j, a j * mu j = 0`, `rootLift` factors `w` through `C` using the represented
centralizer and the published annihilating-root inclusion.
`rootLift_comp` is the exact composite equality, and
`isRootParametrization_rootLift` applies the preceding reflection lemma.
These results do not require a local ring.

For every supplied field algebra `k` over `R`,
`mem_roots_baseChangeHom_iff` says that an exponent `m` is a root of the
actual fibre of `C` exactly when it is a root of the ambient fibre and
`∑ j, m j * mu j = 0`. This comparison assumes reductivity of `G` to supply
smoothness and finite type. The proof identifies the actual factored torus
with the canonical factor through the represented centralizer, applies
`Dynamic.mem_roots_torusFactor_iff`, and computes the exponent pairing.

Finally, given a fibrewise root datum `P`, a root `a`, and a vector `mu` that
annihilates `P.root a` and annihilates no roots except `P.root a` and its
negative, `mem_roots_baseChangeHom_iff_eq_or_neg` identifies the roots of
every supplied field fibre of `C` with exactly those two exponents. The
negative root is obtained by the reflection of `a` in itself.

No reducedness condition on `R`, locality, noetherian, Henselian or
characteristic hypothesis is used. This contribution does not prove an open
three-factor cell or construct normalized Weyl points; the unconditional
local Isomorphism Theorem remains open.
