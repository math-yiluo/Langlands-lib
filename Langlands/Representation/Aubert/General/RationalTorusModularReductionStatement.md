# Reduction of the torus modular character to actual structural inputs

`RationalTorusModularReductionStatement` is an internal reduction target for
`RationalParabolicModulusStatement`. It consumes the general Iwahori Haar-product
statement, actual opposite-radical Haar reciprocity and the generic-centralizer
statement, all in the same arbitrary universe.

For a connected reductive group over a nonarchimedean local field, fix its actual
maximal split torus, a generic cocharacter and the published standard-cocharacter
statement. Use the canonical point topology, with the local compactness,
nonarchimedean group and Hausdorff instances of the original modulus target.
If a supplied subgroup `K0` has `SimultaneousStandardBasisAt i ν K0`, then
Mathlib's ambient modular character is `1` on every point in `torusPoints i`.
The conclusion concerns the actual torus image in `G(k)`.

The internal derivation uses the empty root face. Its standard Levi is the
whole-torus centralizer, so conjugation by a torus point is the identity on that
factor. The original cocharacter is standard for the empty face, and its
negative is standard for the empty face of the reversed chamber. Consequently
the opposite factor of the simultaneous basis is precisely the dynamic radical
of the inverse cocharacter. This comparison requires no root-negation closure
or additional root-system premise. The opposite radical meets the original
parabolic only at `1`, by the affine dynamic intersection theorem. The
Haar-product statement therefore computes the modulus of inner conjugation as
the product of the two radical moduli and the identity Levi modulus. Opposite
reciprocity makes that product `1`; the published inner-conjugation identity
identifies it with Mathlib's modular character.

This conditional reduction supplies neither the general Haar-product theorem,
opposite reciprocity, generic centralizer theorem nor existence of an actual
simultaneous basis. It asserts no Cartan covering and no unimodularity away
from the torus. Those inputs and the remaining ambient and standard-Levi
unimodularity arguments remain obligations of the parent proof.
