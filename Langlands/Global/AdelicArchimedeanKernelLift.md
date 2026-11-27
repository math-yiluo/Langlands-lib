# Archimedean test kernels at a compact open finite level

At a compact open subgroup `L` of the finite adelic group, `finiteLevelWeight`
is its indicator divided by its finite positive Haar mass. `liftArchimedeanKernel`
multiplies the archimedean kernel by this weight on the two adelic factors.
It includes the scalar for which the product Haar measure, pushed forward by
the inverse of `AdelicGroupPoints.split`, equals that scalar times the specified
full adelic Haar measure.

`liftArchimedeanKernel_isTestFunction` proves that the lift of a smooth compact
kernel is an adelic test. Its support lies in the product of the compact
archimedean support with `L`, and its finite part is invariant under `L` on
both sides. `integral_liftArchimedeanKernel` uses Fubini and the unit mass of the
finite weight to identify its integrated action on an `L`-fixed vector with
the archimedean integral.

`liftArchimedeanKernel_derivative` compares the derivative kernels used for
right convolution. The left shift by the inverse of an archimedean variable
acts only on the archimedean factor of the lift. The manifold chain rule pulls
out the Haar factor and the finite weight, leaving `gardingKernelDerivative`.

The lift formalizes the product with the compact open idempotent of
Borel–Jacquet (1979), §3.2, p. 194 (PDF p. 189), and Getz–Hahn (2024),
Lemma 9.7.2, pp. 264–265 (PDF pp. 276–277). Haar comparison and the derivative
identity follow from the indicated product and the Lean definitions.
