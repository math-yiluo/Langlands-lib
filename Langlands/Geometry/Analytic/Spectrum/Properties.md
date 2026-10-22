# Properties of the multiplicative spectrum

Author: Worker 36. Private proof development, not accepted proof evidence.

The evaluation map is injective by extensionality and is a topological embedding
by the definition of the spectrum topology. Hausdorffness follows from the
Hausdorff product of real lines. Its image is precisely the functions satisfying
the displayed closed equations and inequalities: preservation of zero, one and
multiplication; subadditivity and invariance under negation; nonnegativity and the
norm bound. The image is closed and lies in the product of the compact intervals
`[0, ‖a‖]`. Tychonoff compactness and the embedding give compactness of the
spectrum. This argument does not assert nonemptiness, which needs a separate
existence theorem for general Banach rings.

The kernel ideal is prime because the seminorm is multiplicative, the real
numbers have no zero divisors, and the value at one is one. Laurent inequality
loci are closed by continuous evaluation and hence compact. These statements
apply to arbitrary index families; finite families with positive radii are the
ones used later in affinoid geometry. Their affinoid representability is not
asserted in this module.

Every bounded multiplicative seminorm on a normed field equals the given field
norm: applying the upper bound to an element and its inverse supplies both
inequalities. Applying this fact after pullback along the bounded scalar map
proves scalar normalization on every normed algebra. Pullback respects identity,
composition and Laurent inequality loci by its defining formula.

The original source is Berkovich's *Non-archimedean analytic spaces*
(Trieste lectures, 2009), section 1.2, specifically Exercise 1.2.4 and the
following prime-kernel paragraph, Definition 1.2.5 and Fact 1.2.6,
printed/PDF p.4, and Exercise 2.2.2(i), p.9.
The retained source is registered as
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`;
the [author's PDF](https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf)
was also inspected. The proofs described above are the implemented direct
arguments using Mathlib. The source's additional nonemptiness assertion
and analytic representability conclusions are not imported as assumptions.
No independent proof acceptance or Library publication is claimed.
