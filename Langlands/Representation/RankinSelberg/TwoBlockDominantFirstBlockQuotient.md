# First-block disintegration of the rectangular section average

The definition `rectangularSectionAverage` integrates the actual external JPSS
rectangle on the block unipotent quotient. It accepts arbitrary equivariant
Whittaker functions and arbitrary complex-valued weights on the standard
unipotent quotient; this definition alone asserts no regularity or convergence.

The regularity theorem assumes that the test belongs to `coefficientModel π
lambda` for a representation `π` of full Whittaker type and that the quotient
weight is continuous. Finite Schwartz coefficient expansion then proves joint
continuity of the integrand, integrability at every rectangle fiber, and
continuity of the rectangle average. The supplied functionals may be zero; the
expansion permits an empty family in that case.

The disintegration theorem retains these hypotheses and additionally assumes
absolute integrability of the ordinary raw Jacquet integrand for the supplied
additive Haar measure `μR`. The scalar additive Haar measure `ν` supplies the
external rectangle measure. The supplied quotient measures `νN`, `νH`, `νA`, and
`νM` must be compatible with, respectively, the standard unipotent, block
unipotent, first-block standard unipotent, and mixed subgroups and exactly the
normalized Haar measures named in the Lean theorem: `generalLinearHaar` with
`unipotentHaar`, `blockHaar`, `unipotentHaar` at the first-block rank, and
`mixedHaar`. Both `νH` and `νA` are assumed sigma-finite.

Under these conditions, raw Jacquet convergence gives genuine product
integrability. The published normalized first-block tower disintegrates the
rectangle average on block determinant slice `a` over mixed determinant slice
`0`, with inner first-block determinant slice `a` and coefficient exactly one.
The first-block average is measurable and integrable on that mixed slice.

This is derived integration infrastructure from JPSS (1983), Section 4.6
equation (6), printed page 412, for Sections 4.9 and 4.10(2), printed pages
416–419. It does not prove the lower convergence or final Laurent identity.
Source: `jpss-1983-rankin-selberg`, PDF SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
