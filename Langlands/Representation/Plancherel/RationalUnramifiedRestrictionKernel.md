# The actual character quotient by ambient unramified restriction

This internal algebraic prerequisite identifies the quotient of actual
unramified parameters by ambient restrictions using the existing actual
valuation-image map. Its provenance is the published restriction and
valuation constructions and divisibility of the complex units, already
implemented by the Library's complex-character extension theorems.

Let `f : H → G` be a morphism of group schemes over a nonarchimedean
local field. For affine `H`, equip `H(F)` with its canonical rational-point
topology. The homomorphism `rationalUnramifiedValuationKernelRestrict`
restricts the descended character of the discrete valuation image of
`H` to the kernel of the induced image map.

When `H` is locally of finite type, this homomorphism is surjective.
Divisibility of the complex units extends each character of the kernel
to the discrete source valuation image. The canonical projection to
that image is continuous under these hypotheses, giving an actual
continuous unramified character of `H(F)`.

When `H` and `G` are affine and `G` is locally of finite type, use the
canonical rational-point topology on each point group. The kernel of
the restriction homomorphism is then the image of ambient unramified restriction.
For the forward implication, the given source character kills the
valuation-map kernel. The existing descent and extension theorem for an
open homomorphism applies to the discrete valuation groups. Reconstruct
the ambient unramified character and compare values on actual rational
points using compatibility of the valuation projection with `f`.
Conversely, an ambient restriction kills the kernel by that same
compatibility. Applying the kernel statement to a character quotient
identifies all fibers as the multiplicative orbits of ambient restrictions.
Under the combined hypotheses, the quotient of the unramified character
group by the ambient restriction image is isomorphic as an abstract group
to the complex character group of the valuation-map kernel.

The algebraic coordinate construction additionally treats a supplied
one-direction rational character decomposition: assume each rational
character of `H`, after a positive integer multiple, is an integral
multiple of one chosen character plus a restriction from `G`. Evaluation
on the chosen character then injects the actual valuation kernel into
the additive integers, in multiplicative notation. To prove injectivity,
subtract the two valuation functionals; it vanishes on ambient
restrictions and on the chosen character, and hence on every character
by integer torsion-freeness. The valuation kernel is consequently cyclic.
