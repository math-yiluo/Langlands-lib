# Joint continuity from spectral displacement control

## Statement

`SpectralParametricPullbackContinuityStatement` concerns arbitrary normed
commutative rings `A : Type u` and `B : Type v`, an arbitrary topological
space `T : Type w`, and a specified family of actual bounded unital ring
homomorphisms `f : T → BoundedRingHom A B`.

Its hypothesis says that, for every fixed element `a` of `A`, every parameter
`t₀`, and every positive real tolerance `ε`, eventually as `t` approaches
`t₀` one has

`x(f(t)(a) - f(t₀)(a)) ≤ ε`

simultaneously for every bounded multiplicative spectrum point `x` of `B`.
The order of quantifiers requires a single parameter neighborhood for all
such `x`, for the given `a`, `t₀` and `ε`. It does not require a single
neighborhood for all algebra elements.

The conclusion is joint continuity of the concrete map

`(t, x) ↦ comap(f(t))(x)`

from `T × BanachSpectrum B` to `BanachSpectrum A`, both spectra having the
existing topology of pointwise convergence. Each pullback uses the supplied
bounded map; its boundedness constant can depend on `t`. No norm continuity
of the element orbits, common operator bound, compactness, completeness,
field, ultrametricity, nonempty spectrum or separation of elements by
spectrum points is assumed.

## Provenance and intended role

This is an internal general spectral-analysis prerequisite. It abstracts
the evaluation step from Worker 730's published
`StrictTestDomain/SpectralLocalContinuityProof`, separating it from the
strict quotient, group-action and represented-domain machinery. That proof's
private `joint_spectral_evaluation` uses the inequality
`|x(b) - x(c)| ≤ x(b - c)` and continuity of evaluation at a fixed element;
`joint_spectral_action` uses the spectrum's induced topology. The same
argument applies to this general bounded-map family with arbitrary source
and target rings. The present statement is proposed for independent proof;
this file supplies no proof of it.

The Library's `Spectrum/JointContinuityStatement` instead assumes norm
continuity of each orbit. The present target allows the weaker uniform
spectral control needed for local section actions, retaining nilpotents and
empty spectra. It is not an equivalence of those two hypotheses or of any
automorphism topologies. It constructs no analytic domains, spaces, sites
or cohomology.
