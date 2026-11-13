# Exact maximal-unramified recovery from finite integral descent

This internal construction completes the model and recovery assembly once
the finite coefficient model and the upstairs extension property are
supplied. It works for any nonarchimedean local field F in arbitrary universe
`u`, a finite Galois intermediate field E of its separable closure contained
in the inertia fixed field, and the published arithmetic unramifiedness
property of E over F.

The inputs match `FiniteUnramifiedSolution`: an actual smooth integral model
N over the spectral integers of E of the E-base change of a specified
F-group G, a smooth original model P over the inertia integers, exact
compatible recovery of P from N over the canonical generic field-tower
comparison, the fixed-ring smooth homomorphism extension property over the
inertia integers, and stability of P's original integral-point image under
every F-automorphism of the inertia fixed field. The code installs the
specified same-element coefficient algebra structures and the needed scalar
towers, including transitivity from the norm integers through E's integers to
the inertia integers.

`normFiniteDescendedModelIso` proves recovery of P from the effective
norm-integer model at the maximal-unramified coefficient stage. It extends
the proved finite-stage model isomorphism, composes with the supplied
recovery of P, and reverses the actual coefficient-tower isomorphism. The
generic composite is the inverse canonical field-tower comparison followed
by the identity and the same canonical comparison, so it is exactly the
identity of the prescribed inertia-base group. Generic relabeling retains
the entire constructed integral isomorphism.

`givenFiniteDescendedModel` then transports the model to the given valuation
integers of F using `givenIntegerModel`. Its smoothness is
`givenFiniteDescendedModel_smooth`. The full equality of unramified
coefficient models proved in `IntegerPresentation` transports the preceding
maximal-unramified comparison to `givenFiniteDescendedModelIso`. Its source
is the actual published `baseChangeUnramified` of the resulting model, its
target is the original supplied P, and its generic map is `Iso.refl` of the
original prescribed inertia-base group.

This is an internal composition of actual affine descent, exact generic
recovery, transitivity of coefficient extension and same-subring presentation
transport. It supplies the full model/recovery conclusion conditional on the
explicit finite-model/recovery and smooth-extension inputs. It does not prove
those inputs or claim a proof of the unconditional
`UnramifiedSmoothModelDescentStatement` / KP Fact 2.10.16.
