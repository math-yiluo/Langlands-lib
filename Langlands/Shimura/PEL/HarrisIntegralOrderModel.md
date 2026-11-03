# Integral models of the actual Harris order with determinant comparison

This module specializes the geometric integral-order model construction to
the already constructed positive-Harris integer order and its finite integer
basis. All arithmetic objects and schemes are in universe zero, as in the
consumer. Let `D` and `C` be the existing central simple unitary datum and
signature charts. The base `S` is locally noetherian and has its actual
structural map to the spectrum of the Kottwitz cocharacter reflex field.
Let `B` be the original abelian scheme and `i` its original rational algebra
action.

`harrisIntegralOrderModel` constructs an actual integral order model from
the supplied `TorsionFiniteEtaleStatement` and the explicit criterion that
every finite subset of a fibre of `B` is contained in one affine open.
It uses the published Harris order and basis without changing either.
The generic construction supplies the actual quotient abelian scheme, the
unital integral order action, the finite étale isogeny from `B`, and the
positive integral inverse-multiple data.

`harrisIntegralOrderModelIso` is an isomorphism in the existing category of
actual abelian schemes with rational algebra action. Its source is the
original action `i` and its target is the unique full rational extension of
the constructed integral action. It reuses the generic comparison on all
rational algebra elements, including its actual forward map and inverse.

`harrisIntegralOrderModel_determinant_iff` proves that, for the supplied
CM-section proof, the original full Harris rational Lie determinant
condition is equivalent to the existing integral Harris Lie determinant
condition on this model. It first applies the published invariance under
an equivariant rational-action isomorphism. It then applies the published
rational-to-integral determinant comparison, using the exact restriction
formula for the full Harris extension. The result retains every finite
family of order elements, every finite Lie chart, every smaller open, and
equality of the actual structure-sheaf polynomial coefficients. No
geometric-point or reduced-base replacement is made.

The provenance is an internal specialization of the imported constructions
and determinant comparisons. The affine-open criterion is still an input;
this module does not derive it from a polarization. It does not transport
a polarization, relative dimension or level data and does not establish
surjectivity onto normalized CM classes or representability.
