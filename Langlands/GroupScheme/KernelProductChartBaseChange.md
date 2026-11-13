# Base change of compatible product charts

This internal supporting construction uses the canonical categorical product
comparison `PreservesProduct.iso`. It does not introduce a different product
or product comparison.

`baseChangeChart` pulls back a scheme chart and precomposes with the inverse
comparison from the product of the pulled-back factors to the pullback of
the original product. `baseChangeLift` postcomposes a supplied lift with the
forward comparison. `baseChangeLift_chart` proves that their composite is
the original lift followed by the pulled-back chart.

`baseChangeChart_compatibility` transports a supplied commuting square of
product charts and group homomorphisms. Naturality of the canonical comparison
is proved by the product projections. `baseChangeChart_unit` transports the
target chart's preservation of the distinguished unit. The comparison is a
group-scheme isomorphism and pullback preserves the distinguished identity
points. No claim that either chart is a group homomorphism is used.

`mono_baseChangeChart` uses preservation of monomorphisms by pullback and
precomposition with the inverse product comparison. For
`isOpenImmersion_baseChangeChart`, the pulled-back chart is the actual map
between scheme pullbacks, with the identity maps on the base and the new
base. The published open-immersion base-change instance applies, and the
comparison isomorphism preserves this property.

`iso_baseChange` works over arbitrary schemes. In addition to compatible
monomorphic integral charts and target-unit preservation, its input includes
a morphism from the actual full kernel of the base-changed homomorphism
to the pullback of the original source product. Its composite with the
pulled-back source chart must be the kernel inclusion. The converted lift
and preceding chart lemmas discharge precisely the hypotheses of
`KernelProductChart.iso`. The result is an isomorphism over the new base
from the product of the actual base-changed factor kernels to the full
base-changed ambient kernel. It includes the empty finite product.

`smooth_connected_baseChange` specializes the new base to the spectrum of
an arbitrary field. Every actual base-changed factor kernel must additionally
be supplied as smooth, affine and connected. The included
`KernelProductChartGeometry` module proves the finite-product result and
transfers smoothness and connectedness through the scheme isomorphism. Its
paired Markdown describes that argument. No unipotence transfer through a
scheme-only isomorphism is asserted.

All integral charts, their compatibility, full-scheme containment and factor
geometry remain explicit inputs. This module does not prove their existence,
the root-depth kernel theorem or KP Proposition 8.4.15.
