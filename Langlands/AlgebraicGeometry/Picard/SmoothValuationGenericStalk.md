# Actual generic-fibre restrictions at smooth valuation stalks

This internal construction connects smooth-stalk Picard vanishing to an
actual line bundle on the actual generic fibre of the supplied scheme.
The coefficient algebra of each scheme stalk is recovered by the fully
faithful spectrum functor from the composite of its canonical stalk
morphism with the supplied structure morphism. Its spectrum map is
therefore exactly that composite.

For any supplied coefficient algebra `K`, `genericStalkRing` is the tensor
product of that actual stalk with `K` over the original base ring.
`genericStalkToFibre` maps its spectrum to the actual pullback defining the
generic fibre. The two maps in the pullback cone come from the two tensor
inclusions and the canonical stalk morphism. The projection lemmas record
these maps explicitly.

For an arbitrary valuation domain and any chosen fraction field, Mathlib's
localization-under-base-change instance identifies the tensor product as
the localization of the actual stalk at the images of the nonzero
divisors of the base. The imported smooth-stalk localization theorem gives
vanishing of its module Picard group. Applying the imported affine
line-bundle trivialization to the pullback of the supplied line bundle
then constructs an actual isomorphism with the structure sheaf.

These constructions and conclusions are derived from the imported Library
results and Mathlib's spectrum, tensor, pullback, and localization
interfaces. They impose no rank, dimension, Noetherian, or discreteness
assumption on the valuation domain. They give local data over
base-changed total-space stalks; extension and gluing to a line bundle on
the total scheme remain separate obligations.
