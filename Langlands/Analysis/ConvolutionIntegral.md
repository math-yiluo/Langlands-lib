# The convolution integral of two complex functions on a group

`Langlands.Analysis.ConvolutionIntegral` defines

`Langlands.Hecke.convolutionIntegral μ f g x = ∫ y, f y * g (y⁻¹ * x) ∂μ`

for any measure `μ` on a group `G` with a measurable structure and any functions `f g : G → ℂ`.
For a left Haar measure this is the usual left convolution `f ⋆ g`. For arbitrary functions the
expression uses Mathlib's Bochner integral, including its convention for nonintegrable functions;
no topology on `G` is needed for the definition.

The module contains only this definition. It is imported by `Langlands.Representation.Hecke.Convolution`,
which builds the Hecke algebra of locally constant compactly supported functions on a totally
disconnected group with this product, and by the Dixmier–Malliavin theorem
(`Langlands.Analysis.DixmierMalliavin.LinearGroup` and its consumers), which writes a smooth compactly
supported function on a Lie group as a finite sum of such convolutions. Keeping the definition in its
own module lets the second use state its results without importing the Hecke algebra of test
functions. The name keeps its namespace `Langlands.Hecke`.

The page of `Langlands.Representation.Hecke.Convolution` gives the literature for this convention.
